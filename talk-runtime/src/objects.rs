//! Region-allocated objects: the runtime substrate for `'heap` structs.
//!
//! Every object belongs to a region; linking objects merges their regions
//! (union-find — regions only grow, counts only sum, so freeing reduces to
//! the Gay & Aiken invariant: a region dies exactly when its external
//! reference count reaches zero — *Language Support for Regions*, PLDI
//! 2001). The count tracks live stack bindings referencing into the region
//! (Perceus-style dup/drop at binding granularity, lifted to regions —
//! Reinking et al., PLDI 2021); intra-region references — including cycles —
//! never touch it. At zero the region's objects are finalized in reverse
//! allocation order, then bulk-freed (Reggio's finalise-then-free —
//! Arvidsson et al., OOPSLA 2023).

/// One `'heap` struct instance. Fields hold ordinary VM values (which may
/// include handles to other objects — same or other regions; a cross-region
/// store merges the regions).
#[derive(Clone, Debug, PartialEq)]
pub struct ObjectRecord<V> {
    pub fields: Vec<V>,
    /// The region this object was allocated into (the union-find
    /// resolves it to the current merged region).
    pub region: u32,
    /// The lowering-synthesized finalizer thunk, as a runtime function
    /// value (a closure in the VM, a label in the evaluator), if any.
    pub finalizer: Option<V>,
    /// Set when the finalizer walk has visited this object.
    pub finalized: bool,
    pub live: bool,
}

#[derive(Clone, Debug, Default)]
struct Region {
    /// Union-find parent (self-index for roots).
    parent: u32,
    /// Live stack bindings referencing into this region (root-only).
    owner_count: u32,
    /// Object indices allocated into this region (root-only after merge).
    members: Vec<u32>,
    /// Mid-teardown: finalizers running, frees pending.
    finalizing: bool,
    /// Torn down: members are dead.
    dead: bool,
}

#[derive(Debug, PartialEq)]
pub enum ObjectError {
    /// Storing an object handle while its (or the target's) region is
    /// being torn down would resurrect it.
    StoreDuringTeardown,
    /// Ledger underflow: a release without a matching acquire.
    ReleaseUnderflow,
    DeadObject,
    UnknownObject,
}

impl ObjectError {
    pub fn message(&self) -> &'static str {
        match self {
            ObjectError::StoreDuringTeardown => "cannot store an object during region teardown",
            ObjectError::ReleaseUnderflow => "region released more times than acquired",
            ObjectError::DeadObject => "use of an object in a dead region",
            ObjectError::UnknownObject => "unknown object handle",
        }
    }
}

/// The pending finalizer walks, outermost first: a deinit body may release
/// the last handle of *another* region, nesting a second walk.
#[derive(Clone, Debug, Default)]
pub struct FinalizeState {
    pub region: u32,
}

#[derive(Debug)]
pub struct Objects<V> {
    pub records: Vec<ObjectRecord<V>>,
    regions: Vec<Region>,
    /// Stack of regions currently tearing down.
    pub finalize_stack: Vec<FinalizeState>,
}

impl<V> Default for Objects<V> {
    fn default() -> Self {
        Objects {
            records: vec![],
            regions: vec![],
            finalize_stack: vec![],
        }
    }
}

impl<V: Clone> Objects<V> {
    /// Allocate a new object in a fresh region with owner count 1 (the +1
    /// belongs to whatever binding receives the rvalue).
    pub fn allocate(&mut self, fields: Vec<V>) -> u32 {
        let region = self.regions.len() as u32;
        let index = self.records.len() as u32;
        self.regions.push(Region {
            parent: region,
            owner_count: 1,
            members: vec![index],
            finalizing: false,
            dead: false,
        });
        self.records.push(ObjectRecord {
            fields,
            region,
            finalizer: None,
            finalized: false,
            live: true,
        });
        index
    }

    pub fn set_finalizer(&mut self, object: u32, thunk: V) -> Result<(), ObjectError> {
        let record = self
            .records
            .get_mut(object as usize)
            .ok_or(ObjectError::UnknownObject)?;
        record.finalizer = Some(thunk);
        Ok(())
    }

    pub fn get_field(&self, object: u32, index: u16) -> Result<V, ObjectError> {
        let record = self
            .records
            .get(object as usize)
            .ok_or(ObjectError::UnknownObject)?;
        if !record.live {
            return Err(ObjectError::DeadObject);
        }
        record
            .fields
            .get(index as usize)
            .cloned()
            .ok_or(ObjectError::UnknownObject)
    }

    /// In-place field store. `handles` must be the object handles reachable
    /// in the stored value (the caller scans); storing a handle merges the
    /// target's region with the handle's, and is a teardown trap if either
    /// side is finalizing.
    pub fn set_field(
        &mut self,
        object: u32,
        index: u16,
        value: V,
        handles: &[u32],
    ) -> Result<(), ObjectError> {
        let target_region = {
            let record = self
                .records
                .get(object as usize)
                .ok_or(ObjectError::UnknownObject)?;
            if !record.live {
                return Err(ObjectError::DeadObject);
            }
            record.region
        };
        let target_root = self.find(target_region);
        if !handles.is_empty() && self.regions[target_root as usize].finalizing {
            return Err(ObjectError::StoreDuringTeardown);
        }
        for &handle in handles {
            let handle_region = self
                .records
                .get(handle as usize)
                .ok_or(ObjectError::UnknownObject)?
                .region;
            let handle_root = self.find(handle_region);
            if self.regions[handle_root as usize].finalizing
                || self.regions[handle_root as usize].dead
            {
                return Err(ObjectError::StoreDuringTeardown);
            }
            self.union(target_root, handle_root);
        }
        let record = &mut self.records[object as usize];
        let slot = record
            .fields
            .get_mut(index as usize)
            .ok_or(ObjectError::UnknownObject)?;
        *slot = value;
        Ok(())
    }

    /// A live binding took a reference into each handle's region.
    /// Acquiring a finalizing region is a no-op: deinit bodies may bind
    /// locals that alias the dying region; teardown proceeds regardless.
    pub fn acquire(&mut self, handles: &[u32]) -> Result<(), ObjectError> {
        for &handle in handles {
            let region = self
                .records
                .get(handle as usize)
                .ok_or(ObjectError::UnknownObject)?
                .region;
            let root = self.find(region) as usize;
            if self.regions[root].finalizing || self.regions[root].dead {
                continue;
            }
            self.regions[root].owner_count += 1;
        }
        Ok(())
    }

    /// A binding referencing into each handle's region went out of scope.
    /// Regions that reach zero are queued for teardown (the interpreter
    /// pumps [`Objects::next_finalizer`] before each step).
    pub fn release(&mut self, handles: &[u32]) -> Result<(), ObjectError> {
        for &handle in handles {
            let region = self
                .records
                .get(handle as usize)
                .ok_or(ObjectError::UnknownObject)?
                .region;
            let root = self.find(region) as usize;
            if self.regions[root].finalizing || self.regions[root].dead {
                continue;
            }
            if self.regions[root].owner_count == 0 {
                return Err(ObjectError::ReleaseUnderflow);
            }
            self.regions[root].owner_count -= 1;
            if self.regions[root].owner_count == 0 {
                self.regions[root].finalizing = true;
                self.finalize_stack.push(FinalizeState {
                    region: root as u32,
                });
            }
        }
        Ok(())
    }

    /// The next finalizer to run for the innermost region mid-teardown:
    /// highest object index first (reverse allocation order). Marks the
    /// object finalized. When a region's walk is done its objects are
    /// bulk-freed and the walk pops. `None` means no teardown is pending.
    pub fn next_finalizer(&mut self) -> Option<(V, u32)> {
        loop {
            let state = self.finalize_stack.last()?;
            let root = state.region as usize;
            let next = self.regions[root]
                .members
                .iter()
                .copied()
                .filter(|&object| {
                    let record = &self.records[object as usize];
                    !record.finalized && record.finalizer.is_some()
                })
                .max();
            match next {
                Some(object) => {
                    let record = &mut self.records[object as usize];
                    record.finalized = true;
                    // The candidate filter above admits only records with a
                    // finalizer, so this always yields.
                    if let Some(thunk) = record.finalizer.clone() {
                        return Some((thunk, object));
                    }
                }
                None => {
                    // Walk complete: bulk-free the region.
                    let members = std::mem::take(&mut self.regions[root].members);
                    for object in members {
                        let record = &mut self.records[object as usize];
                        record.live = false;
                        record.fields.clear();
                    }
                    self.regions[root].finalizing = false;
                    self.regions[root].dead = true;
                    self.finalize_stack.pop();
                }
            }
        }
    }

    pub fn live_objects(&self) -> usize {
        self.records.iter().filter(|record| record.live).count()
    }

    fn find(&mut self, region: u32) -> u32 {
        let mut root = region;
        while self.regions[root as usize].parent != root {
            root = self.regions[root as usize].parent;
        }
        // Path compression.
        let mut current = region;
        while self.regions[current as usize].parent != root {
            let next = self.regions[current as usize].parent;
            self.regions[current as usize].parent = root;
            current = next;
        }
        root
    }

    /// Merge two region roots: counts sum, members merge small-to-large.
    fn union(&mut self, a: u32, b: u32) {
        let (a, b) = (self.find(a), self.find(b));
        if a == b {
            return;
        }
        let (small, large) =
            if self.regions[a as usize].members.len() < self.regions[b as usize].members.len() {
                (a, b)
            } else {
                (b, a)
            };
        self.regions[small as usize].parent = large;
        let members = std::mem::take(&mut self.regions[small as usize].members);
        let count = std::mem::take(&mut self.regions[small as usize].owner_count);
        self.regions[large as usize].members.extend(members);
        self.regions[large as usize].owner_count += count;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn objects() -> Objects<i64> {
        Objects::default()
    }

    #[test]
    fn allocate_link_release_frees_cycle() {
        let mut o = objects();
        let a = o.allocate(vec![0, 0]);
        let b = o.allocate(vec![0, 0]);
        // a.next = b merges the regions; b.prev = a makes a cycle.
        o.set_field(a, 0, 1, &[b]).unwrap();
        o.set_field(b, 1, 2, &[a]).unwrap();
        assert_eq!(o.live_objects(), 2);
        // Two rvalue owners (one per allocate). Release both.
        o.release(&[a]).unwrap();
        assert_eq!(o.live_objects(), 2, "one owner still live");
        o.release(&[b]).unwrap();
        assert!(o.next_finalizer().is_none(), "no finalizers registered");
        assert_eq!(o.live_objects(), 0, "cycle freed at last release");
    }

    #[test]
    fn acquire_extends_region_life() {
        let mut o = objects();
        let a = o.allocate(vec![0]);
        o.acquire(&[a]).unwrap(); // second binding
        o.release(&[a]).unwrap();
        assert_eq!(o.live_objects(), 1);
        o.release(&[a]).unwrap();
        assert!(o.next_finalizer().is_none());
        assert_eq!(o.live_objects(), 0);
    }

    #[test]
    fn merge_sums_owner_counts() {
        let mut o = objects();
        let a = o.allocate(vec![0]);
        let b = o.allocate(vec![0]);
        o.set_field(a, 0, 7, &[b]).unwrap(); // merged: count 2
        o.release(&[a]).unwrap();
        assert_eq!(o.live_objects(), 2);
        o.release(&[b]).unwrap(); // find() resolves b to the merged root
        assert!(o.next_finalizer().is_none());
        assert_eq!(o.live_objects(), 0);
    }

    #[test]
    fn finalizers_run_in_reverse_allocation_order_then_free() {
        let mut o = objects();
        let a = o.allocate(vec![0, 0]);
        let b = o.allocate(vec![0, 0]);
        let c = o.allocate(vec![0, 0]);
        o.set_finalizer(a, 100).unwrap();
        o.set_finalizer(b, 101).unwrap();
        o.set_finalizer(c, 102).unwrap();
        o.set_field(a, 0, 0, &[b]).unwrap();
        o.set_field(b, 0, 0, &[c]).unwrap();
        o.release(&[b]).unwrap();
        o.release(&[c]).unwrap();
        o.release(&[a]).unwrap();
        // Teardown pending: pump yields finalizers newest-first.
        assert_eq!(o.next_finalizer(), Some((102, c)));
        assert_eq!(o.next_finalizer(), Some((101, b)));
        assert_eq!(o.next_finalizer(), Some((100, a)));
        assert_eq!(o.live_objects(), 3, "memory live through the walk");
        assert_eq!(o.next_finalizer(), None);
        assert_eq!(o.live_objects(), 0, "bulk free after the walk");
    }

    #[test]
    fn fields_readable_during_teardown() {
        let mut o = objects();
        let a = o.allocate(vec![41]);
        o.set_finalizer(a, 9).unwrap();
        o.release(&[a]).unwrap();
        assert_eq!(o.next_finalizer(), Some((9, a)));
        // Mid-walk: memory is live, reads succeed.
        assert_eq!(o.get_field(a, 0), Ok(41));
        assert_eq!(o.next_finalizer(), None);
        assert_eq!(o.get_field(a, 0), Err(ObjectError::DeadObject));
    }

    #[test]
    fn storing_handle_during_teardown_traps() {
        let mut o = objects();
        let dying = o.allocate(vec![0]);
        let survivor = o.allocate(vec![0]);
        o.set_finalizer(dying, 1).unwrap();
        o.release(&[dying]).unwrap();
        assert_eq!(o.next_finalizer(), Some((1, dying)));
        // Resurrection attempt from inside the finalizer.
        assert_eq!(
            o.set_field(survivor, 0, 0, &[dying]),
            Err(ObjectError::StoreDuringTeardown)
        );
        // Plain (non-handle) stores stay legal mid-teardown.
        o.set_field(dying, 0, 5, &[]).unwrap();
    }

    #[test]
    fn release_underflow_traps() {
        let mut o = objects();
        let a = o.allocate(vec![0]);
        o.acquire(&[a]).unwrap();
        o.release(&[a]).unwrap();
        o.release(&[a]).unwrap();
        let _ = o.next_finalizer();
        // Dead region: further releases are inert, not underflow…
        assert_eq!(o.release(&[a]), Ok(()));
        // …but a live region under-released is caught before going negative.
        let b = o.allocate(vec![0]);
        o.release(&[b]).unwrap();
        let _ = o.next_finalizer();
        assert_eq!(o.release(&[b]), Ok(()), "dead again — inert");
        let c = o.allocate(vec![0]);
        o.release(&[c]).unwrap(); // count 0, finalizing
        assert_eq!(o.release(&[c]), Ok(()), "finalizing — inert");
    }

    #[test]
    fn nested_teardown_stacks() {
        let mut o = objects();
        let a = o.allocate(vec![0]);
        let b = o.allocate(vec![0]);
        o.set_finalizer(a, 1).unwrap();
        o.set_finalizer(b, 2).unwrap();
        o.release(&[a]).unwrap();
        // a's walk begins; a's finalizer releases b (deinit body drops the
        // last handle to another region) — b's walk nests atop.
        assert_eq!(o.next_finalizer(), Some((1, a)));
        o.release(&[b]).unwrap();
        assert_eq!(o.next_finalizer(), Some((2, b)), "inner walk first");
        assert_eq!(o.next_finalizer(), None);
        assert_eq!(o.live_objects(), 0);
    }

    #[test]
    fn acquire_during_teardown_is_inert() {
        let mut o = objects();
        let a = o.allocate(vec![0]);
        o.set_finalizer(a, 1).unwrap();
        o.release(&[a]).unwrap();
        assert_eq!(o.next_finalizer(), Some((1, a)));
        // A deinit-body local binding aliases the dying region: allowed,
        // and does not delay the teardown.
        o.acquire(&[a]).unwrap();
        o.release(&[a]).unwrap();
        assert_eq!(o.next_finalizer(), None);
        assert_eq!(o.live_objects(), 0);
    }
}
