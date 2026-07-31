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

use rustc_hash::FxHashMap;

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
}

#[derive(Clone, Debug, Default)]
struct Region {
    /// Union-find parent (self-index for roots).
    parent: u32,
    /// Live stack bindings referencing into this region (root-only).
    owner_count: u32,
    /// Object indices allocated into this region (root-only after merge).
    members: Vec<u32>,
    /// Region ids absorbed into this root by `union`, transitively. A
    /// merged id stays reachable as a union-find parent, so teardown has
    /// to reclaim the whole tree, not just its root.
    merged: Vec<u32>,
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
    /// Handles are never recycled, so the supply is finite. Running out
    /// ends the program rather than wrapping.
    HandlesExhausted,
}

impl ObjectError {
    pub fn message(&self) -> &'static str {
        match self {
            ObjectError::StoreDuringTeardown => "cannot store an object during region teardown",
            ObjectError::ReleaseUnderflow => "region released more times than acquired",
            ObjectError::DeadObject => "use of an object in a dead region",
            ObjectError::UnknownObject => "unknown object handle",
            ObjectError::HandlesExhausted => "ran out of heap object handles",
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
    /// Live objects by handle. A torn-down object is removed, so this is
    /// bounded by what the program currently holds rather than by every
    /// object it has ever allocated.
    pub records: FxHashMap<u32, ObjectRecord<V>>,
    /// Live regions by id, reclaimed with their members at teardown.
    regions: FxHashMap<u32, Region>,
    /// Handles and region ids are never reused, so a stale handle can
    /// never name a live object, and an id below the watermark is one
    /// that was issued and has since died.
    next_object: u32,
    next_region: u32,
    /// Stack of regions currently tearing down.
    pub finalize_stack: Vec<FinalizeState>,
}

impl<V> Default for Objects<V> {
    fn default() -> Self {
        Objects {
            records: FxHashMap::default(),
            regions: FxHashMap::default(),
            next_object: 0,
            next_region: 0,
            finalize_stack: vec![],
        }
    }
}

impl<V: Clone> Objects<V> {
    /// Allocate a new object in a fresh region with owner count 1 (the +1
    /// belongs to whatever binding receives the rvalue).
    pub fn allocate(&mut self, fields: Vec<V>) -> Result<u32, ObjectError> {
        let region = self.next_region;
        let index = self.next_object;
        // Checked, not wrapping: recycling an id would let a stale handle
        // name a live object, and the watermark that separates "torn
        // down" from "never issued" would stop meaning anything.
        self.next_region = self
            .next_region
            .checked_add(1)
            .ok_or(ObjectError::HandlesExhausted)?;
        self.next_object = self
            .next_object
            .checked_add(1)
            .ok_or(ObjectError::HandlesExhausted)?;
        self.regions.insert(
            region,
            Region {
                parent: region,
                owner_count: 1,
                members: vec![index],
                merged: vec![],
                finalizing: false,
                dead: false,
            },
        );
        self.records.insert(
            index,
            ObjectRecord {
                fields,
                region,
                finalizer: None,
                finalized: false,
            },
        );
        Ok(index)
    }

    /// A handle's record. Removing torn-down objects would otherwise blur
    /// "already finalized" into "never existed"; the watermark keeps them
    /// apart.
    fn record(&self, object: u32) -> Result<&ObjectRecord<V>, ObjectError> {
        match self.records.get(&object) {
            Some(record) => Ok(record),
            None if object < self.next_object => Err(ObjectError::DeadObject),
            None => Err(ObjectError::UnknownObject),
        }
    }

    /// The region a handle belongs to, or `None` when the object is dead.
    /// Dead is not an error for the ledger operations: a deinit body may
    /// bind locals aliasing the dying region, and teardown proceeds
    /// regardless.
    fn live_region(&self, object: u32) -> Result<Option<u32>, ObjectError> {
        match self.record(object) {
            Ok(record) => Ok(Some(record.region)),
            Err(ObjectError::DeadObject) => Ok(None),
            Err(error) => Err(error),
        }
    }

    pub fn set_finalizer(&mut self, object: u32, thunk: V) -> Result<(), ObjectError> {
        // Resolve first so a dead handle reports as dead, not unknown.
        self.record(object)?;
        if let Some(record) = self.records.get_mut(&object) {
            record.finalizer = Some(thunk);
        }
        Ok(())
    }

    pub fn get_field(&self, object: u32, index: u16) -> Result<V, ObjectError> {
        let record = self.record(object)?;
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
        let target_region = self.record(object)?.region;
        let target_root = self.find(target_region);
        if !handles.is_empty() && self.region_is(target_root, |region| region.finalizing) {
            return Err(ObjectError::StoreDuringTeardown);
        }
        for &handle in handles {
            let handle_region = self.record(handle)?.region;
            let handle_root = self.find(handle_region);
            if self.region_is(handle_root, |region| region.finalizing || region.dead) {
                return Err(ObjectError::StoreDuringTeardown);
            }
            self.union(target_root, handle_root);
        }
        let record = self
            .records
            .get_mut(&object)
            .ok_or(ObjectError::UnknownObject)?;
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
            let Some(region) = self.live_region(handle)? else {
                continue;
            };
            let root = self.find(region);
            if self.region_is(root, |region| region.finalizing || region.dead) {
                continue;
            }
            if let Some(region) = self.regions.get_mut(&root) {
                region.owner_count += 1;
            }
        }
        Ok(())
    }

    /// A binding referencing into each handle's region went out of scope.
    /// Regions that reach zero are queued for teardown (the interpreter
    /// pumps [`Objects::next_finalizer`] before each step).
    pub fn release(&mut self, handles: &[u32]) -> Result<(), ObjectError> {
        for &handle in handles {
            let Some(region) = self.live_region(handle)? else {
                continue;
            };
            let root = self.find(region);
            if self.region_is(root, |region| region.finalizing || region.dead) {
                continue;
            }
            let Some(entry) = self.regions.get_mut(&root) else {
                continue;
            };
            if entry.owner_count == 0 {
                return Err(ObjectError::ReleaseUnderflow);
            }
            entry.owner_count -= 1;
            if entry.owner_count == 0 {
                entry.finalizing = true;
                self.finalize_stack.push(FinalizeState { region: root });
            }
        }
        Ok(())
    }

    /// The next finalizer to run for the innermost region mid-teardown:
    /// highest object index first (reverse allocation order). Marks the
    /// object finalized. When a region's walk is done its objects are
    /// bulk-freed and the walk pops. `None` means no teardown is pending.
    /// Whether a region teardown walk is in progress. Inline: the
    /// interpreter checks this before every instruction.
    #[inline]
    pub fn finalizing(&self) -> bool {
        !self.finalize_stack.is_empty()
    }

    pub fn next_finalizer(&mut self) -> Option<(V, u32)> {
        loop {
            let root = self.finalize_stack.last()?.region;
            let next = self.regions.get(&root).and_then(|region| {
                region
                    .members
                    .iter()
                    .copied()
                    .filter(|object| {
                        self.records.get(object).is_some_and(|record| {
                            !record.finalized && record.finalizer.is_some()
                        })
                    })
                    .max()
            });
            match next {
                Some(object) => {
                    if let Some(record) = self.records.get_mut(&object) {
                        record.finalized = true;
                        // The candidate filter above admits only records
                        // with a finalizer, so this always yields.
                        if let Some(thunk) = record.finalizer.clone() {
                            return Some((thunk, object));
                        }
                    }
                }
                None => {
                    // Walk complete: bulk-free the region. Dropping each
                    // record returns its field storage; the region and
                    // every id merged into it go with it.
                    if let Some(region) = self.regions.remove(&root) {
                        for object in region.members {
                            self.records.remove(&object);
                        }
                        for merged in region.merged {
                            self.regions.remove(&merged);
                        }
                    }
                    self.finalize_stack.pop();
                }
            }
        }
    }

    pub fn live_objects(&self) -> usize {
        self.records.len()
    }

    /// Read a region field without borrowing the whole table mutably.
    /// A missing region is a torn-down one.
    fn region_is(&self, root: u32, test: impl Fn(&Region) -> bool) -> bool {
        self.regions.get(&root).is_some_and(test)
    }

    /// Live members of the region `object` belongs to, resolved read-only
    /// (no path compression). The test-suite leak fences count a
    /// result-held region's objects as the result's own footprint: while
    /// the result owns a handle, the whole region legitimately stays live.
    pub fn region_live_members(&self, object: u32) -> Vec<u32> {
        let Some(record) = self.records.get(&object) else {
            return vec![];
        };
        let mut root = record.region;
        while let Some(parent) = self.regions.get(&root).map(|region| region.parent) {
            if parent == root {
                break;
            }
            root = parent;
        }
        self.regions
            .get(&root)
            .map(|region| {
                region
                    .members
                    .iter()
                    .copied()
                    .filter(|member| self.records.contains_key(member))
                    .collect()
            })
            .unwrap_or_default()
    }

    fn find(&mut self, region: u32) -> u32 {
        let mut root = region;
        while let Some(parent) = self.regions.get(&root).map(|region| region.parent) {
            if parent == root {
                break;
            }
            root = parent;
        }
        // Path compression.
        let mut current = region;
        while let Some(next) = self
            .regions
            .get_mut(&current)
            .map(|region| std::mem::replace(&mut region.parent, root))
        {
            if next == root || next == current {
                break;
            }
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
        let (Some(a_len), Some(b_len)) = (
            self.regions.get(&a).map(|region| region.members.len()),
            self.regions.get(&b).map(|region| region.members.len()),
        ) else {
            return;
        };
        let (small, large) = if a_len < b_len { (a, b) } else { (b, a) };
        let (members, count, merged) = match self.regions.get_mut(&small) {
            Some(region) => {
                region.parent = large;
                (
                    std::mem::take(&mut region.members),
                    std::mem::take(&mut region.owner_count),
                    std::mem::take(&mut region.merged),
                )
            }
            None => return,
        };
        if let Some(region) = self.regions.get_mut(&large) {
            region.members.extend(members);
            region.owner_count += count;
            // The absorbed root and everything already merged into it stay
            // reachable as parents, so the new root inherits them.
            region.merged.push(small);
            region.merged.extend(merged);
        }
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
        let a = o.allocate(vec![0, 0]).unwrap();
        let b = o.allocate(vec![0, 0]).unwrap();
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

    /// Torn-down objects and their regions must be reclaimed, not just
    /// flagged: at roughly 175 bytes apiece they were the largest term in
    /// a long run's memory.
    #[test]
    fn dead_objects_and_regions_do_not_accumulate() {
        let mut o = objects();
        for _ in 0..1000 {
            let a = o.allocate(vec![0, 0]).unwrap();
            let b = o.allocate(vec![0, 0]).unwrap();
            // Merge, so teardown has a union-find tree to reclaim rather
            // than two singleton regions.
            o.set_field(a, 0, 1, &[b]).unwrap();
            o.release(&[a]).unwrap();
            o.release(&[b]).unwrap();
            assert!(o.next_finalizer().is_none());
        }
        assert_eq!(o.live_objects(), 0);
        assert_eq!(o.records.len(), 0, "dead object records accumulated");
        assert_eq!(
            o.regions.len(),
            0,
            "region slots accumulated: a merged tree must be reclaimed whole"
        );
    }

    /// A deinit body may bind and drop locals that alias the dying
    /// region, so the ledger operations have to tolerate a handle whose
    /// object is already gone. A handle that was never issued is still an
    /// error.
    #[test]
    fn ledger_operations_tolerate_a_dead_handle_but_not_an_unknown_one() {
        let mut o = objects();
        let a = o.allocate(vec![0]).unwrap();
        o.release(&[a]).unwrap();
        assert!(o.next_finalizer().is_none());
        assert_eq!(o.live_objects(), 0);

        o.acquire(&[a]).expect("acquiring a dead handle is a no-op");
        o.release(&[a]).expect("releasing a dead handle is a no-op");
        assert_eq!(o.get_field(a, 0), Err(ObjectError::DeadObject));

        let unknown = 9999;
        assert_eq!(o.acquire(&[unknown]), Err(ObjectError::UnknownObject));
        assert_eq!(o.get_field(unknown, 0), Err(ObjectError::UnknownObject));
    }

    #[test]
    fn acquire_extends_region_life() {
        let mut o = objects();
        let a = o.allocate(vec![0]).unwrap();
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
        let a = o.allocate(vec![0]).unwrap();
        let b = o.allocate(vec![0]).unwrap();
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
        let a = o.allocate(vec![0, 0]).unwrap();
        let b = o.allocate(vec![0, 0]).unwrap();
        let c = o.allocate(vec![0, 0]).unwrap();
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
        let a = o.allocate(vec![41]).unwrap();
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
        let dying = o.allocate(vec![0]).unwrap();
        let survivor = o.allocate(vec![0]).unwrap();
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
        let a = o.allocate(vec![0]).unwrap();
        o.acquire(&[a]).unwrap();
        o.release(&[a]).unwrap();
        o.release(&[a]).unwrap();
        let _ = o.next_finalizer();
        // Dead region: further releases are inert, not underflow…
        assert_eq!(o.release(&[a]), Ok(()));
        // …but a live region under-released is caught before going negative.
        let b = o.allocate(vec![0]).unwrap();
        o.release(&[b]).unwrap();
        let _ = o.next_finalizer();
        assert_eq!(o.release(&[b]), Ok(()), "dead again — inert");
        let c = o.allocate(vec![0]).unwrap();
        o.release(&[c]).unwrap(); // count 0, finalizing
        assert_eq!(o.release(&[c]), Ok(()), "finalizing — inert");
    }

    #[test]
    fn nested_teardown_stacks() {
        let mut o = objects();
        let a = o.allocate(vec![0]).unwrap();
        let b = o.allocate(vec![0]).unwrap();
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
        let a = o.allocate(vec![0]).unwrap();
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
