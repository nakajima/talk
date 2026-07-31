use rustc_hash::FxHashMap;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Pointer {
    address: u32,
    /// Zero identifies static memory; allocation record N uses N + 1.
    provenance: u32,
}

impl Pointer {
    pub const fn static_at(address: u32) -> Self {
        Self {
            address,
            provenance: 0,
        }
    }

    pub const fn address(self) -> u32 {
        self.address
    }

    pub fn checked_add(self, offset: usize) -> Option<Self> {
        Some(Self {
            address: self.address.checked_add(u32::try_from(offset).ok()?)?,
            provenance: self.provenance,
        })
    }

    pub(crate) const fn encode(self) -> u64 {
        (self.provenance as u64) << 32 | self.address as u64
    }

    pub(crate) const fn decode(word: u64) -> Self {
        Self {
            address: word as u32,
            provenance: (word >> 32) as u32,
        }
    }

    pub(crate) const fn wrapping_offset(self, offset: i64) -> Self {
        Self {
            address: self.address.wrapping_add(offset as u32),
            provenance: self.provenance,
        }
    }

    /// The allocation this pointer belongs to, or `None` for static data.
    const fn allocation_id(self) -> Option<u32> {
        match self.provenance {
            0 => None,
            id => Some(id),
        }
    }

    const fn allocated(address: u32, id: u32) -> Self {
        Self {
            address,
            provenance: id,
        }
    }
}

/// A live allocation. There is no `live` flag: a record exists for
/// exactly as long as its allocation does, and dying means being removed.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AllocationRecord {
    pub start: u32,
    pub len: usize,
    /// Reference count: shared buffers (copy-on-write clones) retain; every
    /// free releases; the record dies at zero.
    pub rc: u32,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Allocations {
    /// Live allocations by provenance id. Dead records are removed, so
    /// this is bounded by what the program currently holds rather than by
    /// everything it has ever allocated.
    records: FxHashMap<u32, AllocationRecord>,
    /// The next provenance to issue. Ids are never reused, so a pointer
    /// to a freed allocation can never resolve to a live one, and an id
    /// below this watermark is one that was issued and has since died.
    next_id: u32,
    /// Spans returned by `free`, keyed by their reserved length. A later
    /// allocation of the same span reuses the address instead of
    /// extending memory, which is what keeps an allocate/free loop from
    /// growing the byte memory without bound.
    ///
    /// Reusing an address is not a weakening: every access resolves its
    /// record through the pointer's *provenance*, and provenance is still
    /// minted fresh for every allocation and never recycled. A pointer to
    /// a freed span therefore still finds its own dead record, however
    /// many times the address is handed out again.
    free_spans: FxHashMap<usize, Vec<u32>>,
}

impl Default for Allocations {
    fn default() -> Self {
        Self {
            records: FxHashMap::default(),
            // Provenance zero means static data, so ids start at one.
            next_id: 1,
            free_spans: FxHashMap::default(),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MemoryError {
    AddressOutOfRange,
    AllocationTooLarge,
    InvalidFree,
    DoubleFree,
    OutOfBounds { op: String },
    InvalidPointer { op: String },
}

impl Allocations {
    /// Resolve a managed pointer's record. Removing dead records would
    /// otherwise blur "freed" into "never existed"; the watermark keeps
    /// them apart, since an id below it was issued and has since died.
    fn record(&self, id: u32) -> Result<&AllocationRecord, MemoryError> {
        match self.records.get(&id) {
            Some(record) => Ok(record),
            None if id < self.next_id => Err(MemoryError::DoubleFree),
            None => Err(MemoryError::InvalidFree),
        }
    }

    fn record_mut(&mut self, id: u32) -> Result<&mut AllocationRecord, MemoryError> {
        match self.records.entry(id) {
            std::collections::hash_map::Entry::Occupied(entry) => Ok(entry.into_mut()),
            std::collections::hash_map::Entry::Vacant(_) if id < self.next_id => {
                Err(MemoryError::DoubleFree)
            }
            std::collections::hash_map::Entry::Vacant(_) => Err(MemoryError::InvalidFree),
        }
    }

    pub fn allocate(&mut self, mem: &mut Vec<u8>, count: usize) -> Result<Pointer, MemoryError> {
        // Take the id before touching the free list, so a rejected
        // allocation cannot lose a span.
        let id = self.next_id;
        let next_id = id.checked_add(1).ok_or(MemoryError::AllocationTooLarge)?;
        // Only an exactly matching span is reused: handing a small
        // request a larger span would leave the tail unreachable, and
        // handing a large request a smaller one would be unsound.
        let reserve = count.max(1);
        let address = match self
            .free_spans
            .get_mut(&reserve)
            .and_then(|addresses| addresses.pop())
        {
            Some(address) => {
                // `resize` zero-fills fresh memory, so recycled memory has
                // to be zeroed too or an allocation would observe the
                // previous occupant's bytes.
                let start = address as usize;
                mem[start..start + reserve].fill(0);
                address
            }
            None => {
                let address =
                    u32::try_from(mem.len()).map_err(|_| MemoryError::AddressOutOfRange)?;
                let new_len = mem
                    .len()
                    .checked_add(reserve)
                    .ok_or(MemoryError::AllocationTooLarge)?;
                mem.resize(new_len, 0);
                address
            }
        };
        self.next_id = next_id;
        self.records.insert(
            id,
            AllocationRecord {
                start: address,
                len: count,
                rc: 1,
            },
        );
        Ok(Pointer::allocated(address, id))
    }

    /// Release one reference; the allocation dies when the count reaches
    /// zero. Static data is never freed.
    pub fn free(&mut self, static_len: u32, pointer: Pointer) -> Result<(), MemoryError> {
        let Some(id) = pointer.allocation_id() else {
            return if pointer.address < static_len {
                Ok(())
            } else {
                Err(MemoryError::InvalidFree)
            };
        };
        let record = self.record_mut(id)?;
        if record.start != pointer.address {
            return Err(MemoryError::InvalidFree);
        }
        record.rc -= 1;
        if record.rc > 0 {
            return Ok(());
        }
        // The allocation dies: its record goes, and its span becomes
        // available to a later allocation of the same size.
        let (start, reserve) = (record.start, record.len.max(1));
        self.records.remove(&id);
        self.free_spans.entry(reserve).or_default().push(start);
        Ok(())
    }

    /// Add one reference (a copy-on-write clone). Static data is unmanaged.
    pub fn retain(&mut self, static_len: u32, pointer: Pointer) -> Result<(), MemoryError> {
        let Some(id) = pointer.allocation_id() else {
            return if pointer.address < static_len {
                Ok(())
            } else {
                Err(MemoryError::InvalidFree)
            };
        };
        let record = self.record_mut(id)?;
        if record.start != pointer.address {
            return Err(MemoryError::InvalidFree);
        }
        record.rc += 1;
        Ok(())
    }

    /// Whether this allocation has exactly one reference (in-place mutation
    /// is safe). Static data is shared forever: never unique.
    pub fn is_unique(&self, static_len: u32, pointer: Pointer) -> Result<bool, MemoryError> {
        let Some(id) = pointer.allocation_id() else {
            return if pointer.address < static_len {
                Ok(false)
            } else {
                Err(MemoryError::InvalidFree)
            };
        };
        // A dead allocation is not unique, it is gone -- which is the
        // `false` the `live && rc == 1` test used to produce. A forged id
        // stays an error, as it was.
        let record = match self.record(id) {
            Ok(record) => record,
            Err(MemoryError::DoubleFree) => return Ok(false),
            Err(error) => return Err(error),
        };
        if record.start != pointer.address {
            return Err(MemoryError::InvalidFree);
        }
        Ok(record.rc == 1)
    }

    /// Live allocation count - the leak invariant for tests.
    pub fn live_count(&self) -> usize {
        self.records.len()
    }

    /// Base address of the live allocation identified by `pointer`.
    pub fn live_base(&self, pointer: Pointer) -> Option<u32> {
        Some(self.live_record(pointer)?.start)
    }

    /// The live allocation record identified by an interior pointer. Raw
    /// pointer arithmetic preserves the provenance used for this direct
    /// record lookup.
    pub fn live_record(&self, pointer: Pointer) -> Option<&AllocationRecord> {
        let record = self.records.get(&pointer.allocation_id()?)?;
        let start = record.start as usize;
        // Zero-length allocations still reserve one byte (`allocate`).
        let end = start + record.len.max(1);
        ((pointer.address as usize) >= start && (pointer.address as usize) < end).then_some(record)
    }

    pub fn check_access(
        &self,
        mem_len: usize,
        static_len: u32,
        pointer: Pointer,
        len: usize,
        op: &str,
    ) -> Result<(), MemoryError> {
        let start = pointer.address as usize;
        let end = start
            .checked_add(len)
            .ok_or_else(|| MemoryError::out_of_bounds(op))?;
        if end > mem_len {
            return Err(MemoryError::out_of_bounds(op));
        }
        let Some(id) = pointer.allocation_id() else {
            return if end <= static_len as usize {
                Ok(())
            } else {
                Err(MemoryError::invalid_pointer(op))
            };
        };
        if self.records.get(&id).is_some_and(|record| {
            let alloc_start = record.start as usize;
            let alloc_end = alloc_start + record.len;
            start >= alloc_start && end <= alloc_end
        }) {
            return Ok(());
        }
        Err(MemoryError::invalid_pointer(op))
    }

    pub fn accessible_tail_end(
        &self,
        mem_len: usize,
        static_len: u32,
        pointer: Pointer,
        op: &str,
    ) -> Result<usize, MemoryError> {
        let start = pointer.address as usize;
        if start >= mem_len {
            return Err(MemoryError::out_of_bounds(op));
        }
        let Some(id) = pointer.allocation_id() else {
            return if start < static_len as usize {
                Ok(static_len as usize)
            } else {
                Err(MemoryError::invalid_pointer(op))
            };
        };
        let Some(record) = self.records.get(&id).filter(|record| {
            let alloc_start = record.start as usize;
            let alloc_end = alloc_start + record.len;
            start >= alloc_start && start < alloc_end
        }) else {
            return Err(MemoryError::invalid_pointer(op));
        };
        Ok(record.start as usize + record.len)
    }
}

impl MemoryError {
    fn out_of_bounds(op: &str) -> Self {
        Self::OutOfBounds { op: op.to_string() }
    }

    fn invalid_pointer(op: &str) -> Self {
        Self::InvalidPointer { op: op.to_string() }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn retain_release_lifecycle() {
        let mut mem = vec![0u8; 8];
        let mut allocations = Allocations::default();
        let pointer = allocations.allocate(&mut mem, 4).expect("alloc");
        assert!(allocations.is_unique(8, pointer).expect("unique"));

        allocations.retain(8, pointer).expect("retain");
        assert!(!allocations.is_unique(8, pointer).expect("shared"));

        allocations.free(8, pointer).expect("first release");
        assert_eq!(allocations.live_count(), 1, "still one reference");
        assert!(allocations.is_unique(8, pointer).expect("unique again"));

        allocations.free(8, pointer).expect("final release");
        assert_eq!(allocations.live_count(), 0);
        assert_eq!(allocations.free(8, pointer), Err(MemoryError::DoubleFree));
        assert_eq!(allocations.retain(8, pointer), Err(MemoryError::DoubleFree));
    }

    #[test]
    fn provenance_resolves_interior_pointers_in_constant_time() {
        let mut mem = vec![0u8; 8];
        let mut allocations = Allocations::default();
        let pointer = allocations.allocate(&mut mem, 4).expect("alloc");
        let interior = pointer.checked_add(3).expect("interior");
        let one_past = pointer.checked_add(4).expect("one past");

        assert_eq!(allocations.live_base(pointer), Some(pointer.address()));
        assert_eq!(
            allocations.live_base(interior),
            Some(pointer.address()),
            "interior"
        );
        assert_eq!(allocations.live_base(one_past), None, "one past");
        assert_eq!(
            allocations.live_base(Pointer::static_at(4)),
            None,
            "statics are unmanaged"
        );

        allocations.free(8, pointer).expect("release");
        assert_eq!(allocations.live_base(interior), None, "dead record");
    }

    #[test]
    fn access_rejects_cross_allocation_and_forged_provenance() {
        let mut mem = vec![0u8; 8];
        let mut allocations = Allocations::default();
        let first = allocations.allocate(&mut mem, 4).expect("first");
        let second = allocations.allocate(&mut mem, 4).expect("second");

        assert!(
            allocations
                .check_access(mem.len(), 8, first, 4, "load")
                .is_ok()
        );
        assert!(
            allocations
                .check_access(mem.len(), 8, first, 5, "load")
                .is_err()
        );
        let forged = Pointer {
            address: second.address(),
            provenance: first.provenance,
        };
        assert!(
            allocations
                .check_access(mem.len(), 8, forged, 1, "load")
                .is_err()
        );
    }

    #[test]
    fn pointer_words_preserve_address_and_provenance() {
        let mut mem = vec![0u8; 8];
        let mut allocations = Allocations::default();
        let pointer = allocations.allocate(&mut mem, 4).expect("alloc");
        assert_eq!(Pointer::decode(pointer.encode()), pointer);
        let static_pointer = Pointer::static_at(7);
        assert_eq!(Pointer::decode(static_pointer.encode()), static_pointer);
    }

    /// A loop that allocates and frees the same size must not grow the
    /// byte memory. Before the free list, every iteration appended.
    #[test]
    fn freed_space_is_reused_by_a_later_allocation_of_the_same_size() {
        let mut mem = vec![0u8; 8];
        let mut allocations = Allocations::default();

        let first = allocations.allocate(&mut mem, 32).expect("first");
        allocations.free(8, first).expect("release");
        let high_water = mem.len();

        for _ in 0..1000 {
            let pointer = allocations.allocate(&mut mem, 32).expect("reused");
            assert_eq!(
                pointer.address(),
                first.address(),
                "the freed span should come back"
            );
            allocations.free(8, pointer).expect("release");
        }
        assert_eq!(mem.len(), high_water, "byte memory grew across a free loop");
    }

    /// Reuse must not resurrect a dangling pointer. Provenance is still
    /// minted fresh per allocation, so the stale pointer resolves to its
    /// own dead record however many times the address is recycled.
    #[test]
    fn a_stale_pointer_is_still_rejected_after_its_address_is_reused() {
        let mut mem = vec![0u8; 8];
        let mut allocations = Allocations::default();

        let stale = allocations.allocate(&mut mem, 16).expect("first");
        allocations.free(8, stale).expect("release");

        let fresh = allocations.allocate(&mut mem, 16).expect("second");
        assert_eq!(fresh.address(), stale.address(), "address was recycled");
        assert_ne!(fresh.provenance, stale.provenance, "provenance is fresh");

        assert!(
            allocations
                .check_access(mem.len(), 8, fresh, 16, "load")
                .is_ok()
        );
        assert!(
            allocations
                .check_access(mem.len(), 8, stale, 16, "load")
                .is_err(),
            "use-after-free must not validate against the new allocation"
        );
        assert_eq!(allocations.live_base(stale), None);
        assert_eq!(allocations.free(8, stale), Err(MemoryError::DoubleFree));
    }

    /// Fresh memory reads as zero (`resize` zero-fills). Recycled memory
    /// has to be zeroed too, or an allocation would observe the previous
    /// occupant's bytes.
    #[test]
    fn reused_space_is_zeroed() {
        let mut mem = vec![0u8; 8];
        let mut allocations = Allocations::default();

        let first = allocations.allocate(&mut mem, 4).expect("first");
        let start = first.address() as usize;
        mem[start..start + 4].copy_from_slice(&[0xAB; 4]);
        allocations.free(8, first).expect("release");

        let second = allocations.allocate(&mut mem, 4).expect("second");
        let start = second.address() as usize;
        assert_eq!(&mem[start..start + 4], &[0, 0, 0, 0], "stale bytes leaked");
    }

    /// A free list keyed by span must not hand a small request a larger
    /// span, or the allocation would under-report its accessible length.
    #[test]
    fn reuse_requires_a_matching_span() {
        let mut mem = vec![0u8; 8];
        let mut allocations = Allocations::default();

        let big = allocations.allocate(&mut mem, 64).expect("big");
        allocations.free(8, big).expect("release");

        let small = allocations.allocate(&mut mem, 8).expect("small");
        assert_ne!(
            small.address(),
            big.address(),
            "a 64-byte span must not satisfy an 8-byte request"
        );
        let same = allocations.allocate(&mut mem, 64).expect("same size");
        assert_eq!(same.address(), big.address(), "the 64-byte span is free");
    }

    /// The record table must track *live* allocations, not every
    /// allocation ever made: it was the dominant term in a long run's
    /// memory, at 24 bytes apiece.
    #[test]
    fn dead_records_do_not_accumulate() {
        let mut mem = vec![0u8; 8];
        let mut allocations = Allocations::default();

        for _ in 0..1000 {
            let pointer = allocations.allocate(&mut mem, 16).expect("alloc");
            allocations.free(8, pointer).expect("release");
        }
        assert_eq!(allocations.live_count(), 0);
        assert_eq!(
            allocations.records.len(),
            0,
            "dead records accumulated instead of being reclaimed"
        );
    }

    /// Reclaiming records must not blur the two failures apart. An id
    /// below the watermark was issued and has since died; an id at or
    /// above it was never issued at all.
    #[test]
    fn a_dead_id_is_a_double_free_and_an_unissued_id_is_invalid() {
        let mut mem = vec![0u8; 8];
        let mut allocations = Allocations::default();
        let pointer = allocations.allocate(&mut mem, 8).expect("alloc");
        allocations.free(8, pointer).expect("release");

        assert_eq!(allocations.free(8, pointer), Err(MemoryError::DoubleFree));
        assert_eq!(allocations.retain(8, pointer), Err(MemoryError::DoubleFree));

        let forged = Pointer {
            address: pointer.address(),
            provenance: 9999,
        };
        assert_eq!(allocations.free(8, forged), Err(MemoryError::InvalidFree));
        assert_eq!(allocations.retain(8, forged), Err(MemoryError::InvalidFree));
    }

    #[test]
    fn static_data_is_unmanaged_but_still_bounded() {
        let mut allocations = Allocations::default();
        let pointer = Pointer::static_at(4);
        allocations.free(16, pointer).expect("static free");
        allocations.retain(16, pointer).expect("static retain");
        assert!(!allocations.is_unique(16, pointer).expect("static unique"));
        assert!(
            allocations
                .check_access(16, 16, pointer, 12, "load")
                .is_ok()
        );
        assert!(
            allocations
                .check_access(17, 16, pointer, 13, "load")
                .is_err()
        );
    }
}
