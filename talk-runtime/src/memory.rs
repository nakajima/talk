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

    const fn allocation_index(self) -> Option<usize> {
        match self.provenance.checked_sub(1) {
            Some(index) => Some(index as usize),
            None => None,
        }
    }

    fn allocated(address: u32, index: usize) -> Result<Self, MemoryError> {
        let provenance = u32::try_from(index)
            .ok()
            .and_then(|index| index.checked_add(1))
            .ok_or(MemoryError::AllocationTooLarge)?;
        Ok(Self {
            address,
            provenance,
        })
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AllocationRecord {
    pub start: u32,
    pub len: usize,
    pub live: bool,
    /// Reference count: shared buffers (copy-on-write clones) retain; every
    /// free releases; the record dies at zero.
    pub rc: u32,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Allocations {
    records: Vec<AllocationRecord>,
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
    pub fn allocate(&mut self, mem: &mut Vec<u8>, count: usize) -> Result<Pointer, MemoryError> {
        let address = u32::try_from(mem.len()).map_err(|_| MemoryError::AddressOutOfRange)?;
        let pointer = Pointer::allocated(address, self.records.len())?;
        let reserve = count.max(1);
        let new_len = mem
            .len()
            .checked_add(reserve)
            .ok_or(MemoryError::AllocationTooLarge)?;
        mem.resize(new_len, 0);
        self.records.push(AllocationRecord {
            start: address,
            len: count,
            live: true,
            rc: 1,
        });
        Ok(pointer)
    }

    /// Release one reference; the allocation dies when the count reaches
    /// zero. Static data is never freed.
    pub fn free(&mut self, static_len: u32, pointer: Pointer) -> Result<(), MemoryError> {
        let Some(index) = pointer.allocation_index() else {
            return if pointer.address < static_len {
                Ok(())
            } else {
                Err(MemoryError::InvalidFree)
            };
        };
        let Some(record) = self.records.get_mut(index) else {
            return Err(MemoryError::InvalidFree);
        };
        if record.start != pointer.address {
            return Err(MemoryError::InvalidFree);
        }
        if !record.live {
            return Err(MemoryError::DoubleFree);
        }
        record.rc -= 1;
        if record.rc == 0 {
            record.live = false;
        }
        Ok(())
    }

    /// Add one reference (a copy-on-write clone). Static data is unmanaged.
    pub fn retain(&mut self, static_len: u32, pointer: Pointer) -> Result<(), MemoryError> {
        let Some(index) = pointer.allocation_index() else {
            return if pointer.address < static_len {
                Ok(())
            } else {
                Err(MemoryError::InvalidFree)
            };
        };
        let Some(record) = self.records.get_mut(index) else {
            return Err(MemoryError::InvalidFree);
        };
        if record.start != pointer.address {
            return Err(MemoryError::InvalidFree);
        }
        if !record.live {
            return Err(MemoryError::DoubleFree);
        }
        record.rc += 1;
        Ok(())
    }

    /// Whether this allocation has exactly one reference (in-place mutation
    /// is safe). Static data is shared forever: never unique.
    pub fn is_unique(&self, static_len: u32, pointer: Pointer) -> Result<bool, MemoryError> {
        let Some(index) = pointer.allocation_index() else {
            return if pointer.address < static_len {
                Ok(false)
            } else {
                Err(MemoryError::InvalidFree)
            };
        };
        let Some(record) = self.records.get(index) else {
            return Err(MemoryError::InvalidFree);
        };
        if record.start != pointer.address {
            return Err(MemoryError::InvalidFree);
        }
        Ok(record.live && record.rc == 1)
    }

    /// Live allocation count - the leak invariant for tests.
    pub fn live_count(&self) -> usize {
        self.records.iter().filter(|record| record.live).count()
    }

    /// Base address of the live allocation identified by `pointer`.
    pub fn live_base(&self, pointer: Pointer) -> Option<u32> {
        Some(self.live_record(pointer)?.start)
    }

    /// The live allocation record identified by an interior pointer. Raw
    /// pointer arithmetic preserves the provenance used for this direct
    /// record lookup.
    pub fn live_record(&self, pointer: Pointer) -> Option<&AllocationRecord> {
        let index = pointer.allocation_index()?;
        let record = self.records.get(index)?;
        let start = record.start as usize;
        // Zero-length allocations still reserve one byte (`allocate`).
        let end = start + record.len.max(1);
        (record.live && (pointer.address as usize) >= start && (pointer.address as usize) < end)
            .then_some(record)
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
        let Some(index) = pointer.allocation_index() else {
            return if end <= static_len as usize {
                Ok(())
            } else {
                Err(MemoryError::invalid_pointer(op))
            };
        };
        if self.records.get(index).is_some_and(|record| {
            let alloc_start = record.start as usize;
            let alloc_end = alloc_start + record.len;
            record.live && start >= alloc_start && end <= alloc_end
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
        let Some(index) = pointer.allocation_index() else {
            return if start < static_len as usize {
                Ok(static_len as usize)
            } else {
                Err(MemoryError::invalid_pointer(op))
            };
        };
        let Some(record) = self.records.get(index).filter(|record| {
            let alloc_start = record.start as usize;
            let alloc_end = alloc_start + record.len;
            record.live && start >= alloc_start && start < alloc_end
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
