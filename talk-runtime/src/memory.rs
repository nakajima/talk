use std::collections::BTreeMap;

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
    index: BTreeMap<u32, usize>,
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
    pub fn clear(&mut self) {
        self.records.clear();
        self.index.clear();
    }

    pub fn allocate(&mut self, mem: &mut Vec<u8>, count: usize) -> Result<u32, MemoryError> {
        let addr = u32::try_from(mem.len()).map_err(|_| MemoryError::AddressOutOfRange)?;
        let reserve = count.max(1);
        let new_len = mem
            .len()
            .checked_add(reserve)
            .ok_or(MemoryError::AllocationTooLarge)?;
        mem.resize(new_len, 0);
        let index = self.records.len();
        self.records.push(AllocationRecord {
            start: addr,
            len: count,
            live: true,
            rc: 1,
        });
        self.index.insert(addr, index);
        Ok(addr)
    }

    /// Release one reference; the allocation dies when the count reaches
    /// zero. Static data is never freed.
    pub fn free(&mut self, static_len: u32, ptr: u32) -> Result<(), MemoryError> {
        if ptr < static_len {
            return Ok(());
        }
        let Some(&index) = self.index.get(&ptr) else {
            return Err(MemoryError::InvalidFree);
        };
        let record = &mut self.records[index];
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
    pub fn retain(&mut self, static_len: u32, ptr: u32) -> Result<(), MemoryError> {
        if ptr < static_len {
            return Ok(());
        }
        let Some(&index) = self.index.get(&ptr) else {
            return Err(MemoryError::InvalidFree);
        };
        let record = &mut self.records[index];
        if !record.live {
            return Err(MemoryError::DoubleFree);
        }
        record.rc += 1;
        Ok(())
    }

    /// Whether this allocation has exactly one reference (in-place mutation
    /// is safe). Static data is shared forever: never unique.
    pub fn is_unique(&self, static_len: u32, ptr: u32) -> Result<bool, MemoryError> {
        if ptr < static_len {
            return Ok(false);
        }
        let Some(&index) = self.index.get(&ptr) else {
            return Err(MemoryError::InvalidFree);
        };
        let record = &self.records[index];
        Ok(record.live && record.rc == 1)
    }

    /// Live allocation count — the leak invariant for tests.
    pub fn live_count(&self) -> usize {
        self.records.iter().filter(|record| record.live).count()
    }


    pub fn check_access(
        &self,
        mem_len: usize,
        static_len: u32,
        addr: u32,
        len: usize,
        op: &str,
    ) -> Result<(), MemoryError> {
        let start = addr as usize;
        let end = start
            .checked_add(len)
            .ok_or_else(|| MemoryError::out_of_bounds(op))?;
        if end > mem_len {
            return Err(MemoryError::out_of_bounds(op));
        }
        if end <= static_len as usize {
            return Ok(());
        }
        if self.record_containing(addr).is_some_and(|record| {
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
        addr: u32,
        op: &str,
    ) -> Result<usize, MemoryError> {
        let start = addr as usize;
        if start >= mem_len {
            return Err(MemoryError::out_of_bounds(op));
        }
        if addr < static_len {
            return Ok(static_len as usize);
        }
        let Some(record) = self.record_containing(addr).filter(|record| {
            let alloc_start = record.start as usize;
            let alloc_end = alloc_start + record.len;
            record.live && start >= alloc_start && start < alloc_end
        }) else {
            return Err(MemoryError::invalid_pointer(op));
        };
        Ok(record.start as usize + record.len)
    }

    fn record_containing(&self, addr: u32) -> Option<&AllocationRecord> {
        let (_, index) = self.index.range(..=addr).next_back()?;
        self.records.get(*index)
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
        let ptr = allocations.allocate(&mut mem, 4).expect("alloc");
        assert!(allocations.is_unique(8, ptr).expect("unique"));

        allocations.retain(8, ptr).expect("retain");
        assert!(!allocations.is_unique(8, ptr).expect("shared"));

        allocations.free(8, ptr).expect("first release");
        assert_eq!(allocations.live_count(), 1, "still one reference");
        assert!(allocations.is_unique(8, ptr).expect("unique again"));

        allocations.free(8, ptr).expect("final release");
        assert_eq!(allocations.live_count(), 0);
        assert_eq!(allocations.free(8, ptr), Err(MemoryError::DoubleFree));
        assert_eq!(allocations.retain(8, ptr), Err(MemoryError::DoubleFree));
    }

    #[test]
    fn static_data_is_unmanaged() {
        let mut allocations = Allocations::default();
        allocations.free(16, 4).expect("static free is a no-op");
        allocations.retain(16, 4).expect("static retain is a no-op");
        assert!(!allocations.is_unique(16, 4).expect("static never unique"));
    }
}
