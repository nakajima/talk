use std::collections::BTreeMap;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AllocationRecord {
    pub start: u32,
    pub len: usize,
    pub live: bool,
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
        });
        self.index.insert(addr, index);
        Ok(addr)
    }

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
        record.live = false;
        Ok(())
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
