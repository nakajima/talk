use std::{
    alloc::{Layout, alloc, dealloc},
    cell::Cell,
    ptr::NonNull,
};

const ARENA_SIZE: usize = 1024 * 1024; // 1MB arenas
const ALIGNMENT: usize = 16;

#[derive(Debug)]
pub struct Arena {
    chunks: Vec<ArenaChunk>,
    current: Cell<usize>,
    offset: Cell<usize>,
}

#[derive(Debug)]
struct ArenaChunk {
    data: NonNull<u8>,
    layout: Layout,
}

impl Default for Arena {
    fn default() -> Self {
        Self::new()
    }
}

impl Arena {
    pub fn new() -> Self {
        let mut arena = Self {
            chunks: Vec::new(),
            current: Cell::new(0),
            offset: Cell::new(0),
        };
        arena.allocate_chunk();
        arena
    }

    fn allocate_chunk(&mut self) {
        let layout = Layout::from_size_align(ARENA_SIZE, ALIGNMENT).expect("Invalid arena layout");

        unsafe {
            let ptr = alloc(layout);
            if ptr.is_null() {
                panic!("Arena allocation failed");
            }

            self.chunks.push(ArenaChunk {
                data: NonNull::new_unchecked(ptr),
                layout,
            });
        }
    }

    pub fn alloc(&mut self, size: usize, align: usize) -> NonNull<u8> {
        let size = (size + align - 1) & !(align - 1); // Round up to alignment

        // Check if we need a new chunk
        if self.offset.get() + size > ARENA_SIZE {
            if self.current.get() + 1 >= self.chunks.len() {
                self.allocate_chunk();
            }
            self.current.set(self.current.get() + 1);
            self.offset.set(0);
        }

        let chunk = &self.chunks[self.current.get()];
        let offset = self.offset.get();
        self.offset.set(offset + size);

        unsafe { NonNull::new_unchecked(chunk.data.as_ptr().add(offset)) }
    }

    pub fn reset(&mut self) {
        self.current.set(0);
        self.offset.set(0);
    }
}

impl Drop for Arena {
    fn drop(&mut self) {
        for chunk in &self.chunks {
            unsafe {
                dealloc(chunk.data.as_ptr(), chunk.layout);
            }
        }
    }
}

unsafe impl Send for Arena {}
unsafe impl Sync for Arena {}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_arena_allocation() {
        let mut arena = Arena::new();

        // Allocate some memory
        let ptr1 = arena.alloc(64, 8);
        let ptr2 = arena.alloc(128, 16);

        // Verify they're different
        assert_ne!(ptr1.as_ptr(), ptr2.as_ptr());

        // Write and read back
        unsafe {
            *ptr1.as_ptr() = 42;
            assert_eq!(*ptr1.as_ptr(), 42);
        }
    }

    #[test]
    fn test_arena_reset() {
        let mut arena = Arena::new();

        let ptr1 = arena.alloc(64, 8);
        arena.reset();
        let ptr2 = arena.alloc(64, 8);

        // After reset, we should get the same address
        assert_eq!(ptr1.as_ptr(), ptr2.as_ptr());
    }
}
