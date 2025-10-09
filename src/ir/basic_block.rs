use crate::ir::{instruction::Instruction, terminator::Terminator};

#[derive(Debug, Clone, Copy, PartialEq, Default)]
pub struct BasicBlockId(pub u32);

#[derive(Debug, Clone, PartialEq)]
pub struct BasicBlock<T> {
    pub id: BasicBlockId,
    pub instructions: Vec<Instruction<T>>,
    pub terminator: Terminator<T>,
}
