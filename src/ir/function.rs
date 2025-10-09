use crate::{
    ir::{basic_block::BasicBlock, ir_ty::IrTy},
    name::Name,
};

#[derive(Debug, Clone, PartialEq)]
pub struct Function<T> {
    pub name: Name,
    pub blocks: Vec<BasicBlock<T>>,
    pub ty: IrTy,
}
