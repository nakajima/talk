use rustc_hash::FxHashMap;

use crate::{
    ir::{function::Function, ir_ty::IrTy},
    name::Name,
};

#[derive(Default)]
pub struct Program {
    pub functions: FxHashMap<Name, Function<IrTy>>,
}
