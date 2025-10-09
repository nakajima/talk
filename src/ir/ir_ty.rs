use indexmap::IndexMap;

use crate::{label::Label, name_resolution::symbol::Symbol};

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum IrTy {
    Int,
    Float,
    Bool,
    Func(Vec<IrTy>, Box<IrTy>),
    Record(IndexMap<Label, IrTy>),
    Enum { symbol: Symbol, values: Vec<IrTy> },
    Void,
}
