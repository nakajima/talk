use std::marker::PhantomData;

use crate::{
    expr::{Expr, ExprMeta},
    parser::ExprID,
    symbol_table::SymbolID,
    type_checker::Ty,
};

// Phase markers
pub struct Parsed;
pub struct NameResolved;
pub struct Typed;

pub struct Program<Phase = Parsed> {
    roots: Vec<ExprID>,
    nodes: Vec<Expr>,
    meta: Vec<ExprMeta>,
    types: Vec<Option<Ty>>,         // Only valid after TypeChecked
    symbols: Vec<Option<SymbolID>>, // Only valid after NameResolved
    _phase: PhantomData<Phase>,
}
