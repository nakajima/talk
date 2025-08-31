use crate::types::ty::{Primitive, Ty};

use crate::name_resolution::symbol::Symbol;

pub fn resolve_builtin_type(id: &Symbol) -> Ty {
    match *id {
        Symbol::Int => Ty::Primitive(Primitive::Int),
        Symbol::Float => Ty::Primitive(Primitive::Float),
        Symbol::Bool => Ty::Primitive(Primitive::Bool),
        _ => unreachable!("no builtin named {id:?}"),
    }
}
