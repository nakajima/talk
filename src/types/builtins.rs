use rustc_hash::FxHashMap;

use crate::types::passes::inference_pass::EnvEntry;
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

pub fn builtin_scope() -> FxHashMap<Symbol, EnvEntry> {
    let mut res: FxHashMap<Symbol, EnvEntry> = Default::default();

    res.insert(Symbol::Int, EnvEntry::Mono(Ty::Int));
    res.insert(Symbol::Float, EnvEntry::Mono(Ty::Float));
    res.insert(Symbol::Bool, EnvEntry::Mono(Ty::Bool));

    res
}
