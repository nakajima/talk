use rustc_hash::FxHashMap;

use crate::types::infer_ty::InferTy;
use crate::types::predicate::Predicate;
use crate::types::scheme::ForAll;
use crate::types::term_environment::EnvEntry;

use crate::name_resolution::symbol::Symbol;

pub fn resolve_builtin_type(id: &Symbol) -> (InferTy, Vec<Predicate<InferTy>>, Vec<ForAll>) {
    let ty = match *id {
        Symbol::Int => InferTy::Primitive(Symbol::Int),
        Symbol::Float => InferTy::Primitive(Symbol::Float),
        Symbol::Bool => InferTy::Primitive(Symbol::Bool),
        Symbol::Void => InferTy::Primitive(Symbol::Void),
        _ => unreachable!("no builtin named {id:?}"),
    };

    (ty, vec![], vec![])
}

pub fn builtin_scope() -> FxHashMap<Symbol, EnvEntry> {
    let mut res: FxHashMap<Symbol, EnvEntry> = Default::default();

    res.insert(Symbol::Int, EnvEntry::Mono(InferTy::Int));
    res.insert(Symbol::Float, EnvEntry::Mono(InferTy::Float));
    res.insert(Symbol::Bool, EnvEntry::Mono(InferTy::Bool));

    res
}
