use indexmap::IndexSet;
use rustc_hash::FxHashMap;

use crate::types::infer_ty::{InferTy, TypeParamId};
use crate::types::predicate::Predicate;
use crate::types::scheme::{ForAll, Scheme};
use crate::types::term_environment::EnvEntry;

use crate::name_resolution::symbol::Symbol;

#[macro_export]
macro_rules! indexset {
    ($($k:expr),* $(,)?) => {{
        let mut m = indexmap::IndexSet::default();
        $( m.insert($k); )*
        m
    }};
}

pub fn resolve_builtin_type(id: &Symbol) -> (InferTy, Vec<Predicate<InferTy>>, IndexSet<ForAll>) {
    let ty = match *id {
        Symbol::Int => InferTy::Primitive(Symbol::Int),
        Symbol::Float => InferTy::Primitive(Symbol::Float),
        Symbol::Bool => InferTy::Primitive(Symbol::Bool),
        Symbol::Void => InferTy::Primitive(Symbol::Void),
        Symbol::RawPtr => InferTy::Primitive(Symbol::RawPtr),
        Symbol::Byte => InferTy::Primitive(Symbol::Byte),
        _ => unreachable!("no builtin named {id:?}"),
    };

    (ty, vec![], Default::default())
}

pub fn builtin_scope() -> FxHashMap<Symbol, EnvEntry<InferTy>> {
    let mut res: FxHashMap<Symbol, EnvEntry<InferTy>> = Default::default();

    res.insert(Symbol::Int, EnvEntry::Mono(InferTy::Int));
    res.insert(Symbol::Float, EnvEntry::Mono(InferTy::Float));
    res.insert(Symbol::Bool, EnvEntry::Mono(InferTy::Bool));
    res.insert(Symbol::Void, EnvEntry::Mono(InferTy::Void));
    res.insert(Symbol::Byte, EnvEntry::Mono(InferTy::Byte));
    res.insert(
        Symbol::RawPtr,
        EnvEntry::Mono(InferTy::Primitive(Symbol::RawPtr)),
    );
    res.insert(
        Symbol::IR,
        EnvEntry::Scheme(Scheme::<InferTy>::new(
            indexset!(ForAll::Ty(TypeParamId::IR_TYPE_PARAM)),
            vec![],
            InferTy::Func(
                InferTy::String().into(),
                InferTy::Param(TypeParamId::IR_TYPE_PARAM).into(),
            ),
        )),
    );
    res.insert(
        Symbol::PRINT,
        EnvEntry::Scheme(Scheme::<InferTy>::new(
            indexset!(ForAll::Ty(TypeParamId::IR_TYPE_PARAM)),
            vec![],
            InferTy::Func(
                InferTy::Param(TypeParamId::IR_TYPE_PARAM).into(),
                InferTy::Void.into(),
            ),
        )),
    );

    res
}
