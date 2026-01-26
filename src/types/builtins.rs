use indexmap::IndexSet;
use rustc_hash::FxHashMap;

use crate::name_resolution::symbol::Symbol;
use crate::types::infer_row::{InferRow, InnerRow};
use crate::types::infer_ty::{Infer, InferTy, InnerTy};
use crate::types::predicate::Predicate;
use crate::types::scheme::{ForAll, Scheme};
use crate::types::term_environment::EnvEntry;

#[macro_export]
macro_rules! indexset {
    ($($k:expr),* $(,)?) => {{
        let mut m = indexmap::IndexSet::default();
        $( m.insert($k); )*
        m
    }};
}

pub fn resolve_builtin_type(id: &Symbol) -> (InferTy, Vec<Predicate<Infer>>, IndexSet<ForAll>) {
    let ty = match *id {
        Symbol::Int => InferTy::Primitive(Symbol::Int),
        Symbol::Float => InferTy::Primitive(Symbol::Float),
        Symbol::Bool => InferTy::Primitive(Symbol::Bool),
        Symbol::Void => InferTy::Primitive(Symbol::Void),
        Symbol::Never => InferTy::Primitive(Symbol::Never),
        Symbol::RawPtr => InferTy::Primitive(Symbol::RawPtr),
        Symbol::Byte => InferTy::Primitive(Symbol::Byte),
        Symbol::IR => InferTy::Func(
            InferTy::String().into(),
            InferTy::Param(Symbol::IR_TYPE_PARAM, vec![]).into(),
            InferRow::Empty.into(),
        ),
        Symbol::PRINT => InferTy::Func(
            InferTy::String().into(),
            InferTy::Param(Symbol::IR_TYPE_PARAM, vec![]).into(),
            InferRow::Empty.into(),
        ),
        _ => unreachable!("no builtin named {id:?}"),
    };

    (ty, vec![], Default::default())
}

pub fn builtin_scope() -> FxHashMap<Symbol, EnvEntry<Infer>> {
    let mut res: FxHashMap<Symbol, EnvEntry<Infer>> = Default::default();

    res.insert(Symbol::Int, EnvEntry::Mono(InnerTy::Int));
    res.insert(Symbol::Float, EnvEntry::Mono(InnerTy::Float));
    res.insert(Symbol::Bool, EnvEntry::Mono(InnerTy::Bool));
    res.insert(Symbol::Void, EnvEntry::Mono(InnerTy::Void));
    res.insert(Symbol::Never, EnvEntry::Mono(InnerTy::Never));
    res.insert(Symbol::Byte, EnvEntry::Mono(InnerTy::Byte));
    res.insert(
        Symbol::RawPtr,
        EnvEntry::Mono(InnerTy::Primitive(Symbol::RawPtr)),
    );
    res.insert(
        Symbol::IR,
        EnvEntry::Scheme(Scheme::<Infer>::new(
            indexset!(ForAll::Ty(Symbol::IR_TYPE_PARAM)),
            vec![],
            InnerTy::Func(
                InnerTy::String().into(),
                InnerTy::Param(Symbol::IR_TYPE_PARAM, vec![]).into(),
                InferRow::Empty.into(),
            ),
        )),
    );
    res.insert(
        Symbol::PRINT,
        EnvEntry::Scheme(Scheme::<Infer>::new(
            indexset!(ForAll::Ty(Symbol::IR_TYPE_PARAM)),
            vec![],
            InnerTy::Func(
                InnerTy::Param(Symbol::IR_TYPE_PARAM, vec![]).into(),
                InnerTy::Void.into(),
                InnerRow::Empty.into(),
            ),
        )),
    );

    res
}
