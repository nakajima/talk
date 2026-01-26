use indexmap::IndexSet;
use rustc_hash::FxHashMap;

use crate::name_resolution::symbol::Symbol;
use crate::types::infer_row::Row;
use crate::types::infer_ty::Ty;
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

pub fn resolve_builtin_type(id: &Symbol) -> (Ty, Vec<Predicate>, IndexSet<ForAll>) {
    let ty = match *id {
        Symbol::Int => Ty::Primitive(Symbol::Int),
        Symbol::Float => Ty::Primitive(Symbol::Float),
        Symbol::Bool => Ty::Primitive(Symbol::Bool),
        Symbol::Void => Ty::Primitive(Symbol::Void),
        Symbol::Never => Ty::Primitive(Symbol::Never),
        Symbol::RawPtr => Ty::Primitive(Symbol::RawPtr),
        Symbol::Byte => Ty::Primitive(Symbol::Byte),
        Symbol::IR => Ty::Func(
            Ty::String().into(),
            Ty::Param(Symbol::IR_TYPE_PARAM, vec![]).into(),
            Row::Empty.into(),
        ),
        Symbol::PRINT => Ty::Func(
            Ty::String().into(),
            Ty::Param(Symbol::IR_TYPE_PARAM, vec![]).into(),
            Row::Empty.into(),
        ),
        _ => unreachable!("no builtin named {id:?}"),
    };

    (ty, vec![], Default::default())
}

pub fn builtin_scope() -> FxHashMap<Symbol, EnvEntry> {
    let mut res: FxHashMap<Symbol, EnvEntry> = Default::default();

    res.insert(Symbol::Int, EnvEntry::Mono(Ty::Int));
    res.insert(Symbol::Float, EnvEntry::Mono(Ty::Float));
    res.insert(Symbol::Bool, EnvEntry::Mono(Ty::Bool));
    res.insert(Symbol::Void, EnvEntry::Mono(Ty::Void));
    res.insert(Symbol::Never, EnvEntry::Mono(Ty::Never));
    res.insert(Symbol::Byte, EnvEntry::Mono(Ty::Byte));
    res.insert(
        Symbol::RawPtr,
        EnvEntry::Mono(Ty::Primitive(Symbol::RawPtr)),
    );
    res.insert(
        Symbol::IR,
        EnvEntry::Scheme(Scheme::new(
            indexset!(ForAll::Ty(Symbol::IR_TYPE_PARAM)),
            vec![],
            Ty::Func(
                Ty::String().into(),
                Ty::Param(Symbol::IR_TYPE_PARAM, vec![]).into(),
                Row::Empty.into(),
            ),
        )),
    );
    res.insert(
        Symbol::PRINT,
        EnvEntry::Scheme(Scheme::new(
            indexset!(ForAll::Ty(Symbol::IR_TYPE_PARAM)),
            vec![],
            Ty::Func(
                Ty::Param(Symbol::IR_TYPE_PARAM, vec![]).into(),
                Ty::Void.into(),
                Row::Empty.into(),
            ),
        )),
    );

    res
}
