use crate::name_resolution::{
    name_resolver::Scope,
    symbol::{BuiltinId, Symbol},
};

pub fn import_builtins(scope: &mut Scope) {
    scope
        .types
        .insert("Int".into(), Symbol::Builtin(BuiltinId(1)));
    scope
        .types
        .insert("Float".into(), Symbol::Builtin(BuiltinId(2)));
    scope
        .types
        .insert("Bool".into(), Symbol::Builtin(BuiltinId(3)));
}
