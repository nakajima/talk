use crate::name_resolution::{
    name_resolver::Scope,
    symbol::{BuiltinId, Symbol},
};

pub fn import_builtins(scope: &mut Scope) {
    scope
        .types
        .insert("Int".into(), Symbol::BuiltinType(BuiltinId(1)));
    scope
        .types
        .insert("Float".into(), Symbol::BuiltinType(BuiltinId(2)));
    scope
        .types
        .insert("Bool".into(), Symbol::BuiltinType(BuiltinId(3)));
}
