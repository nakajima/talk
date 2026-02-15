use crate::name_resolution::{name_resolver::Scope, symbol::Symbol};

pub fn import_builtins(scope: &mut Scope) {
    scope.types.insert("Int".into(), Symbol::Int);
    scope.types.insert("Float".into(), Symbol::Float);
    scope.types.insert("Bool".into(), Symbol::Bool);
    scope.types.insert("Void".into(), Symbol::Void);
    scope.types.insert("Never".into(), Symbol::Never);
    scope.types.insert("RawPtr".into(), Symbol::RawPtr);
    scope.types.insert("__IR".into(), Symbol::IR);
    scope.types.insert("Byte".into(), Symbol::Byte);
    scope.types.insert("yield".into(), Symbol::YIELD);
}
