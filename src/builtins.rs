use std::collections::HashMap;

use crate::{
    SymbolID, SymbolInfo, SymbolKind, SymbolTable,
    name::Name,
    type_checker::{Scheme, TypeVarID, TypeVarKind},
};

use super::type_checker::Ty;

struct Builtin {
    id: i32,
    info: SymbolInfo,
    ty: Ty,
    unbound_vars: Vec<TypeVarID>,
}

fn builtins() -> Vec<Builtin> {
    vec![
        Builtin {
            id: -1,
            info: SymbolInfo {
                name: "Int".to_string(),
                kind: SymbolKind::BuiltinType,
                expr_id: -1,
                is_captured: false,
            },
            ty: Ty::Int,
            unbound_vars: vec![],
        },
        Builtin {
            id: -2,
            info: SymbolInfo {
                name: "Float".into(),
                kind: SymbolKind::BuiltinType,
                expr_id: -2,
                is_captured: false,
            },
            ty: Ty::Float,
            unbound_vars: vec![],
        },
        Builtin {
            id: -3,
            info: SymbolInfo {
                name: "Bool".into(),
                kind: SymbolKind::BuiltinType,
                expr_id: -3,
                is_captured: false,
            },
            ty: Ty::Bool,
            unbound_vars: vec![],
        },
        Builtin {
            id: -4,
            info: SymbolInfo {
                name: "Array".into(),
                kind: SymbolKind::BuiltinType,
                expr_id: -4,
                is_captured: false,
            },
            ty: Ty::Array(Box::new(Ty::TypeVar(TypeVarID(-4, TypeVarKind::Element)))),
            unbound_vars: vec![TypeVarID(-4, TypeVarKind::Element)],
        },
    ]
}

pub fn default_env_scope() -> HashMap<SymbolID, Scheme> {
    let mut scope = HashMap::new();
    for builtin in builtins() {
        scope.insert(
            SymbolID(builtin.id),
            Scheme::new(builtin.ty, builtin.unbound_vars),
        );
    }
    scope
}

pub fn default_name_scope() -> HashMap<String, SymbolID> {
    let mut scope = HashMap::new();
    for builtin in builtins() {
        scope.insert(builtin.info.name, SymbolID(builtin.id));
    }
    scope
}

pub fn import_symbols(symbol_table: &mut SymbolTable) {
    for builtin in builtins() {
        symbol_table.import(&SymbolID(builtin.id), builtin.info.clone());
    }
}

pub fn match_builtin(name: &Name) -> Option<Ty> {
    let Name::Resolved(id, _) = name else {
        return None;
    };
    for builtin in builtins() {
        if SymbolID(builtin.id) == *id {
            return Some(builtin.ty);
        }
    }

    None
}
