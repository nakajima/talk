use std::collections::HashMap;

use crate::{
    SymbolID, SymbolInfo, SymbolKind, SymbolTable,
    environment::{StructDef, TypeDef, TypeParams},
    name::Name,
    type_checker::{Scheme, TypeVarID, TypeVarKind},
};

use super::type_checker::Ty;

struct Builtin {
    id: i32,
    info: SymbolInfo,
    ty: Ty,
    unbound_vars: Vec<TypeVarID>,
    type_def: Option<TypeDef>,
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
            type_def: None,
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
            type_def: None,
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
            type_def: None,
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
            type_def: Some(TypeDef::Struct(StructDef::new(
                SymbolID(-4),
                Some(array_override),
                vec![Ty::TypeVar(TypeVarID(-4, TypeVarKind::Element))],
                Default::default(),
                Default::default(),
            ))),
        },
        Builtin {
            id: -5,
            info: SymbolInfo {
                name: "__init_array".into(),
                kind: SymbolKind::BuiltinFunc,
                expr_id: -5,
                is_captured: false,
            },
            ty: Ty::Func(
                vec![Ty::Int /* capacity */],
                Ty::Array(Box::new(Ty::TypeVar(TypeVarID(-4, TypeVarKind::Element)))).into(),
                vec![Ty::TypeVar(TypeVarID(-4, TypeVarKind::Element))],
            ),
            unbound_vars: vec![TypeVarID(-4, TypeVarKind::Element)],
            type_def: None,
        },
    ]
}
fn array_override(generics: &TypeParams) -> Ty {
    Ty::Array(Box::new(generics[0].clone()))
}

pub fn default_env_types() -> HashMap<SymbolID, TypeDef> {
    let mut result = HashMap::default();
    for builtin in builtins() {
        if let Some(def) = builtin.type_def {
            result.insert(SymbolID(builtin.id), def);
        }
    }
    result
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
    for builtin in builtins() {
        match name {
            Name::Resolved(id, _) => {
                if *id == SymbolID(builtin.id) {
                    return Some(builtin.ty);
                }
            }
            Name::Raw(name_str) => {
                if &builtin.info.name == name_str {
                    return Some(builtin.ty);
                }
            }
            _ => todo!(),
        }
    }

    None
}

pub fn is_builtin_func(symbol_id: &SymbolID) -> bool {
    for builtin in builtins() {
        if SymbolID(builtin.id) == *symbol_id {
            return true;
        }
    }

    false
}

#[cfg(test)]
mod tests {
    use crate::{check, type_checker::Ty};

    #[test]
    fn checks_init_array() {
        let checked = check(
            "
        __init_array<Int>(8)
        ",
        )
        .unwrap();

        assert_eq!(
            checked.type_for(checked.root_ids()[0]),
            Ty::Array(Ty::Int.into())
        );
    }
}
