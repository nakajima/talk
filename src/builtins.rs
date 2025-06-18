use std::collections::HashMap;

use crate::{
    SymbolID, SymbolInfo, SymbolKind, SymbolTable,
    environment::TypeDef,
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
                definition: None,
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
                definition: None,
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
                definition: None,
            },
            ty: Ty::Bool,
            unbound_vars: vec![],
            type_def: None,
        },
        Builtin {
            id: -4,
            info: SymbolInfo {
                name: "Pointer".into(),
                kind: SymbolKind::BuiltinType,
                expr_id: -4,
                is_captured: false,
                definition: None,
            },
            ty: Ty::Pointer,
            unbound_vars: vec![],
            type_def: None,
        },
        // Builtin {
        //     id: -4,
        //     info: SymbolInfo {
        //         name: "Array".into(),
        //         kind: SymbolKind::BuiltinType,
        //         expr_id: -4,
        //         is_captured: false,
        //         definition: None,
        //     },
        //     ty: Ty::Array(Box::new(Ty::TypeVar(TypeVarID(-4, TypeVarKind::Element)))),
        //     unbound_vars: vec![TypeVarID(-4, TypeVarKind::Element)],
        //     type_def: Some(TypeDef::Struct(StructDef::new(
        //         SymbolID(-4),
        //         "Array".to_string(),
        //         Some(array_override),
        //         vec![Ty::TypeVar(TypeVarID(-4, TypeVarKind::Element))],
        //         Default::default(),
        //         Default::default(),
        //         Default::default(),
        //     ))),
        // },
        Builtin {
            id: -5,
            info: SymbolInfo {
                name: "__alloc".into(),
                kind: SymbolKind::BuiltinFunc,
                expr_id: -5,
                is_captured: false,
                definition: None,
            },
            ty: Ty::Func(
                vec![Ty::Int /* capacity */],
                Ty::Pointer.into(),
                vec![Ty::TypeVar(TypeVarID(-4, TypeVarKind::Element))],
            ),
            unbound_vars: vec![TypeVarID(-4, TypeVarKind::Element)],
            type_def: None,
        },
        Builtin {
            id: -6,
            info: SymbolInfo {
                name: "__realloc".into(),
                kind: SymbolKind::BuiltinFunc,
                expr_id: -6,
                is_captured: false,
                definition: None,
            },
            ty: Ty::Func(
                vec![Ty::Pointer, Ty::Int],
                Ty::Pointer.into(),
                vec![Ty::TypeVar(TypeVarID(-4, TypeVarKind::Element))],
            ),
            unbound_vars: vec![TypeVarID(-4, TypeVarKind::Element)],
            type_def: None,
        },
        Builtin {
            id: -7,
            info: SymbolInfo {
                name: "__free".into(),
                kind: SymbolKind::BuiltinFunc,
                expr_id: -7,
                is_captured: false,
                definition: None,
            },
            ty: Ty::Func(vec![Ty::Pointer], Ty::Void.into(), vec![]),
            unbound_vars: vec![],
            type_def: None,
        },
        Builtin {
            id: -8,
            info: SymbolInfo {
                name: "__store".into(),
                kind: SymbolKind::BuiltinFunc,
                expr_id: -8,
                is_captured: false,
                definition: None,
            },
            ty: Ty::Func(
                vec![
                    Ty::Pointer,
                    Ty::Int,
                    Ty::TypeVar(TypeVarID(-8, TypeVarKind::Element)),
                ],
                Ty::Void.into(),
                vec![Ty::TypeVar(TypeVarID(-4, TypeVarKind::Element))],
            ),
            unbound_vars: vec![TypeVarID(-4, TypeVarKind::Element)],
            type_def: None,
        },
        Builtin {
            id: -9,
            info: SymbolInfo {
                name: "__load".into(),
                kind: SymbolKind::BuiltinFunc,
                expr_id: -9,
                is_captured: false,
                definition: None,
            },
            ty: Ty::Func(
                vec![Ty::Pointer, Ty::Int],
                Ty::TypeVar(TypeVarID(-9, TypeVarKind::Element)).into(),
                vec![Ty::TypeVar(TypeVarID(-9, TypeVarKind::Element))],
            ),
            unbound_vars: vec![TypeVarID(-9, TypeVarKind::Element)],
            type_def: None,
        },
    ]
}

// fn array_override(generics: &TypeParams) -> Ty {
//     Ty::Array(Box::new(generics[0].clone()))
// }

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
    fn checks_alloc() {
        let checked = check(
            "
        __alloc<Int>(8)
        ",
        )
        .unwrap();

        assert!(checked.diagnostics().is_empty());
        assert_eq!(
            checked.type_for(checked.root_ids()[0]).unwrap(),
            Ty::Pointer
        );
    }

    #[test]
    fn checks_realloc() {
        let checked = check(
            "
        let ptr = __alloc<Int>(1)
        __realloc<Int>(ptr, 10)
        ",
        )
        .unwrap();

        assert!(checked.diagnostics().is_empty());
        assert_eq!(
            checked.type_for(checked.root_ids()[1]).unwrap(),
            Ty::Pointer
        );
    }

    #[test]
    fn checks_store() {
        let checked = check(
            "
        let ptr = __alloc<Int>(10)
        __store<Int>(ptr, 0, 4)
        ",
        )
        .unwrap();

        assert!(checked.diagnostics().is_empty());
        assert_eq!(checked.type_for(checked.root_ids()[1]).unwrap(), Ty::Void);
    }

    #[test]
    fn checks_load() {
        let checked = check(
            "
        let ptr = __alloc<Int>(10)
        __store<Int>(ptr, 0, 4)
        ",
        )
        .unwrap();

        assert!(checked.diagnostics().is_empty());
        assert_eq!(checked.type_for(checked.root_ids()[1]), Some(Ty::Void));
    }
}
