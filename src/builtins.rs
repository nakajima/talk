use std::collections::BTreeMap;

use crate::{
    SymbolID, SymbolInfo, SymbolKind, SymbolTable,
    name::Name,
    parsing::node_id::NodeID,
    ty::Ty2,
    type_checker::Scheme,
    type_def::{TypeDef, TypeDefKind},
    type_var_id::{TypeVarID, TypeVarKind},
    types::ty::Ty,
};

pub struct Builtin {
    id: i32,
    info: SymbolInfo,
    pub ty2: Ty2,
    pub ty: Ty,
    pub unbound_vars: Vec<TypeVarID>,
    type_def: Option<TypeDef>,
}

pub fn builtins() -> Vec<Builtin> {
    vec![
        Builtin {
            id: -1,
            info: SymbolInfo {
                name: "Int".to_string(),
                kind: SymbolKind::BuiltinType,
                expr_id: NodeID(-1),
                is_captured: false,
                definition: None,
                documentation: None,
            },
            ty: Ty::Int,
            ty2: Ty2::Int,
            unbound_vars: vec![],
            type_def: Some(TypeDef::new(
                SymbolID(-1),
                "Int".to_string(),
                TypeDefKind::Builtin(Ty2::Int),
                vec![],
            )),
        },
        Builtin {
            id: -2,
            info: SymbolInfo {
                name: "Float".into(),
                kind: SymbolKind::BuiltinType,
                expr_id: NodeID(-2),
                is_captured: false,
                definition: None,
                documentation: None,
            },
            ty: Ty::Float,
            ty2: Ty2::Float,
            unbound_vars: vec![],
            type_def: Some(TypeDef::new(
                SymbolID(-2),
                "Float".to_string(),
                TypeDefKind::Builtin(Ty2::Float),
                vec![],
            )),
        },
        Builtin {
            id: -3,
            info: SymbolInfo {
                name: "Bool".into(),
                kind: SymbolKind::BuiltinType,
                expr_id: NodeID(-3),
                is_captured: false,
                definition: None,
                documentation: None,
            },
            ty: Ty::Bool,
            ty2: Ty2::Bool,
            unbound_vars: vec![],
            type_def: Some(TypeDef::new(
                SymbolID(-3),
                "Bool".to_string(),
                TypeDefKind::Builtin(Ty2::Bool),
                vec![],
            )),
        },
        Builtin {
            id: -4,
            info: SymbolInfo {
                name: "Pointer".into(),
                kind: SymbolKind::BuiltinType,
                expr_id: NodeID(-4),
                is_captured: false,
                definition: None,
                documentation: None,
            },
            ty: Ty::Pointer,
            ty2: Ty2::Pointer,
            unbound_vars: vec![],
            type_def: Some(TypeDef::new(
                SymbolID(-4),
                "Pointer".to_string(),
                TypeDefKind::Builtin(Ty2::Pointer),
                vec![],
            )),
        },
        Builtin {
            id: -5,
            info: SymbolInfo {
                name: "__alloc".into(),
                kind: SymbolKind::BuiltinFunc,
                expr_id: NodeID(-5),
                is_captured: false,
                definition: None,
                documentation: None,
            },
            ty: Ty::Int,
            ty2: Ty2::Func(
                vec![Ty2::Int /* capacity */],
                Ty2::Pointer.into(),
                vec![Ty2::TypeVar(TypeVarID {
                    id: 0,
                    kind: TypeVarKind::Element,
                    expr_id: NodeID(-5),
                })],
            ),
            unbound_vars: vec![TypeVarID {
                id: 0,
                kind: TypeVarKind::Element,
                expr_id: NodeID(-5),
            }],
            type_def: None,
        },
        Builtin {
            id: -6,
            info: SymbolInfo {
                name: "__realloc".into(),
                kind: SymbolKind::BuiltinFunc,
                expr_id: NodeID(-6),
                is_captured: false,
                definition: None,
                documentation: None,
            },
            ty: Ty::Int,
            ty2: Ty2::Func(
                vec![Ty2::Pointer, Ty2::Int],
                Ty2::Pointer.into(),
                vec![Ty2::TypeVar(TypeVarID {
                    id: 1,
                    kind: TypeVarKind::Element,
                    expr_id: NodeID(-6),
                })],
            ),
            unbound_vars: vec![TypeVarID {
                id: 1,
                kind: TypeVarKind::Element,
                expr_id: NodeID(-6),
            }],
            type_def: None,
        },
        Builtin {
            id: -7,
            info: SymbolInfo {
                name: "__free".into(),
                kind: SymbolKind::BuiltinFunc,
                expr_id: NodeID(-7),
                is_captured: false,
                definition: None,
                documentation: None,
            },
            ty: Ty::Int,
            ty2: Ty2::Func(vec![Ty2::Pointer], Ty2::Void.into(), vec![]),
            unbound_vars: vec![],
            type_def: None,
        },
        Builtin {
            id: -8,
            info: SymbolInfo {
                name: "__store".into(),
                kind: SymbolKind::BuiltinFunc,
                expr_id: NodeID(-8),
                is_captured: false,
                definition: None,
                documentation: None,
            },
            ty: Ty::Int,
            ty2: Ty2::Func(
                vec![
                    Ty2::Pointer,
                    Ty2::Int,
                    Ty2::TypeVar(TypeVarID {
                        id: 2,
                        kind: TypeVarKind::Element,
                        expr_id: NodeID(-8),
                    }),
                ],
                Ty2::Void.into(),
                vec![Ty2::TypeVar(TypeVarID {
                    id: 2,
                    kind: TypeVarKind::Element,
                    expr_id: NodeID(-8),
                })],
            ),
            unbound_vars: vec![TypeVarID {
                id: 2,
                kind: TypeVarKind::Element,
                expr_id: NodeID(-8),
            }],
            type_def: None,
        },
        Builtin {
            id: -9,
            info: SymbolInfo {
                name: "__load".into(),
                kind: SymbolKind::BuiltinFunc,
                expr_id: NodeID(-9),
                is_captured: false,
                definition: None,
                documentation: None,
            },
            ty: Ty::Int,
            ty2: Ty2::Func(
                vec![Ty2::Pointer, Ty2::Int],
                Ty2::TypeVar(TypeVarID {
                    id: 3,
                    kind: TypeVarKind::Element,
                    expr_id: NodeID(-9),
                })
                .into(),
                vec![Ty2::TypeVar(TypeVarID {
                    id: 3,
                    kind: TypeVarKind::Element,
                    expr_id: NodeID(-9),
                })],
            ),
            unbound_vars: vec![TypeVarID {
                id: 3,
                kind: TypeVarKind::Element,
                expr_id: NodeID(-9),
            }],
            type_def: None,
        },
        // Reserve -10 for tuple symbol
        Builtin {
            id: -11,
            info: SymbolInfo {
                name: "print".into(),
                kind: SymbolKind::BuiltinFunc,
                expr_id: NodeID(-11),
                is_captured: false,
                definition: None,
                documentation: None,
            },
            ty: Ty::Int,
            ty2: Ty2::Func(
                vec![Ty2::TypeVar(TypeVarID {
                    id: 4,
                    kind: TypeVarKind::FuncParam("printable".into()),
                    expr_id: NodeID(-11),
                })],
                Ty2::Void.into(),
                vec![Ty2::TypeVar(TypeVarID {
                    id: 4,
                    kind: TypeVarKind::FuncParam("printable".into()),
                    expr_id: NodeID(-11),
                })],
            ),
            unbound_vars: vec![TypeVarID {
                id: 4,
                kind: TypeVarKind::FuncParam("printable".into()),
                expr_id: NodeID(-11),
            }],
            type_def: None,
        },
        Builtin {
            id: -12,
            info: SymbolInfo {
                name: "__ir_instr".into(),
                kind: SymbolKind::BuiltinFunc,
                expr_id: NodeID(-12),
                is_captured: false,
                definition: None,
                documentation: None,
            },
            ty: Ty::Int,
            ty2: Ty2::Func(
                vec![Ty2::string()],
                Ty2::TypeVar(TypeVarID {
                    id: 5,
                    kind: TypeVarKind::CallReturn,
                    expr_id: NodeID(-12),
                })
                .into(),
                vec![Ty2::TypeVar(TypeVarID {
                    id: 5,
                    kind: TypeVarKind::CallReturn,
                    expr_id: NodeID(-12),
                })],
            ),
            unbound_vars: vec![TypeVarID {
                id: 5,
                kind: TypeVarKind::CallReturn,
                expr_id: NodeID(-12),
            }],
            type_def: None,
        },
        Builtin {
            id: -13,
            info: SymbolInfo {
                name: "Byte".into(),
                kind: SymbolKind::BuiltinType,
                expr_id: NodeID(-13),
                is_captured: false,
                definition: None,
                documentation: None,
            },
            ty: Ty::Byte,
            ty2: Ty2::Byte,
            unbound_vars: vec![],
            type_def: Some(TypeDef::new(
                SymbolID(-13),
                "Byte".to_string(),
                TypeDefKind::Builtin(Ty2::Byte),
                vec![],
            )),
        },
    ]
}

pub fn builtin_type(symbol_id: &SymbolID) -> Option<Ty2> {
    for builtin in builtins() {
        if symbol_id == &SymbolID(builtin.id) {
            return Some(builtin.ty2);
        }
    }

    None
}

pub fn builtin_type_def(symbol_id: &SymbolID) -> Option<TypeDef> {
    for builtin in builtins() {
        if symbol_id == &SymbolID(builtin.id) {
            #[allow(clippy::expect_used)]
            return builtin.type_def;
        }
    }

    None
}

pub fn default_env_types() -> BTreeMap<SymbolID, TypeDef> {
    let mut result = BTreeMap::default();
    for builtin in builtins() {
        if let Some(def) = builtin.type_def {
            result.insert(SymbolID(builtin.id), def);
        }
    }
    result
}

pub fn default_env_scope() -> BTreeMap<SymbolID, Scheme> {
    let mut scope = BTreeMap::new();
    for builtin in builtins() {
        scope.insert(
            SymbolID(builtin.id),
            Scheme::new(builtin.ty2, builtin.unbound_vars, vec![]),
        );
    }
    scope
}

pub fn default_type_checker_scope() -> BTreeMap<SymbolID, Ty> {
    let mut scope = BTreeMap::new();
    for builtin in builtins() {
        scope.insert(SymbolID(builtin.id), builtin.ty);
    }
    scope
}

pub fn default_name_scope() -> BTreeMap<String, SymbolID> {
    let mut scope = BTreeMap::new();
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

pub fn match_builtin(name: &Name) -> Option<Ty2> {
    for builtin in builtins() {
        match name {
            Name::Resolved(id, _) => {
                if *id == SymbolID(builtin.id) {
                    return Some(builtin.ty2);
                }
            }
            Name::Raw(name_str) => {
                if &builtin.info.name == name_str {
                    return Some(builtin.ty2);
                }
            }
            _ => return None,
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
#[allow(clippy::unwrap_used)]
mod tests {
    use crate::{check, ty::Ty2};

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
            Ty2::Pointer
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
            Ty2::Pointer
        );
    }

    #[test]
    fn checks_store() {
        let checked = check(
            "
        let ptr = __alloc<Int>(10)
        __store<Int>(ptr, 4, 123)
        ",
        )
        .unwrap();

        assert!(
            checked.diagnostics().is_empty(),
            "{:#?}",
            checked.diagnostics()
        );
        assert_eq!(checked.type_for(checked.root_ids()[1]).unwrap(), Ty2::Void);
    }

    #[test]
    fn checks_load() {
        let checked = check(
            "
        let ptr = __alloc<Int>(10)
        __load<Int>(ptr, 1)
        ",
        )
        .unwrap();

        assert!(checked.diagnostics().is_empty());
        assert_eq!(checked.type_for(checked.root_ids()[1]), Some(Ty2::Int));
    }
}

#[cfg(test)]
mod optional_tests {
    use crate::{
        any_expr,
        parsed_node::{self, ParsedNode},
        parser::parse,
    };

    #[test]
    fn gets_parsed() {
        let parsed = parse("let a: Int?", "-");

        assert_eq!(
            parsed.roots()[0],
            any_expr!(parsed_node::Expr::Let(
                "a".into(),
                Some(
                    any_expr!(parsed_node::Expr::TypeRepr {
                        name: "Optional".into(),
                        generics: vec![any_expr!(parsed_node::Expr::TypeRepr {
                            name: "Int".into(),
                            generics: vec![],
                            conformances: vec![],
                            introduces_type: false
                        })],
                        conformances: vec![],
                        introduces_type: false
                    })
                    .into()
                )
            ))
        );
    }
}

// #[cfg(test)]
// mod array_tests {
//     use crate::{SymbolID, compiling::driver::Driver, ty::Ty2};

//     #[test]
//     fn gets_typed() {
//         let checked = crate::type_checking::check("[1,2,3]").unwrap();
//         assert_eq!(
//             checked.type_for(checked.root_ids()[0]).unwrap(),
//             Ty2::struct_type(SymbolID::ARRAY, vec![Ty2::Int])
//         );
//     }

//     #[test]
//     fn gets_typed_get() {
//         let checked = crate::type_checking::check("[1,2,3].get(0)").unwrap();
//         assert_eq!(checked.type_for(checked.root_ids()[0]).unwrap(), Ty2::Int);
//     }

//     #[test]
//     fn gets_count() {
//         let checked = crate::type_checking::check("[1,2,3].count").unwrap();
//         assert_eq!(checked.type_for(checked.root_ids()[0]).unwrap(), Ty2::Int);
//     }

//     #[test]
//     fn lowers_literal() {
//         let mut driver = Driver::with_str("[1,2,3].count");
//         let module = driver.lower().into_iter().next().unwrap().module();

//         crate::assert_lowered_function!(
//             module,
//             "@main",
//             IRFunction {
//                 debug_info: Default::default(),
//                 ty: IRType::Func(vec![], IRType::Void.into()).clone(),
//                 name: "@main".into(),
//                 blocks: vec![BasicBlock {
//                     id: BasicBlockID(0),
//                     instructions: vec![
//                         Instr::Alloc {
//                             dest: Register(0),
//                             ty: IRType::array(IRType::Int),
//                             count: None
//                         },
//                         // Set the array's count
//                         Instr::ConstantInt(Register(1), 3),
//                         Instr::GetElementPointer {
//                             dest: Register(2),
//                             base: Register(0),
//                             ty: IRType::array(IRType::Int),
//                             index: 0.into(),
//                         },
//                         Instr::Store {
//                             location: Register(2),
//                             ty: IRType::Int,
//                             val: Register(1).into()
//                         },
//                         // Set the array's capacity
//                         Instr::ConstantInt(Register(3), 3),
//                         Instr::GetElementPointer {
//                             dest: Register(4),
//                             base: Register(0),
//                             ty: IRType::array(IRType::Int),
//                             index: 1.into(),
//                         },
//                         Instr::Store {
//                             location: Register(4),
//                             ty: IRType::Int,
//                             val: Register(3).into()
//                         },
//                         // Get array's storage pointer
//                         Instr::GetElementPointer {
//                             dest: Register(5),
//                             base: Register(0),
//                             ty: IRType::array(IRType::Int),
//                             index: 2.into(),
//                         },
//                         // Alloc space for the items
//                         Instr::Alloc {
//                             dest: Register(6),
//                             ty: IRType::Int,
//                             count: Some(IRValue::Register(Register(1)))
//                         },
//                         Instr::Store {
//                             ty: IRType::POINTER,
//                             val: Register(6).into(),
//                             location: Register(5)
//                         },
//                         // Store first element
//                         Instr::ConstantInt(Register(7), 1),
//                         Instr::GetElementPointer {
//                             dest: Register(8),
//                             base: Register(6),
//                             ty: IRType::TypedBuffer {
//                                 element: IRType::Int.into()
//                             },
//                             index: 0.into(),
//                         },
//                         Instr::Store {
//                             ty: IRType::Int,
//                             val: Register(7).into(),
//                             location: Register(8)
//                         },
//                         // Store second element
//                         Instr::ConstantInt(Register(9), 2),
//                         Instr::GetElementPointer {
//                             dest: Register(10),
//                             base: Register(6),
//                             ty: IRType::TypedBuffer {
//                                 element: IRType::Int.into()
//                             },
//                             index: 1.into(),
//                         },
//                         Instr::Store {
//                             ty: IRType::Int,
//                             val: Register(9).into(),
//                             location: Register(10)
//                         },
//                         // Store third element
//                         Instr::ConstantInt(Register(11), 3),
//                         Instr::GetElementPointer {
//                             dest: Register(12),
//                             base: Register(6),
//                             ty: IRType::TypedBuffer {
//                                 element: IRType::Int.into()
//                             },
//                             index: 2.into(),
//                         },
//                         Instr::Store {
//                             ty: IRType::Int,
//                             val: Register(11).into(),
//                             location: Register(12)
//                         },
//                         // Instr::Load {
//                         //     dest: Register(13),
//                         //     ty: IRType::array(),
//                         //     addr: Register(0),
//                         // },
//                         // Get .count
//                         Instr::GetElementPointer {
//                             dest: Register(13),
//                             base: Register(0),
//                             ty: IRType::array(IRType::Int),
//                             index: 0.into(),
//                         },
//                         Instr::Load {
//                             dest: Register(14),
//                             ty: IRType::Int,
//                             addr: Register(13)
//                         },
//                         Instr::Ret(IRType::Int, Some(Register(14).into()))
//                     ],
//                 }],
//                 env_ty: None,
//                 env_reg: None,
//                 size: 15
//             }
//         );
//     }
// }

// #[cfg(test)]
// mod stdlib_tests {
//     use crate::{
//         assert_lowered_function,
//         compiling::driver::Driver,
//         lowering::{
//             instr::Instr,
//             ir_function::IRFunction,
//             ir_type::IRType,
//             ir_value::IRValue,
//             lowerer::{BasicBlock, BasicBlockID},
//             register::Register,
//         },
//     };

//     #[test]
//     fn lowers_alloc() {
//         let mut driver = Driver::with_str("__alloc<Int>(4)");
//         let lowered = driver.lower().into_iter().next().unwrap().module();
//         assert_lowered_function!(
//             lowered,
//             "@main",
//             IRFunction {
//                 debug_info: Default::default(),
//                 ty: IRType::Func(vec![], IRType::Void.into()),
//                 name: "@main".into(),
//                 blocks: vec![BasicBlock {
//                     id: BasicBlockID(0),
//                     instructions: vec![
//                         Instr::ConstantInt(Register(0), 4),
//                         Instr::Alloc {
//                             dest: Register(1),
//                             ty: IRType::Int,
//                             count: Some(IRValue::Register(Register(0))),
//                         },
//                         Instr::Ret(IRType::POINTER, Some(Register(1).into()))
//                     ],
//                 }],
//                 env_ty: None,
//                 env_reg: None,
//                 size: 2,
//             }
//         );
//     }

//     #[test]
//     fn lowers_store() {
//         let mut driver = Driver::with_str(
//             "
//         let ptr = __alloc<Int>(2)
//         __store<Int>(ptr, 1, 123)
//         ",
//         );
//         let lowered = driver.lower().into_iter().next().unwrap().module();
//         assert_lowered_function!(
//             lowered,
//             "@main",
//             IRFunction {
//                 debug_info: Default::default(),
//                 ty: IRType::Func(vec![], IRType::Void.into()),
//                 name: "@main".into(),
//                 blocks: vec![BasicBlock {
//                     id: BasicBlockID(0),
//                     instructions: vec![
//                         // First alloc (so we can get a pointer)
//                         Instr::ConstantInt(Register(0), 2),
//                         Instr::Alloc {
//                             dest: Register(1),
//                             ty: IRType::Int,
//                             count: Some(IRValue::Register(Register(0))),
//                         },
//                         Instr::ConstantInt(Register(2), 1),
//                         Instr::ConstantInt(Register(3), 123),
//                         Instr::GetElementPointer {
//                             dest: Register(4),
//                             base: Register(1),
//                             ty: IRType::TypedBuffer {
//                                 element: IRType::Int.into()
//                             },
//                             index: Register(2).into(),
//                         },
//                         Instr::Store {
//                             val: Register(3).into(),
//                             ty: IRType::Int,
//                             location: Register(4)
//                         },
//                         Instr::Ret(IRType::Void, None)
//                     ],
//                 }],
//                 env_ty: None,
//                 env_reg: None,
//                 size: 5,
//             }
//         );
//     }

//     #[test]
//     fn lowers_load() {
//         let mut driver = Driver::with_str(
//             "
//         let ptr = __alloc<Int>(2)
//         __load<Int>(ptr, 1)
//         ",
//         );
//         let lowered = driver.lower().into_iter().next().unwrap().module();
//         assert_lowered_function!(
//             lowered,
//             "@main",
//             IRFunction {
//                 debug_info: Default::default(),
//                 ty: IRType::Func(vec![], IRType::Void.into()),
//                 name: "@main".into(),
//                 blocks: vec![BasicBlock {
//                     id: BasicBlockID(0),
//                     instructions: vec![
//                         // First alloc (so we can get a pointer)
//                         Instr::ConstantInt(Register(0), 2),
//                         Instr::Alloc {
//                             dest: Register(1),
//                             ty: IRType::Int,
//                             count: Some(IRValue::Register(Register(0))),
//                         },
//                         Instr::ConstantInt(Register(2), 1),
//                         Instr::GetElementPointer {
//                             dest: Register(4),
//                             base: Register(1),
//                             ty: IRType::TypedBuffer {
//                                 element: IRType::Int.into()
//                             },
//                             index: Register(2).into()
//                         },
//                         Instr::Load {
//                             dest: Register(3),
//                             ty: IRType::Int,
//                             addr: Register(4)
//                         },
//                         Instr::Ret(IRType::Int, Some(Register(3).into()))
//                     ],
//                 }],
//                 env_ty: None,
//                 env_reg: None,
//                 size: 5
//             },
//         );
//     }

//     #[test]
//     fn lowers_ir_instr() {
//         let mut driver = Driver::with_str(
//             "
//         let x = 1
//         let y = 2
//         __ir_instr<Int>(\"$? = add int %0, %1;\")
//         ",
//         );
//         let lowered = driver.lower().into_iter().next().unwrap().module();
//         assert_lowered_function!(
//             lowered,
//             "@main",
//             IRFunction {
//                 debug_info: Default::default(),
//                 ty: IRType::Func(vec![], IRType::Void.into()),
//                 name: "@main".into(),
//                 blocks: vec![BasicBlock {
//                     id: BasicBlockID(0),
//                     instructions: vec![
//                         Instr::ConstantInt(Register(0), 1),
//                         Instr::ConstantInt(Register(1), 2),
//                         Instr::Add(Register(2), IRType::Int, Register(0), Register(1)),
//                         Instr::Ret(IRType::Int, Some(Register(2).into()))
//                     ],
//                 }],
//                 env_ty: None,
//                 env_reg: None,
//                 size: 3
//             },
//         );
//     }
// }
