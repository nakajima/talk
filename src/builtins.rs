use std::collections::BTreeMap;

use crate::{
    SymbolID, SymbolInfo, SymbolKind, SymbolTable,
    name::Name,
    ty::Ty,
    type_checker::Scheme,
    type_defs::{TypeDef, builtin_def::BuiltinDef},
    type_var_id::{TypeVarID, TypeVarKind},
};

pub struct Builtin {
    id: i32,
    info: SymbolInfo,
    pub ty: Ty,
    unbound_vars: Vec<TypeVarID>,
    type_def: Option<TypeDef>,
}

pub fn builtins() -> Vec<Builtin> {
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
            type_def: Some(TypeDef::Builtin(BuiltinDef {
                symbol_id: SymbolID(-1),
                name_str: "Int".to_string(),
                methods: vec![],
                conformances: vec![],
                ty: Ty::Int,
            })),
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
            type_def: Some(TypeDef::Builtin(BuiltinDef {
                symbol_id: SymbolID(-2),
                name_str: "Float".to_string(),
                methods: vec![],
                conformances: vec![],
                ty: Ty::Float,
            })),
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
            type_def: Some(TypeDef::Builtin(BuiltinDef {
                symbol_id: SymbolID(-3),
                name_str: "Bool".to_string(),
                methods: vec![],
                conformances: vec![],
                ty: Ty::Bool,
            })),
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
            type_def: Some(TypeDef::Builtin(BuiltinDef {
                symbol_id: SymbolID(-4),
                name_str: "Pointer".to_string(),
                methods: vec![],
                conformances: vec![],
                ty: Ty::Pointer,
            })),
        },
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
                vec![Ty::TypeVar(TypeVarID {
                    id: u32::MAX - 5,
                    kind: TypeVarKind::Element,
                })],
            ),
            unbound_vars: vec![TypeVarID {
                id: u32::MAX - 5,
                kind: TypeVarKind::Element,
            }],
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
                vec![Ty::TypeVar(TypeVarID {
                    id: u32::MAX - 4,
                    kind: TypeVarKind::Element,
                })],
            ),
            unbound_vars: vec![TypeVarID {
                id: u32::MAX - 4,
                kind: TypeVarKind::Element,
            }],
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
                    Ty::TypeVar(TypeVarID {
                        id: u32::MAX - 8,
                        kind: TypeVarKind::Element,
                    }),
                ],
                Ty::Void.into(),
                vec![Ty::TypeVar(TypeVarID {
                    id: u32::MAX - 8,
                    kind: TypeVarKind::Element,
                })],
            ),
            unbound_vars: vec![TypeVarID {
                id: u32::MAX - 8,
                kind: TypeVarKind::Element,
            }],
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
                Ty::TypeVar(TypeVarID {
                    id: u32::MAX - 9,
                    kind: TypeVarKind::Element,
                })
                .into(),
                vec![Ty::TypeVar(TypeVarID {
                    id: u32::MAX - 9,
                    kind: TypeVarKind::Element,
                })],
            ),
            unbound_vars: vec![TypeVarID {
                id: u32::MAX - 9,
                kind: TypeVarKind::Element,
            }],
            type_def: None,
        },
        // Reserve -10 for tuple symbol
        Builtin {
            id: -11,
            info: SymbolInfo {
                name: "print".into(),
                kind: SymbolKind::BuiltinFunc,
                expr_id: -11,
                is_captured: false,
                definition: None,
            },
            ty: Ty::Func(
                vec![Ty::TypeVar(TypeVarID {
                    id: u32::MAX - 11,
                    kind: TypeVarKind::FuncParam("printable".into()),
                })],
                Ty::Void.into(),
                vec![Ty::TypeVar(TypeVarID {
                    id: u32::MAX - 11,
                    kind: TypeVarKind::FuncParam("printable".into()),
                })],
            ),
            unbound_vars: vec![TypeVarID {
                id: u32::MAX - 11,
                kind: TypeVarKind::FuncParam("printable".into()),
            }],
            type_def: None,
        },
        Builtin {
            id: -12,
            info: SymbolInfo {
                name: "__ir_instr".into(),
                kind: SymbolKind::BuiltinFunc,
                expr_id: -12,
                is_captured: false,
                definition: None,
            },
            ty: Ty::Func(
                vec![Ty::string()],
                Ty::TypeVar(TypeVarID {
                    id: u32::MAX - 12,
                    kind: TypeVarKind::CallReturn,
                })
                .into(),
                vec![Ty::TypeVar(TypeVarID {
                    id: u32::MAX - 12,
                    kind: TypeVarKind::CallReturn,
                })],
            ),
            unbound_vars: vec![TypeVarID {
                id: u32::MAX - 12,
                kind: TypeVarKind::CallReturn,
            }],
            type_def: None,
        },
        Builtin {
            id: -13,
            info: SymbolInfo {
                name: "Byte".into(),
                kind: SymbolKind::BuiltinType,
                expr_id: -13,
                is_captured: false,
                definition: None,
            },
            ty: Ty::Byte,
            unbound_vars: vec![],
            type_def: None,
        },
    ]
}

pub fn builtin_type(symbol_id: &SymbolID) -> Option<Ty> {
    for builtin in builtins() {
        if symbol_id == &SymbolID(builtin.id) {
            return Some(builtin.ty);
        }
    }

    None
}

pub fn builtin_type_def(symbol_id: &SymbolID) -> TypeDef {
    for builtin in builtins() {
        if symbol_id == &SymbolID(builtin.id) {
            #[allow(clippy::expect_used)]
            return builtin.type_def.expect("No builtin type def found");
        }
    }

    unreachable!()
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
            Scheme::new(builtin.ty, builtin.unbound_vars),
        );
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
    use crate::{check, ty::Ty};

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
            checked.type_for(&checked.root_ids()[0]).unwrap(),
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
            checked.type_for(&checked.root_ids()[1]).unwrap(),
            Ty::Pointer
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
        assert_eq!(checked.type_for(&checked.root_ids()[1]).unwrap(), Ty::Void);
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
        assert_eq!(checked.type_for(&checked.root_ids()[1]), Some(Ty::Int));
    }
}

#[cfg(test)]
mod optional_tests {
    use crate::{expr::Expr, parser::parse};

    #[test]
    fn gets_parsed() {
        let parsed = parse("let a: Int?", "-".into());
        let Expr::Let(_, Some(ty)) = parsed.roots()[0].unwrap() else {
            panic!("didn't get let expr");
        };

        assert_eq!(
            *parsed.get(ty).unwrap(),
            Expr::TypeRepr {
                name: "Optional".into(),
                generics: vec![0],
                conformances: vec![],
                introduces_type: false
            }
        );

        assert_eq!(
            *parsed.get(&0).unwrap(),
            Expr::TypeRepr {
                name: "Int".into(),
                generics: vec![],
                conformances: vec![],
                introduces_type: false
            }
        );
    }
}

#[cfg(test)]
mod array_tests {
    use crate::{
        SymbolID,
        compiling::driver::Driver,
        expr::Expr,
        lowering::{
            instr::Instr,
            ir_function::IRFunction,
            ir_type::IRType,
            ir_value::IRValue,
            lowerer::{BasicBlock, BasicBlockID},
            register::Register,
        },
        parser::parse,
        ty::Ty,
    };

    #[test]
    fn gets_parsed() {
        let parsed = parse("[1,2,3]", "-".into());
        assert_eq!(
            *parsed.roots()[0].unwrap(),
            Expr::LiteralArray(vec![0, 1, 2])
        );

        assert_eq!(*parsed.get(&0).unwrap(), Expr::LiteralInt("1".into()));
        assert_eq!(*parsed.get(&1).unwrap(), Expr::LiteralInt("2".into()));
        assert_eq!(*parsed.get(&2).unwrap(), Expr::LiteralInt("3".into()));
    }

    #[test]
    fn gets_typed() {
        let checked = crate::type_checking::check("[1,2,3]").unwrap();
        assert_eq!(
            checked.type_for(&checked.root_ids()[0]).unwrap(),
            Ty::Struct(SymbolID::ARRAY, vec![Ty::Int])
        );
    }

    #[test]
    fn gets_count() {
        let checked = crate::type_checking::check("[1,2,3].count").unwrap();
        assert_eq!(checked.type_for(&checked.root_ids()[0]).unwrap(), Ty::Int);
    }

    #[test]
    fn lowers_literal() {
        let mut driver = Driver::with_str("[1,2,3].count");
        let module = driver.lower().into_iter().next().unwrap().module();

        crate::assert_lowered_function!(
            module,
            "@main",
            IRFunction {
                debug_info: Default::default(),
                ty: IRType::Func(vec![], IRType::Void.into()).clone(),
                name: "@main".into(),
                blocks: vec![BasicBlock {
                    id: BasicBlockID(0),
                    instructions: vec![
                        Instr::Alloc {
                            dest: Register(0),
                            ty: IRType::array(IRType::Int),
                            count: None
                        },
                        // Set the array's count
                        Instr::ConstantInt(Register(1), 3),
                        Instr::GetElementPointer {
                            dest: Register(2),
                            base: Register(0),
                            ty: IRType::array(IRType::Int),
                            index: 0.into(),
                        },
                        Instr::Store {
                            location: Register(2),
                            ty: IRType::Int,
                            val: Register(1).into()
                        },
                        // Set the array's capacity
                        Instr::ConstantInt(Register(3), 3),
                        Instr::GetElementPointer {
                            dest: Register(4),
                            base: Register(0),
                            ty: IRType::array(IRType::Int),
                            index: 1.into(),
                        },
                        Instr::Store {
                            location: Register(4),
                            ty: IRType::Int,
                            val: Register(3).into()
                        },
                        // Get array's storage pointer
                        Instr::GetElementPointer {
                            dest: Register(5),
                            base: Register(0),
                            ty: IRType::array(IRType::Int),
                            index: 2.into(),
                        },
                        // Alloc space for the items
                        Instr::Alloc {
                            dest: Register(6),
                            ty: IRType::Int,
                            count: Some(IRValue::Register(Register(1)))
                        },
                        Instr::Store {
                            ty: IRType::POINTER,
                            val: Register(6).into(),
                            location: Register(5)
                        },
                        // Store first element
                        Instr::ConstantInt(Register(7), 1),
                        Instr::GetElementPointer {
                            dest: Register(8),
                            base: Register(6),
                            ty: IRType::TypedBuffer {
                                element: IRType::Int.into()
                            },
                            index: 0.into(),
                        },
                        Instr::Store {
                            ty: IRType::Int,
                            val: Register(7).into(),
                            location: Register(8)
                        },
                        // Store second element
                        Instr::ConstantInt(Register(9), 2),
                        Instr::GetElementPointer {
                            dest: Register(10),
                            base: Register(6),
                            ty: IRType::TypedBuffer {
                                element: IRType::Int.into()
                            },
                            index: 1.into(),
                        },
                        Instr::Store {
                            ty: IRType::Int,
                            val: Register(9).into(),
                            location: Register(10)
                        },
                        // Store third element
                        Instr::ConstantInt(Register(11), 3),
                        Instr::GetElementPointer {
                            dest: Register(12),
                            base: Register(6),
                            ty: IRType::TypedBuffer {
                                element: IRType::Int.into()
                            },
                            index: 2.into(),
                        },
                        Instr::Store {
                            ty: IRType::Int,
                            val: Register(11).into(),
                            location: Register(12)
                        },
                        // Instr::Load {
                        //     dest: Register(13),
                        //     ty: IRType::array(),
                        //     addr: Register(0),
                        // },
                        // Get .count
                        Instr::GetElementPointer {
                            dest: Register(13),
                            base: Register(0),
                            ty: IRType::array(IRType::Int),
                            index: 0.into(),
                        },
                        Instr::Load {
                            dest: Register(14),
                            ty: IRType::Int,
                            addr: Register(13)
                        },
                        Instr::Ret(IRType::Int, Some(Register(14).into()))
                    ],
                }],
                env_ty: None,
                env_reg: None,
                size: 15
            }
        );
    }
}

#[cfg(test)]
mod stdlib_tests {
    use crate::{
        assert_lowered_function,
        compiling::driver::Driver,
        lowering::{
            instr::Instr,
            ir_function::IRFunction,
            ir_type::IRType,
            ir_value::IRValue,
            lowerer::{BasicBlock, BasicBlockID},
            register::Register,
        },
    };

    #[test]
    fn lowers_alloc() {
        let mut driver = Driver::with_str("__alloc<Int>(4)");
        let lowered = driver.lower().into_iter().next().unwrap().module();
        assert_lowered_function!(
            lowered,
            "@main",
            IRFunction {
                debug_info: Default::default(),
                ty: IRType::Func(vec![], IRType::Void.into()),
                name: "@main".into(),
                blocks: vec![BasicBlock {
                    id: BasicBlockID(0),
                    instructions: vec![
                        Instr::ConstantInt(Register(1), 4),
                        Instr::Alloc {
                            dest: Register(0),
                            ty: IRType::Int,
                            count: Some(IRValue::Register(Register(1))),
                        },
                        Instr::Ret(IRType::POINTER, Some(Register(0).into()))
                    ],
                }],
                env_ty: None,
                env_reg: None,
                size: 2,
            }
        );
    }

    #[test]
    fn lowers_realloc() {
        let mut driver = Driver::with_str(
            "
        let ptr = __alloc<Int>(2)
        __realloc<Int>(ptr, 4)
        ",
        );
        let lowered = driver.lower().into_iter().next().unwrap().module();
        assert_lowered_function!(
            lowered,
            "@main",
            IRFunction {
                debug_info: Default::default(),
                ty: IRType::Func(vec![], IRType::Void.into()),
                name: "@main".into(),
                blocks: vec![BasicBlock {
                    id: BasicBlockID(0),
                    instructions: vec![
                        // First alloc
                        Instr::ConstantInt(Register(1), 2),
                        Instr::Alloc {
                            dest: Register(0),
                            ty: IRType::Int,
                            count: Some(IRValue::Register(Register(1))),
                        },
                        // Realloc
                        Instr::ConstantInt(Register(3), 4),
                        Instr::Alloc {
                            dest: Register(2),
                            ty: IRType::Int,
                            count: Some(IRValue::Register(Register(3))),
                        },
                        Instr::Ret(IRType::POINTER, Some(Register(2).into()))
                    ],
                }],
                env_ty: None,
                env_reg: None,
                size: 4,
            },
        )
    }

    #[test]
    fn lowers_store() {
        let mut driver = Driver::with_str(
            "
        let ptr = __alloc<Int>(2)
        __store<Int>(ptr, 1, 123)
        ",
        );
        let lowered = driver.lower().into_iter().next().unwrap().module();
        assert_lowered_function!(
            lowered,
            "@main",
            IRFunction {
                debug_info: Default::default(),
                ty: IRType::Func(vec![], IRType::Void.into()),
                name: "@main".into(),
                blocks: vec![BasicBlock {
                    id: BasicBlockID(0),
                    instructions: vec![
                        // First alloc (so we can get a pointer)
                        Instr::ConstantInt(Register(1), 2),
                        Instr::Alloc {
                            dest: Register(0),
                            ty: IRType::Int,
                            count: Some(IRValue::Register(Register(1))),
                        },
                        Instr::ConstantInt(Register(2), 1),
                        Instr::ConstantInt(Register(3), 123),
                        Instr::GetElementPointer {
                            dest: Register(4),
                            base: Register(0),
                            ty: IRType::TypedBuffer {
                                element: IRType::Int.into()
                            },
                            index: Register(2).into(),
                        },
                        Instr::Store {
                            val: Register(3).into(),
                            ty: IRType::Int,
                            location: Register(4)
                        },
                        Instr::Ret(IRType::Void, None)
                    ],
                }],
                env_ty: None,
                env_reg: None,
                size: 5,
            }
        );
    }

    #[test]
    fn lowers_load() {
        let mut driver = Driver::with_str(
            "
        let ptr = __alloc<Int>(2)
        __load<Int>(ptr, 1)
        ",
        );
        let lowered = driver.lower().into_iter().next().unwrap().module();
        assert_lowered_function!(
            lowered,
            "@main",
            IRFunction {
                debug_info: Default::default(),
                ty: IRType::Func(vec![], IRType::Void.into()),
                name: "@main".into(),
                blocks: vec![BasicBlock {
                    id: BasicBlockID(0),
                    instructions: vec![
                        // First alloc (so we can get a pointer)
                        Instr::ConstantInt(Register(1), 2),
                        Instr::Alloc {
                            dest: Register(0),
                            ty: IRType::Int,
                            count: Some(IRValue::Register(Register(1))),
                        },
                        Instr::ConstantInt(Register(3), 1),
                        Instr::GetElementPointer {
                            dest: Register(4),
                            base: Register(0),
                            ty: IRType::TypedBuffer {
                                element: IRType::Int.into()
                            },
                            index: Register(3).into()
                        },
                        Instr::Load {
                            dest: Register(2),
                            ty: IRType::Int,
                            addr: Register(4)
                        },
                        Instr::Ret(IRType::Int, Some(Register(2).into()))
                    ],
                }],
                env_ty: None,
                env_reg: None,
                size: 5
            },
        );
    }

    #[test]
    fn lowers_ir_instr() {
        let mut driver = Driver::with_str(
            "
        let x = 1
        let y = 2
        __ir_instr<Int>(\"$? = add int %0, %1;\")
        ",
        );
        let lowered = driver.lower().into_iter().next().unwrap().module();
        assert_lowered_function!(
            lowered,
            "@main",
            IRFunction {
                debug_info: Default::default(),
                ty: IRType::Func(vec![], IRType::Void.into()),
                name: "@main".into(),
                blocks: vec![BasicBlock {
                    id: BasicBlockID(0),
                    instructions: vec![
                        Instr::ConstantInt(Register(0), 1),
                        Instr::ConstantInt(Register(1), 2),
                        Instr::Add(Register(2), IRType::Int, Register(0), Register(1)),
                        Instr::Ret(IRType::Int, Some(Register(2).into()))
                    ],
                }],
                env_ty: None,
                env_reg: None,
                size: 3
            },
        );
    }
}
