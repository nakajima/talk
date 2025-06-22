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
                vec![Ty::TypeVar(TypeVarID(-5, TypeVarKind::Element))],
            ),
            unbound_vars: vec![TypeVarID(-5, TypeVarKind::Element)],
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
                vec![Ty::TypeVar(TypeVarID(-8, TypeVarKind::Element))],
            ),
            unbound_vars: vec![TypeVarID(-8, TypeVarKind::Element)],
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
        // Reserve -10 for tuple symbol
    ]
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
    fn checks_alloc() {
        let checked = check(
            "
        __alloc<Int>(8)
        ",
        )
        .unwrap();

        assert!(checked.source_file.diagnostics().is_empty());
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

        assert!(checked.source_file.diagnostics().is_empty());
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
            checked.source_file.diagnostics().is_empty(),
            "{:#?}",
            checked.source_file.diagnostics()
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

        assert!(checked.source_file.diagnostics().is_empty());
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
            Expr::TypeRepr("Optional".into(), vec![0], false)
        );

        assert_eq!(
            *parsed.get(&0).unwrap(),
            Expr::TypeRepr("Int".into(), vec![], false)
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
            ir_type::IRType,
            lowerer::{BasicBlock, BasicBlockID, IRFunction},
            register::Register,
        },
        parser::parse,
        type_checker::Ty,
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
                            ty: IRType::array(),
                            count: None
                        },
                        // Set the array's count
                        Instr::ConstantInt(Register(1), 3),
                        Instr::GetElementPointer {
                            dest: Register(2),
                            base: Register(0),
                            ty: IRType::array(),
                            index: 0.into(),
                        },
                        Instr::Store {
                            location: Register(2),
                            ty: IRType::Int,
                            val: Register(1)
                        },
                        // Set the array's capacity
                        Instr::ConstantInt(Register(3), 3),
                        Instr::GetElementPointer {
                            dest: Register(4),
                            base: Register(0),
                            ty: IRType::array(),
                            index: 1.into(),
                        },
                        Instr::Store {
                            location: Register(4),
                            ty: IRType::Int,
                            val: Register(3)
                        },
                        // Get array's storage pointer
                        Instr::GetElementPointer {
                            dest: Register(5),
                            base: Register(0),
                            ty: IRType::array(),
                            index: 2.into(),
                        },
                        // Alloc space for the items
                        Instr::Alloc {
                            dest: Register(6),
                            ty: IRType::Int,
                            count: Some(Register(1))
                        },
                        Instr::Store {
                            ty: IRType::Pointer,
                            val: Register(6),
                            location: Register(5)
                        },
                        // Store first element
                        Instr::ConstantInt(Register(7), 1),
                        Instr::GetElementPointer {
                            dest: Register(8),
                            base: Register(6),
                            ty: IRType::Array {
                                element: IRType::Int.into()
                            },
                            index: 0.into(),
                        },
                        Instr::Store {
                            ty: IRType::Int,
                            val: Register(7),
                            location: Register(8)
                        },
                        // Store second element
                        Instr::ConstantInt(Register(9), 2),
                        Instr::GetElementPointer {
                            dest: Register(10),
                            base: Register(6),
                            ty: IRType::Array {
                                element: IRType::Int.into()
                            },
                            index: 1.into(),
                        },
                        Instr::Store {
                            ty: IRType::Int,
                            val: Register(9),
                            location: Register(10)
                        },
                        // Store third element
                        Instr::ConstantInt(Register(11), 3),
                        Instr::GetElementPointer {
                            dest: Register(12),
                            base: Register(6),
                            ty: IRType::Array {
                                element: IRType::Int.into()
                            },
                            index: 2.into(),
                        },
                        Instr::Store {
                            ty: IRType::Int,
                            val: Register(11),
                            location: Register(12)
                        },
                        Instr::Load {
                            dest: Register(13),
                            ty: IRType::array(),
                            addr: Register(0),
                        },
                        // Get .count
                        Instr::GetElementPointer {
                            dest: Register(14),
                            base: Register(13),
                            ty: IRType::array(),
                            index: 0.into(),
                        },
                        Instr::Load {
                            dest: Register(15),
                            ty: IRType::Int,
                            addr: Register(14)
                        },
                        Instr::Ret(IRType::Int, Some(Register(15).into()))
                    ],
                }],
                env_ty: None,
                env_reg: None,
                size: 16
            }
        );
    }
}

#[cfg(test)]
mod stdlib_tests {
    use crate::{
        assert_lowered_function, assert_lowered_functions,
        compiling::driver::Driver,
        lowering::{
            instr::Instr,
            ir_type::IRType,
            lowerer::{BasicBlock, BasicBlockID, IRFunction},
            register::Register,
        },
    };

    #[test]
    fn lowers_alloc() {
        let mut driver = Driver::with_str("__alloc<Int>(4)");
        let lowered = driver.lower().into_iter().next().unwrap().module();
        assert_lowered_functions!(
            lowered,
            vec![IRFunction {
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
                            count: Some(Register(1)),
                        },
                        Instr::Ret(IRType::Pointer, Some(Register(0).into()))
                    ],
                }],
                env_ty: None,
                env_reg: None,
                size: 5,
            }],
        )
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
        assert_lowered_functions!(
            lowered,
            vec![IRFunction {
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
                            count: Some(Register(1)),
                        },
                        // Realloc
                        Instr::ConstantInt(Register(3), 4),
                        Instr::Alloc {
                            dest: Register(2),
                            ty: IRType::Int,
                            count: Some(Register(3)),
                        },
                        Instr::Ret(IRType::Pointer, Some(Register(2).into()))
                    ],
                }],
                env_ty: None,
                env_reg: None,
                size: 5,
            }],
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
                            count: Some(Register(1)),
                        },
                        Instr::ConstantInt(Register(3), 1),
                        Instr::ConstantInt(Register(4), 1),
                        Instr::GetElementPointer {
                            dest: Register(5),
                            base: Register(0),
                            ty: IRType::Array {
                                element: IRType::Int.into()
                            },
                            index: Register(3).into(),
                        },
                        Instr::Store {
                            val: Register(4),
                            ty: IRType::Int,
                            location: Register(5)
                        },
                        Instr::Ret(IRType::Void, Some(Register(2).into()))
                    ],
                }],
                env_ty: None,
                env_reg: None,
                size: 6,
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
        assert_lowered_functions!(
            lowered,
            vec![IRFunction {
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
                            count: Some(Register(1)),
                        },
                        Instr::ConstantInt(Register(3), 1),
                        Instr::GetElementPointer {
                            dest: Register(4),
                            base: Register(0),
                            ty: IRType::Array {
                                element: IRType::Int.into()
                            },
                            index: Register(3).into()
                        },
                        Instr::Load {
                            dest: Register(2),
                            ty: IRType::Int.into(),
                            addr: Register(4)
                        },
                        Instr::Ret(IRType::Int, Some(Register(2).into()))
                    ],
                }],
                env_ty: None,
                env_reg: None,
                size: 5
            }],
        )
    }
}
