#[cfg(test)]
pub mod helpers {
    use std::path::PathBuf;

    use crate::{
        compiling::driver::{Driver, DriverConfig},
        environment::Environment,
        lowering::{ir_error::IRError, ir_module::IRModule},
    };

    pub fn lower_without_prelude(input: &'static str) -> Result<IRModule, IRError> {
        let mut driver = Driver::new(DriverConfig {
            executable: true,
            include_prelude: false,
            include_comments: false,
        });
        driver.update_file(&PathBuf::from("-"), input.into());
        let lowered = driver.lower().into_iter().next().unwrap();
        let diagnostics = driver.refresh_diagnostics_for(&PathBuf::from("-")).unwrap();
        let module = lowered.module().clone();

        assert!(diagnostics.is_empty(), "{diagnostics:?}");
        Ok(module)
    }

    pub fn lower_without_prelude_with_env(
        input: &'static str,
    ) -> Result<(IRModule, Environment), IRError> {
        let mut driver = Driver::new(DriverConfig {
            executable: true,
            include_prelude: false,
            include_comments: false,
        });
        driver.update_file(&PathBuf::from("-"), input.into());
        let lowered = driver.lower().into_iter().next().unwrap();
        let diagnostics = driver.refresh_diagnostics_for(&PathBuf::from("-")).unwrap();
        let module = lowered.module().clone();

        assert!(diagnostics.is_empty(), "{diagnostics:?}");
        Ok((module, lowered.env))
    }
}

#[cfg(test)]
pub mod lowering_tests {
    use std::{collections::HashMap, path::PathBuf};

    use crate::{
        SymbolID, assert_lowered_function,
        compiling::{
            compiled_module::{CompiledModule, ImportedSymbol, ImportedSymbolKind},
            driver::{Driver, DriverConfig},
        },
        lowering::{
            instr::{Callee, Instr},
            ir_error::IRError,
            ir_function::IRFunction,
            ir_module::{IRConstantData, IRModule},
            ir_type::IRType,
            ir_value::IRValue,
            lowerer::{BasicBlock, BasicBlockID, RefKind, RegisterList, TypedRegister},
            lowerer_tests::helpers::lower_without_prelude,
            phi_predecessors::PhiPredecessors,
            register::Register,
        },
        prelude::compile_prelude,
        ty::Ty,
    };

    pub fn lower_with_imports(
        imports: Vec<CompiledModule>,
        input: &'static str,
    ) -> Result<IRModule, IRError> {
        let mut driver = Driver::new(DriverConfig {
            executable: true,
            include_prelude: true,
            include_comments: false,
        });
        driver.update_file(&PathBuf::from("-"), input.into());
        driver.import_modules(imports);
        let lowered = driver.lower().into_iter().next().unwrap();
        let diagnostics = driver.refresh_diagnostics_for(&PathBuf::from("-")).unwrap();
        let module = lowered.module().clone();

        assert!(diagnostics.is_empty(), "{diagnostics:?}");
        Ok(module)
    }

    pub fn lower(input: &'static str) -> Result<IRModule, IRError> {
        let mut driver = Driver::new(DriverConfig {
            executable: true,
            include_prelude: true,
            include_comments: false,
        });
        driver.update_file(&PathBuf::from("-"), input.into());
        let lowered = driver.lower().into_iter().next().unwrap();
        let diagnostics = driver.refresh_diagnostics_for(&PathBuf::from("-")).unwrap();
        let module = lowered.module().clone();

        assert!(diagnostics.is_empty(), "{diagnostics:?}");
        Ok(module)
    }

    #[test]
    fn lowers_basic_function() {
        let lowered = lower("func foo() { 123 }").unwrap();

        // Define the types we'll be using to make the test cleaner
        let foo_func_type = IRType::Func(vec![], Box::new(IRType::Int));

        assert_lowered_function!(
            lowered,
            format!("@_{}_foo", SymbolID::resolved(1).0),
            IRFunction {
                debug_info: Default::default(),
                ty: foo_func_type.clone(),
                name: format!("@_{}_foo", SymbolID::resolved(1).0),
                blocks: vec![BasicBlock {
                    id: BasicBlockID(0),
                    instructions: vec![
                        Instr::ConstantInt(Register(0), 123),
                        Instr::Ret(IRType::Int, Some(Register(0).into()))
                    ],
                }],
                env_ty: None,
                env_reg: None,
                size: 1
            }
        );
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
                        Instr::Ref(
                            Register(0),
                            foo_func_type.clone(),
                            RefKind::Func(format!("@_{}_foo", SymbolID::resolved(1).0))
                        ),
                        Instr::Ret(IRType::POINTER, Some(Register(0).into())),
                    ],
                }],
                env_ty: None,
                env_reg: None,
                size: 1
            }
        );
    }

    #[test]
    fn lowers_recursion() {
        let lowered = lower(
            "
            func foo(x) {
                foo(x)
            }
            ",
        )
        .unwrap();

        let foo_name = format!("@_{}_foo", SymbolID::resolved(1).0);
        let t3 = format!("T{}", compile_prelude().environment.next_type_var_id() + 3);
        let t4 = format!("T{}", compile_prelude().environment.next_type_var_id() + 4);

        assert_lowered_function!(
            lowered,
            foo_name,
            IRFunction {
                debug_info: Default::default(),
                ty: IRType::Func(
                    vec![IRType::TypeVar(t3.clone())],
                    Box::new(IRType::TypeVar(t4.clone()))
                ),
                name: foo_name.clone(),
                blocks: vec![BasicBlock {
                    id: BasicBlockID(0),
                    instructions: vec![
                        Instr::Call {
                            dest_reg: Register(1),
                            ty: IRType::TypeVar(t4.clone()),
                            callee: Callee::Name(foo_name.clone()),
                            args: RegisterList(vec![TypedRegister::new(
                                IRType::TypeVar(t3.clone()),
                                Register(0)
                            )])
                        },
                        // The `return x` becomes a Ret instruction using the argument register.
                        // In our calling convention, the env is %0, so x is %1.
                        Instr::Ret(IRType::TypeVar(t4.clone()), Some(Register(1).into())),
                    ],
                }],
                env_ty: None,
                env_reg: None,
                size: 2
            }
        );
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
                        Instr::Ref(
                            Register(0),
                            IRType::Func(
                                vec![IRType::TypeVar(t3.clone())],
                                IRType::TypeVar(t4.clone()).into()
                            ),
                            RefKind::Func(format!("@_{}_foo", SymbolID::resolved(1).0))
                        ),
                        Instr::Ret(IRType::POINTER, Some(Register(0).into())),
                    ],
                }],
                env_ty: None,
                env_reg: None,
                size: 1
            }
        );
    }

    #[test]
    fn lowers_return() {
        let lowered = lower(
            "
            func foo(x) {
                return x
                123
            }
            ",
        )
        .unwrap();

        let foo_func_type = IRType::Func(vec![IRType::Int], Box::new(IRType::Int));
        let foo_name = format!("@_{}_foo", SymbolID::resolved(1).0);

        assert_lowered_function!(
            lowered,
            foo_name,
            IRFunction {
                debug_info: Default::default(),
                ty: foo_func_type.clone(),
                name: foo_name.clone(),
                blocks: vec![BasicBlock {
                    id: BasicBlockID(0),
                    instructions: vec![
                        // The `return x` becomes a Ret instruction using the argument register.
                        // In our calling convention, the env is %0, so x is %1.
                        Instr::Ret(IRType::Int, Some(Register(0).into())),
                        // The `123` is dead code but is still lowered.
                        Instr::ConstantInt(Register(1), 123),
                        // The implicit return is still added
                        Instr::Ret(IRType::Int, Some(Register(1).into()))
                    ],
                }],
                env_ty: None,
                env_reg: None,
                size: 2
            }
        );

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
                        Instr::Ref(Register(0), foo_func_type, RefKind::Func(foo_name)),
                        Instr::Ret(IRType::POINTER, Some(Register(0).into())),
                    ],
                }],
                env_ty: None,
                env_reg: None,
                size: 1
            }
        );
    }

    #[test]
    fn lowers_calls() {
        let lowered = lower("func foo(x) { x }\nfoo(123)").unwrap();

        let type_var = format!("T{}", compile_prelude().environment.next_type_var_id() + 2);

        let foo_func_type = IRType::Func(
            vec![IRType::TypeVar(type_var.clone())],
            Box::new(IRType::TypeVar(type_var.clone())),
        );

        let foo_name = format!("@_{}_foo", SymbolID::resolved(1).0);

        assert_lowered_function!(
            lowered,
            foo_name,
            IRFunction {
                debug_info: Default::default(),
                ty: foo_func_type.clone(),
                name: foo_name.clone(),
                blocks: vec![BasicBlock {
                    id: BasicBlockID(0),
                    instructions: vec![Instr::Ret(
                        IRType::TypeVar(type_var.clone()),
                        Some(Register(0).into())
                    )],
                }],
                env_ty: None,
                env_reg: None,
                size: 1
            }
        );
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
                        Instr::Ref(
                            Register(0),
                            IRType::Func(
                                vec![IRType::TypeVar(type_var.clone())],
                                IRType::TypeVar(type_var.clone()).into()
                            ),
                            RefKind::Func(foo_name.clone())
                        ),
                        // Get the arg
                        Instr::ConstantInt(Register(1), 123),
                        Instr::Call {
                            dest_reg: Register(2),
                            ty: IRType::Int,
                            callee: Callee::Name(foo_name),
                            args: RegisterList(vec![TypedRegister::new(IRType::Int, Register(1))]), // (env_ptr, arg)
                        },
                        // 4. Return the result of the call.
                        Instr::Ret(IRType::Int, Some(Register(2).into()))
                    ],
                }],
                env_ty: None,
                env_reg: None,
                size: 3
            },
        );
    }

    #[test]
    fn lowers_func_with_params() {
        let type_var = format!("T{}", compile_prelude().environment.next_type_var_id() + 2);
        let lowered = lower("func foo(x) { x }").unwrap();
        let foo_name = format!("@_{}_foo", SymbolID::resolved(1).0);
        assert_lowered_function!(
            &lowered,
            foo_name,
            IRFunction {
                debug_info: Default::default(),
                ty: IRType::Func(
                    vec![IRType::TypeVar(type_var.clone())],
                    IRType::TypeVar(type_var.clone()).into()
                ),
                name: format!("@_{}_foo", SymbolID::resolved(1).0),
                blocks: vec![BasicBlock {
                    id: BasicBlockID(0),
                    instructions: vec![Instr::Ret(
                        IRType::TypeVar(type_var.clone()),
                        Some(Register(0).into())
                    )],
                }],
                env_ty: None,
                env_reg: None,
                size: 1
            }
        );
        assert_lowered_function!(
            &lowered,
            "@main",
            IRFunction {
                debug_info: Default::default(),
                ty: IRType::Func(vec![], IRType::Void.into()),
                name: "@main".into(),
                blocks: vec![BasicBlock {
                    id: BasicBlockID(0),
                    instructions: vec![
                        Instr::Ref(
                            Register(0),
                            IRType::Func(
                                vec![IRType::TypeVar(type_var.clone())],
                                IRType::TypeVar(type_var.clone()).into()
                            ),
                            RefKind::Func(format!("@_{}_foo", SymbolID::resolved(1).0))
                        ),
                        Instr::Ret(IRType::POINTER, Some(Register(0).into()))
                    ],
                }],
                env_ty: None,
                env_reg: None,
                size: 1
            },
        )
    }

    #[test]
    fn lowers_int() {
        let lowered = lower("123").unwrap();
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
                        Instr::ConstantInt(Register(0), 123),
                        Instr::Ret(IRType::Int, Some(Register(0).into()))
                    ],
                }],
                env_ty: None,
                env_reg: None,
                size: 1
            }
        )
    }

    #[test]
    fn lowers_float() {
        let lowered = lower("123.0").unwrap();
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
                        Instr::ConstantFloat(Register(0), 123.),
                        Instr::Ret(IRType::Float, Some(Register(0).into()))
                    ],
                }],
                env_ty: None,
                env_reg: None,
                size: 1
            },
        )
    }

    #[test]
    fn lowers_bools() {
        let lowered = lower("true\nfalse").unwrap();
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
                        Instr::ConstantBool(Register(0), true),
                        Instr::ConstantBool(Register(1), false),
                        Instr::Ret(IRType::Bool, Some(Register(1).into())),
                    ],
                }],
                env_ty: None,
                env_reg: None,
                size: 2
            }
        )
    }

    #[test]
    fn lowers_add() {
        let lowered = lower("1 + 2").unwrap();
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
            }
        )
    }

    #[test]
    fn lowers_sub() {
        let lowered = lower("2 - 1").unwrap();
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
                        Instr::ConstantInt(Register(0), 2),
                        Instr::ConstantInt(Register(1), 1),
                        Instr::Sub(Register(2), IRType::Int, Register(0), Register(1)),
                        Instr::Ret(IRType::Int, Some(Register(2).into()))
                    ],
                }],
                env_ty: None,
                env_reg: None,
                size: 3
            },
        )
    }

    #[test]
    fn lowers_mul() {
        let lowered = lower("2 * 1").unwrap();
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
                        Instr::ConstantInt(Register(0), 2),
                        Instr::ConstantInt(Register(1), 1),
                        Instr::Mul(Register(2), IRType::Int, Register(0), Register(1)),
                        Instr::Ret(IRType::Int, Some(Register(2).into()))
                    ],
                }],
                env_ty: None,
                env_reg: None,
                size: 3
            }
        )
    }

    #[test]
    fn lowers_div() {
        let lowered = lower("2 / 1").unwrap();
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
                        Instr::ConstantInt(Register(0), 2),
                        Instr::ConstantInt(Register(1), 1),
                        Instr::Div(Register(2), IRType::Int, Register(0), Register(1)),
                        Instr::Ret(IRType::Int, Some(Register(2).into()))
                    ],
                }],
                env_ty: None,
                env_reg: None,
                size: 3
            }
        )
    }

    #[test]
    fn lowers_assignment() {
        let lowered = lower("let a = 123\na").unwrap();
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
                        Instr::ConstantInt(Register(0), 123),
                        Instr::Ret(IRType::Int, Some(Register(0).into())),
                    ],
                }],
                env_ty: None,
                env_reg: None,
                size: 1
            }
        )
    }

    #[test]
    fn lowers_if_expr_with_else() {
        let lowered = lower(
            "
                if true {
                    123
                } else {
                    456
                }

                789
        ",
        )
        .unwrap();

        let expected = IRFunction {
            debug_info: Default::default(),
            ty: IRType::Func(vec![], IRType::Void.into()),
            name: "@main".into(),
            blocks: vec![
                // if block
                BasicBlock {
                    id: BasicBlockID(0),
                    instructions: vec![
                        Instr::ConstantBool(Register(0), true),
                        Instr::Branch {
                            cond: Register(0),
                            true_target: BasicBlockID(1),
                            false_target: BasicBlockID(2),
                        },
                    ],
                },
                // if block
                BasicBlock {
                    id: BasicBlockID(1),
                    instructions: vec![
                        Instr::ConstantInt(Register(1), 123),
                        Instr::Jump(BasicBlockID(3)),
                    ],
                },
                // else block
                BasicBlock {
                    id: BasicBlockID(2),
                    instructions: vec![
                        Instr::ConstantInt(Register(2), 456),
                        Instr::Jump(BasicBlockID(3)),
                    ],
                },
                // converge block
                BasicBlock {
                    id: BasicBlockID(3),
                    instructions: vec![
                        Instr::Phi(
                            Register(3),
                            IRType::Int,
                            PhiPredecessors(vec![
                                (Register(1), BasicBlockID(1)),
                                (Register(2), BasicBlockID(2)),
                            ]),
                        ),
                        Instr::ConstantInt(Register(4), 789),
                        Instr::Ret(IRType::Int, Some(Register(4).into())),
                    ],
                },
            ],
            env_ty: None,
            env_reg: None,
            size: 5,
        };

        assert_lowered_function!(lowered, "@main", expected);
    }

    #[test]
    fn lowers_if_expr_without_else() {
        let lowered = lower(
            "
                if true {
                    return 123
                }

                789
        ",
        )
        .unwrap();

        let expected = IRFunction {
            debug_info: Default::default(),
            ty: IRType::Func(vec![], IRType::Void.into()),
            name: "@main".into(),
            blocks: vec![
                // if block
                BasicBlock {
                    id: BasicBlockID(0),
                    instructions: vec![
                        Instr::ConstantBool(Register(0), true),
                        Instr::Branch {
                            cond: Register(0),
                            true_target: BasicBlockID(1),
                            false_target: BasicBlockID(2),
                        },
                    ],
                },
                // if block
                BasicBlock {
                    id: BasicBlockID(1),
                    instructions: vec![
                        Instr::ConstantInt(Register(1), 123),
                        Instr::Ret(IRType::Int, Some(Register(1).into())),
                        Instr::Jump(BasicBlockID(2)),
                    ],
                },
                // else block
                BasicBlock {
                    id: BasicBlockID(2),
                    instructions: vec![
                        Instr::ConstantInt(Register(3), 789),
                        Instr::Ret(IRType::Int, Some(Register(3).into())),
                    ],
                },
            ],
            env_ty: None,
            env_reg: None,
            size: 4,
        };

        assert_lowered_function!(lowered, "@main", expected);
    }

    #[test]
    fn lowers_basic_enum() {
        let lowered = lower_without_prelude(
            "enum Foo {
                    case fizz, buzz
                }
                
                Foo.buzz",
        )
        .unwrap();
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
                        Instr::TagVariant(
                            Register(0),
                            IRType::Enum(SymbolID(1), vec![]),
                            1,
                            RegisterList::EMPTY
                        ),
                        Instr::Ret(IRType::Enum(SymbolID(1), vec![]), Some(Register(0).into()))
                    ],
                }],
                env_ty: None,
                env_reg: None,
                size: 1
            }
        )
    }

    #[test]
    fn lowers_builtin_optional() {
        let lowered = lower("Optional.some(123)").unwrap();
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
                        Instr::ConstantInt(Register(0), 123),
                        Instr::TagVariant(
                            Register(1),
                            IRType::Enum(SymbolID::OPTIONAL, vec![IRType::Int]),
                            0,
                            RegisterList(vec![TypedRegister::new(IRType::Int, Register(0))])
                        ),
                        Instr::Ret(
                            IRType::Enum(SymbolID::OPTIONAL, vec![IRType::Int]),
                            Some(Register(1).into())
                        )
                    ],
                }],
                env_ty: None,
                env_reg: None,
                size: 2
            }
        )
    }

    #[test]
    fn lowers_match_ints() {
        let lowered = lower(
            "
            match 123 {
                123 -> 3.14,
                456 -> 2.71
            }
            ",
        )
        .unwrap();

        assert_lowered_function!(
            lowered,
            "@main",
            IRFunction {
                debug_info: Default::default(),
                ty: IRType::Func(vec![], IRType::Void.into()),
                name: "@main".into(),
                blocks: vec![
                    BasicBlock {
                        id: BasicBlockID::ENTRY,
                        instructions: vec![
                            Instr::ConstantInt(Register(0), 123),
                            Instr::Jump(BasicBlockID(2))
                        ],
                    },
                    BasicBlock {
                        id: BasicBlockID(1),
                        instructions: vec![
                            Instr::Phi(
                                Register(7),
                                IRType::Float,
                                PhiPredecessors(vec![
                                    (Register(3), BasicBlockID(5)),
                                    (Register(6), BasicBlockID(6))
                                ])
                            ),
                            Instr::Ret(IRType::Float, Some(Register(7).into()))
                        ]
                    },
                    BasicBlock {
                        id: BasicBlockID(2),
                        instructions: vec![
                            Instr::ConstantInt(Register(1), 123),
                            Instr::Eq(Register(2), IRType::Int, Register(0), Register(1)),
                            Instr::Branch {
                                cond: Register(2),
                                true_target: BasicBlockID(5),
                                false_target: BasicBlockID(3)
                            },
                        ]
                    },
                    BasicBlock {
                        id: BasicBlockID(3),
                        instructions: vec![
                            Instr::ConstantInt(Register(4), 456),
                            Instr::Eq(Register(5), IRType::Int, Register(0), Register(4)),
                            Instr::Branch {
                                cond: Register(5),
                                true_target: BasicBlockID(6),
                                false_target: BasicBlockID(4)
                            }
                        ]
                    },
                    BasicBlock {
                        id: BasicBlockID(4),
                        instructions: vec![Instr::Unreachable]
                    },
                    BasicBlock {
                        id: BasicBlockID(5),
                        instructions: vec![
                            Instr::ConstantFloat(Register(3), 3.14),
                            Instr::Jump(BasicBlockID(1))
                        ]
                    },
                    BasicBlock {
                        id: BasicBlockID(6),
                        instructions: vec![
                            Instr::ConstantFloat(Register(6), 2.71),
                            Instr::Jump(BasicBlockID(1))
                        ]
                    },
                ],
                env_ty: None,
                env_reg: None,
                size: 8
            }
        )
    }

    #[test]
    fn lowers_match_bind() {
        let lowered = lower(
            "
            match Optional.some(123) {
                .some(x) -> x,
                .none -> 456
            }
            ",
        )
        .unwrap();

        assert_lowered_function!(
            lowered,
            "@main",
            IRFunction {
                debug_info: Default::default(),
                ty: IRType::Func(vec![], IRType::Void.into()),
                name: "@main".into(),
                blocks: vec![
                    // Block 0: Dispatch
                    BasicBlock {
                        id: BasicBlockID::ENTRY,
                        instructions: vec![
                            // Scrutinee: Optional.some(123)
                            Instr::ConstantInt(Register(0), 123),
                            Instr::TagVariant(
                                Register(1),
                                IRType::Enum(SymbolID::OPTIONAL, vec![IRType::Int]),
                                0,
                                RegisterList(vec![TypedRegister::new(IRType::Int, Register(0))])
                            ),
                            Instr::Jump(BasicBlockID(2)),
                        ],
                    },
                    // Block 1: Merge Point
                    BasicBlock {
                        id: BasicBlockID(1),
                        instructions: vec![
                            Instr::Phi(
                                Register(10),
                                IRType::Int,
                                PhiPredecessors(vec![
                                    (Register(5), BasicBlockID(5)), // from .some arm
                                    (Register(9), BasicBlockID(6)), // from .none arm
                                ])
                            ),
                            Instr::Ret(IRType::Int, Some(Register(10).into())),
                        ]
                    },
                    BasicBlock {
                        id: BasicBlockID(2),
                        instructions: vec![
                            Instr::GetEnumTag(Register(2), Register(1)),
                            Instr::ConstantInt(Register(3), 0), // Tag for .some
                            Instr::Eq(Register(4), IRType::Int, Register(2), Register(3)),
                            Instr::Branch {
                                cond: Register(4),
                                true_target: BasicBlockID(5),
                                false_target: BasicBlockID(3)
                            },
                        ]
                    },
                    // Pattern 2
                    BasicBlock {
                        id: BasicBlockID(3),
                        instructions: vec![
                            Instr::GetEnumTag(Register(6), Register(1)),
                            Instr::ConstantInt(Register(7), 1), // Tag for .none
                            Instr::Eq(Register(8), IRType::Int, Register(6), Register(7)),
                            Instr::Branch {
                                cond: Register(8),
                                true_target: BasicBlockID(6),
                                false_target: BasicBlockID(4)
                            },
                        ]
                    },
                    BasicBlock {
                        id: BasicBlockID(4),
                        instructions: vec![Instr::Unreachable]
                    },
                    BasicBlock {
                        id: BasicBlockID(5),
                        instructions: vec![
                            // This is the binding: get value at index 0 and put it in register 8
                            Instr::GetEnumValue(Register(5), IRType::Int, Register(1), 0, 0),
                            Instr::Jump(BasicBlockID(1)),
                        ]
                    },
                    // Block 2: Body for .some(x) -> x
                    BasicBlock {
                        id: BasicBlockID(6),
                        instructions: vec![
                            Instr::ConstantInt(Register(9), 456),
                            Instr::Jump(BasicBlockID(1)),
                        ]
                    },
                ],
                env_ty: None,
                env_reg: None,
                size: 11
            }
        )
    }

    #[test]
    fn lowers_enum_match() {
        let lowered = lower_without_prelude(
            "
            enum Foo {
                case fizz, buzz
            }
            match Foo.buzz {
                .fizz -> 123,
                .buzz -> 456
            }
            ",
        )
        .unwrap();

        use Instr::*;
        assert_lowered_function!(
            lowered,
            "@main",
            IRFunction {
                debug_info: Default::default(),
                ty: IRType::Func(vec![], IRType::Void.into()),
                name: "@main".into(),
                blocks: vec![
                    BasicBlock {
                        id: BasicBlockID(0,),
                        instructions: vec![
                            TagVariant(
                                Register(0),
                                IRType::Enum(SymbolID(1), vec![],),
                                1,
                                RegisterList(vec![]),
                            ),
                            Jump(BasicBlockID(2,),),
                        ],
                    },
                    BasicBlock {
                        id: BasicBlockID(1,),
                        instructions: vec![
                            Phi(
                                Register(9,),
                                IRType::Int,
                                PhiPredecessors(vec![
                                    (Register(4,), BasicBlockID(5,),),
                                    (Register(8,), BasicBlockID(6,),),
                                ],),
                            ),
                            Ret(IRType::Int, Some(Register(9,).into(),),),
                        ],
                    },
                    BasicBlock {
                        id: BasicBlockID(2,),
                        instructions: vec![
                            GetEnumTag(Register(1,), Register(0,),),
                            ConstantInt(Register(2,), 0,),
                            Eq(Register(3,), IRType::Int, Register(1,), Register(2,),),
                            Branch {
                                cond: Register(3,),
                                true_target: BasicBlockID(5,),
                                false_target: BasicBlockID(3,),
                            },
                        ],
                    },
                    BasicBlock {
                        id: BasicBlockID(3,),
                        instructions: vec![
                            GetEnumTag(Register(5,), Register(0,),),
                            ConstantInt(Register(6,), 1,),
                            Eq(Register(7,), IRType::Int, Register(5,), Register(6,),),
                            Branch {
                                cond: Register(7,),
                                true_target: BasicBlockID(6,),
                                false_target: BasicBlockID(4,),
                            },
                        ],
                    },
                    BasicBlock {
                        id: BasicBlockID(4,),
                        instructions: vec![Unreachable,],
                    },
                    BasicBlock {
                        id: BasicBlockID(5,),
                        instructions: vec![
                            ConstantInt(Register(4,), 123,),
                            Jump(BasicBlockID(1,),),
                        ],
                    },
                    BasicBlock {
                        id: BasicBlockID(6,),
                        instructions: vec![
                            ConstantInt(Register(8,), 456,),
                            Jump(BasicBlockID(1,),),
                        ],
                    },
                ],
                env_ty: None,
                env_reg: None,
                size: 10
            }
        );
    }

    #[test]
    fn lowers_captured_value() {
        let lowered = lower(
            "
            let x = 1
            func add(y) { x + y }
            add(2)
            ",
        )
        .unwrap();

        // The function signature for `add` only includes its explicit parameters.
        let add_func_type = IRType::Func(vec![IRType::Int], Box::new(IRType::Int));
        let env_struct_type = IRType::Struct(SymbolID(0), vec![IRType::Int], vec![]);

        assert_lowered_function!(
            lowered,
            format!("@_{}_add", SymbolID::resolved(1).0),
            IRFunction {
                debug_info: Default::default(),
                ty: add_func_type.clone(),
                name: format!("@_{}_add", SymbolID::resolved(1).0),
                blocks: vec![BasicBlock {
                    id: BasicBlockID(0),
                    instructions: vec![
                        Instr::GetElementPointer {
                            dest: Register(2),
                            ty: IRType::closure(),
                            base: Register(0),
                            index: 0.into(),
                        },
                        Instr::Load {
                            dest: Register(3),
                            ty: IRType::Int,
                            addr: Register(2)
                        },
                        Instr::Add(Register(4), IRType::Int, Register(3), Register(1)),
                        Instr::Ret(IRType::Int, Some(Register(4).into())),
                    ],
                }],
                env_ty: Some(IRType::Struct(SymbolID::ENV, vec![IRType::Int], vec![])),
                env_reg: Some(Register(0)),
                size: 5
            }
        );
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
                        // === Part 1: Setup `let x = 1` and environment ===
                        // The environment struct now holds the VALUE of x, not a pointer.
                        Instr::ConstantInt(Register(0), 1),
                        Instr::Alloc {
                            dest: Register(1),
                            count: None,
                            ty: IRType::closure()
                        },
                        Instr::MakeStruct {
                            dest: Register(2),
                            ty: env_struct_type.clone(),
                            values: RegisterList(vec![TypedRegister::new(
                                IRType::Int,
                                Register(0)
                            )])
                        },
                        Instr::Alloc {
                            dest: Register(3),
                            count: None,
                            ty: env_struct_type.clone()
                        },
                        Instr::Store {
                            val: Register(2).into(),
                            location: Register(3),
                            ty: env_struct_type.clone()
                        },
                        Instr::Ref(
                            Register(4),
                            add_func_type.clone(),
                            RefKind::Func(format!("@_{}_add", SymbolID::resolved(1).0))
                        ),
                        Instr::GetElementPointer {
                            dest: Register(5),
                            base: Register(1),
                            index: 1.into(),
                            ty: IRType::closure()
                        },
                        Instr::GetElementPointer {
                            dest: Register(6),
                            base: Register(1),
                            index: 0.into(),
                            ty: IRType::closure()
                        },
                        Instr::Store {
                            val: Register(3).into(),
                            location: Register(5),
                            ty: IRType::POINTER
                        },
                        Instr::Store {
                            val: Register(4).into(),
                            location: Register(6),
                            ty: IRType::POINTER
                        },
                        Instr::ConstantInt(Register(7), 2), // The argument `y`.
                        // Unpack the closure environment
                        Instr::GetElementPointer {
                            dest: Register(8),
                            base: Register(1),
                            index: 1.into(),
                            ty: IRType::closure()
                        },
                        // Instr::Load {
                        //     dest: Register(9),
                        //     ty: IRType::POINTER,
                        //     addr: Register(8)
                        // },
                        Instr::Call {
                            dest_reg: Register(9),
                            ty: IRType::Int,
                            callee: Callee::Name(format!("@_{}_add", SymbolID::resolved(1).0)),
                            args: RegisterList(vec![
                                TypedRegister::new(IRType::POINTER, Register(8)),
                                TypedRegister::new(IRType::Int, Register(7))
                            ]),
                        },
                        Instr::Ret(IRType::Int, Some(Register(9).into())),
                    ],
                }],
                env_ty: None,
                env_reg: None,
                size: 10
            }
        );
    }

    #[test]
    fn lowers_strings() {
        let lowered = lower("\"sup \"").unwrap();

        assert_eq!(lowered.constants.len(), 1);
        assert_eq!(
            lowered.constants[0],
            IRConstantData::RawBuffer("sup ".as_bytes().to_vec())
        );

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
                        // Allocate the String struct
                        Instr::Alloc {
                            dest: Register(0),
                            ty: IRType::string(),
                            count: None
                        },
                        // Set the length
                        Instr::GetElementPointer {
                            dest: Register(1),
                            base: Register(0),
                            ty: IRType::string(),
                            index: 0.into(),
                        },
                        Instr::Store {
                            ty: IRType::Int,
                            val: IRValue::ImmediateInt(4),
                            location: Register(1)
                        },
                        // Set the capacity
                        Instr::GetElementPointer {
                            dest: Register(2),
                            base: Register(0),
                            ty: IRType::string(),
                            index: 1.into(),
                        },
                        Instr::Store {
                            ty: IRType::Int,
                            val: IRValue::ImmediateInt(4),
                            location: Register(2)
                        },
                        // Set the storage
                        Instr::GetElementPointer {
                            dest: Register(3),
                            base: Register(0),
                            ty: IRType::string(),
                            index: 2.into(),
                        },
                        Instr::Const {
                            dest: Register(4),
                            ty: IRType::RawBuffer,
                            val: IRValue::ImmediateInt(0)
                        },
                        Instr::Store {
                            ty: IRType::POINTER,
                            val: Register(4).into(),
                            location: Register(3)
                        },
                        Instr::Ret(IRType::string(), Some(Register(0).into())),
                    ],
                }],
                env_ty: None,
                env_reg: None,
                size: 5
            }
        )
    }

    #[test]
    fn lowers_struct_initializer() {
        let lowered = lower_without_prelude(
            "
            struct Person {
                let age: Int

                init(age: Int) {
                    self.age = age
                }
            }

            Person(age: 123)
            ",
        )
        .unwrap();

        assert_lowered_function!(
            lowered,
            format!("@_1_Person_init"),
            IRFunction {
                debug_info: Default::default(),
                ty: IRType::Func(vec![IRType::Int], IRType::POINTER.into()),
                name: "@_1_Person_init".into(),
                blocks: vec![BasicBlock {
                    id: BasicBlockID(0),
                    instructions: vec![
                        // self.age = age
                        Instr::GetElementPointer {
                            dest: Register(2),
                            base: Register(0), // self is in register 0
                            ty: IRType::Struct(SymbolID(1), vec![IRType::Int], vec![]),
                            index: 0.into(),
                        },
                        Instr::Store {
                            ty: IRType::Int,
                            val: Register(1).into(), // age is in register 1
                            location: Register(2)
                        },
                        Instr::Load {
                            ty: IRType::Struct(SymbolID(1), vec![IRType::Int], vec![]),
                            dest: Register(3),
                            addr: Register(0)
                        },
                        Instr::Ret(
                            IRType::Struct(SymbolID(1), vec![IRType::Int], vec![]),
                            Some(Register(3).into())
                        )
                    ],
                }],
                env_ty: Some(IRType::Struct(SymbolID(1), vec![IRType::Int], vec![])),
                env_reg: Some(Register(0)),
                size: 4
            },
        );

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
                        // Alloc the arg
                        Instr::ConstantInt(Register(0), 123),
                        // Alloc the space for the struct
                        Instr::Alloc {
                            dest: Register(1),
                            ty: IRType::Struct(SymbolID(1), vec![IRType::Int], vec![]),
                            count: None,
                        },
                        // Call the init directly
                        Instr::Call {
                            dest_reg: Register(2),
                            ty: IRType::Struct(SymbolID(1), vec![IRType::Int], vec![]),
                            callee: Callee::Name(format!("@_{}_Person_init", SymbolID(1).0),),
                            args: RegisterList(vec![
                                TypedRegister::new(IRType::POINTER, Register(1)),
                                TypedRegister::new(IRType::Int, Register(0)),
                            ]),
                        },
                        Instr::Ret(
                            IRType::Struct(SymbolID(1), vec![IRType::Int], vec![]),
                            Some(Register(1).into()),
                        ),
                    ],
                }],
                env_ty: None,
                env_reg: None,
                size: 3
            },
        )
    }

    #[test]
    fn lowers_struct_property() {
        let lowered = lower(
            "
        struct Person {
            let age: Int

            init(age: Int) {
                self.age = age
            }
        }

        Person(age: 123).age
        ",
        )
        .unwrap();

        let person_struct_ty = IRType::Struct(SymbolID::resolved(1), vec![IRType::Int], vec![]);
        let person_init_func_ty = IRType::Func(vec![IRType::Int], IRType::POINTER.into());

        assert_lowered_function!(
            lowered,
            format!("@_{}_Person_init", SymbolID::resolved(1).0),
            IRFunction {
                debug_info: Default::default(),
                ty: person_init_func_ty.clone(),
                name: format!("@_{}_Person_init", SymbolID::resolved(1).0),
                blocks: vec![BasicBlock {
                    id: BasicBlockID(0),
                    instructions: vec![
                        // self.age = age
                        Instr::GetElementPointer {
                            dest: Register(2),
                            base: Register(0), // self is in register 0
                            ty: person_struct_ty.clone(),
                            index: 0.into(),
                        },
                        Instr::Store {
                            ty: IRType::Int,
                            val: Register(1).into(), // age is in register 1
                            location: Register(2)
                        },
                        Instr::Load {
                            ty: person_struct_ty.clone(),
                            dest: Register(3),
                            addr: Register(0)
                        },
                        // return self
                        Instr::Ret(person_struct_ty.clone(), Some(Register(3).into()))
                    ],
                }],
                env_ty: Some(person_struct_ty.clone()),
                env_reg: Some(Register(0),),
                size: 4
            }
        );
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
                        Instr::ConstantInt(Register(0), 123),
                        Instr::Alloc {
                            dest: Register(1),
                            count: None,
                            ty: person_struct_ty.clone(),
                        },
                        Instr::Call {
                            dest_reg: Register(2),
                            ty: person_struct_ty.clone(),
                            callee: Callee::Name(format!(
                                "@_{}_Person_init",
                                SymbolID::resolved(1).0
                            )),
                            args: RegisterList(vec![
                                TypedRegister::new(IRType::POINTER, Register(1)),
                                TypedRegister::new(IRType::Int, Register(0))
                            ])
                        },
                        // .age
                        Instr::GetElementPointer {
                            dest: Register(3),
                            base: Register(1),
                            ty: person_struct_ty,
                            index: 0.into(),
                        },
                        Instr::Load {
                            dest: Register(4),
                            ty: IRType::Int,
                            addr: Register(3)
                        },
                        Instr::Ret(IRType::Int, Some(Register(4).into()))
                    ],
                }],
                env_ty: None,
                env_reg: None,
                size: 5
            },
        )
    }

    #[test]
    fn lowers_struct_method() {
        let lowered = lower(
            "
        struct Person {
            let age: Int

            init(age: Int) {
                self.age = age
            }

            func getAge() {
                self.age
            }
        }

        Person(age: 123).getAge()
        ",
        )
        .unwrap();

        let person_struct_ty = IRType::Struct(SymbolID::resolved(1), vec![IRType::Int], vec![]);
        let person_init_func_ty = IRType::Func(vec![IRType::Int], IRType::POINTER.into());

        assert_lowered_function!(
            lowered,
            format!("@_{}_Person_init", SymbolID::resolved(1).0),
            IRFunction {
                debug_info: Default::default(),
                ty: person_init_func_ty.clone(),
                name: format!("@_{}_Person_init", SymbolID::resolved(1).0),
                blocks: vec![BasicBlock {
                    id: BasicBlockID(0),
                    instructions: vec![
                        Instr::GetElementPointer {
                            dest: Register(2),
                            base: Register(0), // self is in register 0
                            ty: person_struct_ty.clone(),
                            index: 0.into(),
                        },
                        Instr::Store {
                            ty: IRType::Int,
                            val: Register(1).into(), // age is in register 1
                            location: Register(2)
                        },
                        Instr::Load {
                            ty: person_struct_ty.clone(),
                            dest: Register(3),
                            addr: Register(0)
                        },
                        // return self
                        Instr::Ret(person_struct_ty.clone(), Some(Register(3).into()))
                    ],
                }],
                env_ty: Some(person_struct_ty.clone()),
                env_reg: Some(Register(0),),
                size: 4
            }
        );
        assert_lowered_function!(
            lowered,
            format!("@_{}_Person_getAge", SymbolID::resolved(1).0),
            IRFunction {
                debug_info: Default::default(),
                ty: IRType::Func(vec![], IRType::Int.into()),
                name: format!("@_{}_Person_getAge", SymbolID::resolved(1).0),
                blocks: vec![BasicBlock {
                    id: BasicBlockID::ENTRY,
                    instructions: vec![
                        Instr::GetElementPointer {
                            dest: Register(1),
                            base: Register(0),
                            ty: person_struct_ty.clone(),
                            index: IRValue::ImmediateInt(0),
                        },
                        Instr::Load {
                            dest: Register(2),
                            ty: IRType::Int,
                            addr: Register(1),
                        },
                        Instr::Ret(IRType::Int, Some(Register(2).into())),
                    ],
                }],
                env_ty: Some(IRType::Struct(
                    SymbolID::resolved(1),
                    vec![IRType::Int],
                    vec![]
                )),
                env_reg: Some(Register(0)),
                size: 3,
            }
        );

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
                        Instr::ConstantInt(Register(0), 123),
                        Instr::Alloc {
                            dest: Register(1),
                            count: None,
                            ty: person_struct_ty.clone(),
                        },
                        Instr::Call {
                            dest_reg: Register(2),
                            ty: person_struct_ty.clone(),
                            callee: Callee::Name(format!(
                                "@_{}_Person_init",
                                SymbolID::resolved(1).0
                            )),
                            args: RegisterList(vec![
                                TypedRegister::new(IRType::POINTER, Register(1)),
                                TypedRegister::new(IRType::Int, Register(0)),
                            ]),
                        },
                        Instr::Call {
                            dest_reg: Register(3),
                            ty: IRType::Int,
                            callee: Callee::Name(format!(
                                "@_{}_Person_getAge",
                                SymbolID::resolved(1).0
                            )),
                            args: RegisterList(vec![TypedRegister::new(
                                IRType::POINTER,
                                Register(1),
                            )]),
                        },
                        Instr::Ret(IRType::Int, Some(Register(3).into())),
                    ],
                }],
                env_ty: None,
                env_reg: None,
                size: 4,
            },
        );
    }

    #[test]
    fn lowers_loop() {
        let lowered = lower(
            "
                loop {
                    123
                }
        ",
        )
        .unwrap();

        let expected = IRFunction {
            debug_info: Default::default(),
            ty: IRType::Func(vec![], IRType::Void.into()),
            name: "@main".into(),
            blocks: vec![
                BasicBlock {
                    id: BasicBlockID(0),
                    instructions: vec![Instr::Jump(BasicBlockID(1))],
                },
                // The entry to the loop
                BasicBlock {
                    id: BasicBlockID(1),
                    instructions: vec![
                        Instr::ConstantInt(Register(0), 123),
                        Instr::Jump(BasicBlockID(1)),
                    ],
                },
                BasicBlock {
                    id: BasicBlockID(2),
                    instructions: vec![Instr::Ret(IRType::Void, None)],
                },
                //
            ],
            env_ty: None,
            env_reg: None,
            size: 1,
        };

        assert_lowered_function!(lowered, "@main", expected);
    }

    #[test]
    fn lowers_break() {
        let lowered = lower(
            "
                loop {
                    break
                }
        ",
        )
        .unwrap();

        let expected = IRFunction {
            debug_info: Default::default(),
            ty: IRType::Func(vec![], IRType::Void.into()),
            name: "@main".into(),
            blocks: vec![
                BasicBlock {
                    id: BasicBlockID(0),
                    instructions: vec![Instr::Jump(BasicBlockID(1))],
                },
                // The entry to the loop
                BasicBlock {
                    id: BasicBlockID(1),
                    instructions: vec![
                        Instr::Jump(BasicBlockID(2)),
                        Instr::Jump(BasicBlockID(1)), // Still emit the original jump even tho it won't be used
                    ],
                },
                BasicBlock {
                    id: BasicBlockID(2),
                    instructions: vec![Instr::Ret(IRType::Void, None)],
                },
            ],
            env_ty: None,
            env_reg: None,
            size: 0,
        };

        assert_lowered_function!(lowered, "@main", expected);
    }

    #[test]
    fn lowers_loop_with_condition() {
        let lowered = lower(
            "
                let i = 123
                loop i > 456 {
                    789
                }
        ",
        )
        .unwrap();

        let expected = IRFunction {
            debug_info: Default::default(),
            ty: IRType::Func(vec![], IRType::Void.into()),
            name: "@main".into(),
            blocks: vec![
                BasicBlock {
                    id: BasicBlockID(0),
                    instructions: vec![
                        Instr::ConstantInt(Register(0), 123),
                        Instr::Jump(BasicBlockID(3)),
                    ],
                },
                // The body of the loop
                BasicBlock {
                    id: BasicBlockID(1),
                    instructions: vec![
                        Instr::ConstantInt(Register(3), 789),
                        Instr::Jump(BasicBlockID(3)),
                    ],
                },
                // The exit of the loop
                BasicBlock {
                    id: BasicBlockID(2),
                    instructions: vec![Instr::Ret(IRType::Void, None)],
                },
                // The condition for the loop
                BasicBlock {
                    id: BasicBlockID(3),
                    instructions: vec![
                        Instr::ConstantInt(Register(1), 456),
                        Instr::GreaterThan(Register(2), IRType::Int, Register(0), Register(1)),
                        Instr::Branch {
                            cond: Register(2),
                            true_target: BasicBlockID(1),
                            false_target: BasicBlockID(2),
                        },
                    ],
                },
            ],
            env_ty: None,
            env_reg: None,
            size: 4,
        };

        assert_lowered_function!(lowered, "@main", expected);
    }

    #[test]
    fn lowers_imported_func() {
        let mut symbols = HashMap::new();
        symbols.insert(
            "importedFunc".to_string(),
            ImportedSymbol {
                name: "importedFunc".to_string(),
                module: "Imported".to_string(),
                symbol: SymbolID(123123123),
                kind: ImportedSymbolKind::Function { index: 0 },
            },
        );

        let mut types = HashMap::new();
        types.insert(
            SymbolID(123123123),
            Ty::Func(vec![Ty::Int], Ty::Int.into(), vec![]),
        );

        let imported_func = IRFunction {
            ty: IRType::Func(vec![IRType::Int], IRType::Int.into()),
            name: "@_123123123_importedFunc".to_string(),
            blocks: vec![BasicBlock {
                id: BasicBlockID::ENTRY,
                instructions: vec![Instr::Ret(IRType::Int, Some(IRValue::ImmediateInt(123)))],
            }],
            env_ty: None,
            env_reg: None,
            size: 1,
            debug_info: Default::default(),
        };

        let lowered = lower_with_imports(
            vec![CompiledModule {
                module_name: "Imported".to_string(),
                symbols,
                types,
                ir_module: IRModule {
                    constants: vec![],
                    functions: vec![imported_func.clone()],
                },
            }],
            "
        import Imported

        importedFunc(123)
        ",
        )
        .unwrap();

        let foo_name = format!("@_{}_importedFunc", SymbolID::resolved(1).0,);

        let imported_renamed_fn = IRFunction {
            debug_info: Default::default(),
            ty: imported_func.ty.clone(),
            name: foo_name.clone(),
            blocks: imported_func.blocks.clone(),
            env_ty: None,
            env_reg: None,
            size: 1,
        };

        assert_lowered_function!(lowered, foo_name, imported_renamed_fn);
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
                        // Get the arg
                        Instr::ConstantInt(Register(0), 123),
                        Instr::Call {
                            dest_reg: Register(1),
                            ty: IRType::Int,
                            callee: Callee::Name(foo_name),
                            args: RegisterList(vec![TypedRegister::new(IRType::Int, Register(0))]),
                        },
                        // 4. Return the result of the call.
                        Instr::Ret(IRType::Int, Some(Register(1).into()))
                    ],
                }],
                env_ty: None,
                env_reg: None,
                size: 2
            },
        );
    }
}

#[cfg(test)]
mod protocol_lowering_tests {
    use crate::{
        SymbolID, assert_lowered_function,
        lowering::{
            instr::{Callee, Instr},
            ir_function::IRFunction,
            ir_type::IRType,
            ir_value::IRValue,
            lowerer::{BasicBlock, BasicBlockID, RefKind, RegisterList, TypedRegister},
            lowerer_tests::helpers::lower_without_prelude_with_env,
            register::Register,
        },
    };

    #[test]
    fn lowers_protocol_method_call() {
        let (lowered, _) = lower_without_prelude_with_env(
            "
            protocol Aged {
                func getAge() -> Int
            }

            struct Person: Aged {
                func getAge() {
                    123
                }
            }

            struct Cat: Aged {
                func getAge() {
                    123
                }
            }

            func get<T: Aged>(t: T) {
                t.getAge()
            }

            get(Person())
            get(Cat())
        ",
        )
        .unwrap();

        let person_struct = IRType::Struct(SymbolID(4), vec![], vec![]);
        let cat_struct = IRType::Struct(SymbolID(6), vec![], vec![]);

        assert_lowered_function!(
            lowered,
            "@main",
            IRFunction {
                debug_info: Default::default(),
                ty: IRType::Func(vec![], IRType::Void.into()),
                name: "@main".into(),
                blocks: vec![BasicBlock {
                    id: BasicBlockID::ENTRY,
                    instructions: vec![
                        Instr::Ref(
                            Register(0),
                            IRType::Func(vec![IRType::TypeVar("T15".into())], IRType::Int.into()),
                            RefKind::Func("@_3_get".into())
                        ),
                        Instr::Alloc {
                            dest: Register(1),
                            ty: person_struct.clone(),
                            count: None
                        },
                        Instr::Call {
                            dest_reg: Register(2),
                            ty: person_struct.clone(),
                            callee: Callee::Name("@_4_Person_init".into()),
                            args: RegisterList(vec![TypedRegister::new(
                                IRType::POINTER,
                                Register(1)
                            )])
                        },
                        Instr::Call {
                            dest_reg: Register(3),
                            ty: IRType::Int,
                            callee: Callee::Name("@_3_get".into()),
                            args: RegisterList(vec![TypedRegister::new(
                                person_struct.clone(),
                                Register(1)
                            )])
                        },
                        Instr::Alloc {
                            dest: Register(4),
                            ty: cat_struct.clone(),
                            count: None
                        },
                        Instr::Call {
                            dest_reg: Register(5),
                            ty: cat_struct.clone(),
                            callee: Callee::Name("@_6_Cat_init".into()),
                            args: RegisterList(vec![TypedRegister::new(
                                IRType::POINTER,
                                Register(4)
                            )])
                        },
                        Instr::Call {
                            dest_reg: Register(6),
                            ty: IRType::Int,
                            callee: Callee::Name("@_3_get".into()),
                            args: RegisterList(vec![TypedRegister::new(
                                cat_struct.clone(),
                                Register(4)
                            )])
                        },
                        Instr::Ret(IRType::Int, Some(IRValue::Register(Register(6))))
                    ]
                }],
                env_ty: None,
                env_reg: None,
                size: 7,
            }
        );
    }
}
