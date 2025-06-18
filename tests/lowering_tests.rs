#[cfg(test)]
pub mod lowering_tests {
    use talk::{
        SymbolID, assert_lowered_functions,
        compiling::driver::Driver,
        lowering::{
            instr::{Callee, Instr},
            ir_error::IRError,
            ir_module::IRModule,
            ir_type::IRType,
            lowerer::{
                BasicBlock, BasicBlockID, IRFunction, PhiPredecessors, RefKind, RegisterList,
            },
            register::Register,
        },
    };

    fn lower(input: &'static str) -> Result<IRModule, IRError> {
        let mut driver = Driver::with_str(input);
        let typed = driver.units[0]
            .parse()
            .resolved(&mut driver.symbol_table)
            .typed(&mut driver.symbol_table)
            .lower(&mut driver.symbol_table);

        Ok(typed.module())
    }

    #[test]
    fn lowers_nested_function() {
        let lowered = lower("func foo() { 123 }").unwrap();

        // Define the types we'll be using to make the test cleaner
        let foo_func_type = IRType::Func(vec![], Box::new(IRType::Int));

        assert_lowered_functions!(
            lowered,
            vec![
                IRFunction {
                    ty: foo_func_type.clone(),
                    name: format!("@_{}_foo", SymbolID::resolved(1).0),
                    blocks: vec![BasicBlock {
                        id: BasicBlockID(0),
                        instructions: vec![
                            Instr::ConstantInt(Register(1), 123),
                            Instr::Ret(IRType::Int, Some(Register(1)))
                        ],
                    }],
                    env_ty: IRType::Struct(SymbolID::ENV, vec![]),
                    env_reg: Register(0)
                },
                IRFunction {
                    ty: IRType::Func(vec![], IRType::Void.into()),
                    name: "@main".into(),
                    blocks: vec![BasicBlock {
                        id: BasicBlockID(0),
                        instructions: vec![
                            Instr::Alloc {
                                dest: Register(1),
                                ty: IRType::closure(),
                                count: None
                            },
                            Instr::MakeStruct {
                                dest: Register(2),
                                ty: IRType::EMPTY_STRUCT,
                                values: RegisterList::EMPTY
                            },
                            Instr::Alloc {
                                dest: Register(3),
                                ty: IRType::EMPTY_STRUCT,
                                count: None,
                            },
                            Instr::Store {
                                val: Register(2),
                                location: Register(3),
                                ty: IRType::EMPTY_STRUCT
                            },
                            Instr::Ref(
                                Register(4),
                                foo_func_type.clone(),
                                RefKind::Func(format!("@_{}_foo", SymbolID::resolved(1).0))
                            ),
                            Instr::GetElementPointer {
                                dest: Register(5),
                                base: Register(1),
                                index: 1,
                                ty: IRType::closure()
                            },
                            Instr::GetElementPointer {
                                dest: Register(6),
                                base: Register(1),
                                index: 0,
                                ty: IRType::closure()
                            },
                            Instr::Store {
                                val: Register(3),
                                location: Register(5),
                                ty: IRType::Pointer
                            },
                            Instr::Store {
                                val: Register(4),
                                location: Register(6),
                                ty: IRType::Pointer
                            },
                            Instr::Ret(IRType::Pointer, Some(Register(1))),
                        ],
                    }],
                    env_ty: IRType::Struct(SymbolID::ENV, vec![]),
                    env_reg: Register(0)
                },
            ]
        )
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

        assert_lowered_functions!(
            lowered,
            vec![
                IRFunction {
                    ty: IRType::Func(
                        vec![IRType::TypeVar("T3".into())],
                        Box::new(IRType::TypeVar("T4".into()))
                    ),
                    name: format!("@_{}_foo", SymbolID::resolved(1).0),
                    blocks: vec![BasicBlock {
                        id: BasicBlockID(0),
                        instructions: vec![
                            Instr::GetElementPointer {
                                dest: Register(2),
                                base: Register(0),
                                ty: IRType::closure(),
                                index: 0
                            },
                            Instr::Load {
                                dest: Register(3),
                                ty: IRType::Pointer,
                                addr: Register(2)
                            },
                            Instr::GetElementPointer {
                                dest: Register(4),
                                base: Register(3),
                                ty: IRType::closure(),
                                index: 0
                            },
                            Instr::Load {
                                dest: Register(5),
                                ty: IRType::Func(
                                    vec![IRType::TypeVar("T3".into())],
                                    IRType::TypeVar("T4".into()).into()
                                ),
                                addr: Register(4)
                            },
                            Instr::GetElementPointer {
                                dest: Register(6),
                                base: Register(3),
                                ty: IRType::closure(),
                                index: 1
                            },
                            Instr::Load {
                                dest: Register(7),
                                ty: IRType::Pointer,
                                addr: Register(6)
                            },
                            Instr::Call {
                                dest_reg: Register(8),
                                ty: IRType::TypeVar("T4".into()),
                                callee: Callee::Register(Register(5)),
                                args: RegisterList(vec![Register(7), Register(1)])
                            },
                            // The `return x` becomes a Ret instruction using the argument register.
                            // In our calling convention, the env is %0, so x is %1.
                            Instr::Ret(IRType::TypeVar("T4".into()), Some(Register(8))),
                        ],
                    }],
                    env_ty: IRType::Struct(SymbolID::ENV, vec![IRType::Pointer]),
                    env_reg: Register(0)
                },
                IRFunction {
                    ty: IRType::Func(vec![], IRType::Void.into()),
                    name: "@main".into(),
                    blocks: vec![BasicBlock {
                        id: BasicBlockID(0),
                        instructions: vec![
                            Instr::Alloc {
                                dest: Register(1),
                                ty: IRType::closure(),
                                count: None,
                            },
                            Instr::MakeStruct {
                                dest: Register(2),
                                ty: IRType::Struct(SymbolID(0), vec![IRType::Pointer]),
                                values: RegisterList(vec![Register(1)])
                            },
                            Instr::Alloc {
                                dest: Register(3),
                                count: None,
                                ty: IRType::Struct(SymbolID(0), vec![IRType::Pointer]),
                            },
                            Instr::Store {
                                val: Register(2),
                                location: Register(3),
                                ty: IRType::Struct(SymbolID(0), vec![IRType::Pointer]),
                            },
                            Instr::Ref(
                                Register(4),
                                IRType::Func(
                                    vec![IRType::TypeVar("T3".into())],
                                    IRType::TypeVar("T4".into()).into()
                                ),
                                RefKind::Func(format!("@_{}_foo", SymbolID::resolved(1).0))
                            ),
                            Instr::GetElementPointer {
                                dest: Register(5),
                                base: Register(1),
                                index: 1,
                                ty: IRType::closure()
                            },
                            Instr::GetElementPointer {
                                dest: Register(6),
                                base: Register(1),
                                index: 0,
                                ty: IRType::closure()
                            },
                            Instr::Store {
                                val: Register(3),
                                location: Register(5),
                                ty: IRType::Pointer
                            },
                            Instr::Store {
                                val: Register(4),
                                location: Register(6),
                                ty: IRType::Pointer
                            },
                            Instr::Ret(IRType::Pointer, Some(Register(1))),
                        ],
                    }],
                    env_ty: IRType::Struct(SymbolID::ENV, vec![]),
                    env_reg: Register(0)
                },
            ]
        )
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

        assert_lowered_functions!(
            lowered,
            vec![
                IRFunction {
                    ty: foo_func_type.clone(),
                    name: foo_name.clone(),
                    blocks: vec![BasicBlock {
                        id: BasicBlockID(0),
                        instructions: vec![
                            // The `return x` becomes a Ret instruction using the argument register.
                            // In our calling convention, the env is %0, so x is %1.
                            Instr::Ret(IRType::Int, Some(Register(1))),
                            // The `123` is dead code but is still lowered.
                            Instr::ConstantInt(Register(2), 123),
                            // The implicit return is still added
                            Instr::Ret(IRType::Int, Some(Register(2)))
                        ],
                    }],
                    env_ty: IRType::Struct(SymbolID::ENV, vec![]),
                    env_reg: Register(0)
                },
                IRFunction {
                    ty: IRType::Func(vec![], IRType::Void.into()),
                    name: "@main".into(),
                    blocks: vec![BasicBlock {
                        id: BasicBlockID(0),
                        instructions: vec![
                            Instr::Alloc {
                                dest: Register(1),
                                count: None,
                                ty: IRType::closure()
                            },
                            // This sequence is now identical to your working test case.
                            Instr::MakeStruct {
                                dest: Register(2),
                                ty: IRType::EMPTY_STRUCT,
                                values: RegisterList::EMPTY
                            },
                            Instr::Alloc {
                                dest: Register(3),
                                count: None,
                                ty: IRType::EMPTY_STRUCT
                            },
                            Instr::Store {
                                val: Register(2),
                                location: Register(3),
                                ty: IRType::EMPTY_STRUCT
                            },
                            Instr::Ref(Register(4), foo_func_type.clone(), RefKind::Func(foo_name)),
                            Instr::GetElementPointer {
                                dest: Register(5),
                                base: Register(1),
                                index: 1,
                                ty: IRType::closure()
                            },
                            Instr::GetElementPointer {
                                dest: Register(6),
                                base: Register(1),
                                index: 0,
                                ty: IRType::closure()
                            },
                            Instr::Store {
                                val: Register(3),
                                location: Register(5),
                                ty: IRType::Pointer
                            },
                            Instr::Store {
                                val: Register(4),
                                location: Register(6),
                                ty: IRType::Pointer
                            },
                            Instr::Ret(IRType::Pointer, Some(Register(1))),
                        ],
                    }],
                    env_ty: IRType::Struct(SymbolID::ENV, vec![]),
                    env_reg: Register(0)
                },
            ]
        )
    }

    #[test]
    fn lowers_calls() {
        let lowered = lower("func foo(x) { x }\nfoo(123)").unwrap();

        let foo_func_type = IRType::Func(
            vec![IRType::TypeVar("T3".into())],
            Box::new(IRType::TypeVar("T3".into())),
        );

        let foo_name = format!("@_{}_foo", SymbolID::resolved(1).0);

        assert_lowered_functions!(
            lowered,
            vec![
                IRFunction {
                    ty: foo_func_type.clone(),
                    name: foo_name.clone(),
                    blocks: vec![BasicBlock {
                        id: BasicBlockID(0),
                        instructions: vec![Instr::Ret(
                            IRType::TypeVar("T3".into()),
                            Some(Register(1))
                        )],
                    }],
                    env_ty: IRType::Struct(SymbolID::ENV, vec![]),
                    env_reg: Register(0)
                },
                IRFunction {
                    ty: IRType::Func(vec![], IRType::Void.into()),
                    name: "@main".into(),
                    blocks: vec![BasicBlock {
                        id: BasicBlockID(0),
                        instructions: vec![
                            Instr::Alloc {
                                dest: Register(1),
                                count: None,
                                ty: IRType::closure()
                            },
                            Instr::MakeStruct {
                                dest: Register(2),
                                ty: IRType::EMPTY_STRUCT,
                                values: RegisterList::EMPTY
                            },
                            Instr::Alloc {
                                dest: Register(3),
                                count: None,
                                ty: IRType::EMPTY_STRUCT
                            },
                            Instr::Store {
                                val: Register(2),
                                location: Register(3),
                                ty: IRType::EMPTY_STRUCT
                            },
                            Instr::Ref(Register(4), foo_func_type.clone(), RefKind::Func(foo_name)),
                            Instr::GetElementPointer {
                                dest: Register(5),
                                base: Register(1),
                                index: 1,
                                ty: IRType::closure()
                            },
                            Instr::GetElementPointer {
                                dest: Register(6),
                                base: Register(1),
                                index: 0,
                                ty: IRType::closure()
                            },
                            Instr::Store {
                                val: Register(3),
                                location: Register(5),
                                ty: IRType::Pointer
                            },
                            Instr::Store {
                                val: Register(4),
                                location: Register(6),
                                ty: IRType::Pointer
                            },
                            // %4 now holds the pointer to the `foo` closure.

                            // === Part 2: Call the closure ===

                            // 1. Prepare the explicit argument(s).
                            Instr::ConstantInt(Register(7), 123),
                            // 2. Unpack the closure object from %4.
                            // You need to introduce a Load instruction here.
                            Instr::GetElementPointer {
                                dest: Register(8),
                                base: Register(1),
                                index: 0,
                                ty: IRType::closure()
                            },
                            Instr::Load {
                                dest: Register(9),
                                ty: IRType::Func(vec![IRType::Int], IRType::Int.into()),
                                addr: Register(8)
                            }, // Load the func_ptr
                            Instr::GetElementPointer {
                                dest: Register(10),
                                base: Register(1),
                                index: 1,
                                ty: IRType::closure()
                            },
                            Instr::Load {
                                dest: Register(11),
                                ty: IRType::Pointer,
                                addr: Register(10)
                            }, // Load the env_ptr
                            // 3. Make the indirect call.
                            Instr::Call {
                                dest_reg: Register(12),
                                ty: IRType::Int,
                                callee: Register(9).into(), // The loaded function pointer
                                args: RegisterList(vec![Register(11), Register(7)]), // (env_ptr, arg)
                            },
                            // 4. Return the result of the call.
                            Instr::Ret(IRType::Int, Some(Register(12)))
                        ],
                    }],
                    env_ty: IRType::Struct(SymbolID::ENV, vec![]),
                    env_reg: Register(0)
                },
            ]
        )
    }

    #[test]
    fn lowers_func_with_params() {
        let lowered = lower("func foo(x) { x }").unwrap();
        assert_lowered_functions!(
            lowered,
            vec![
                IRFunction {
                    ty: IRType::Func(
                        vec![IRType::TypeVar("T3".into())],
                        IRType::TypeVar("T3".into()).into()
                    ),
                    name: format!("@_{}_foo", SymbolID::resolved(1).0),
                    blocks: vec![BasicBlock {
                        id: BasicBlockID(0),
                        instructions: vec![Instr::Ret(
                            IRType::TypeVar("T3".into()),
                            Some(Register(1))
                        )],
                    }],
                    env_ty: IRType::Struct(SymbolID::ENV, vec![]),
                    env_reg: Register(0)
                },
                IRFunction {
                    ty: IRType::Func(vec![], IRType::Void.into()),
                    name: "@main".into(),
                    blocks: vec![BasicBlock {
                        id: BasicBlockID(0),
                        instructions: vec![
                            // Alloc the closure
                            Instr::Alloc {
                                dest: Register(1),
                                count: None,
                                ty: IRType::closure()
                            },
                            // Create the env
                            Instr::MakeStruct {
                                dest: Register(2),
                                ty: IRType::EMPTY_STRUCT,
                                values: RegisterList::EMPTY
                            },
                            // Alloc space for it
                            Instr::Alloc {
                                dest: Register(3),
                                count: None,
                                ty: IRType::EMPTY_STRUCT,
                            },
                            // Store the env
                            Instr::Store {
                                ty: IRType::EMPTY_STRUCT,
                                val: Register(2),
                                location: Register(3)
                            },
                            // Get the fn
                            Instr::Ref(
                                Register(4),
                                IRType::Func(
                                    vec![IRType::TypeVar("T3".into())],
                                    IRType::TypeVar("T3".into()).into()
                                ),
                                RefKind::Func(format!("@_{}_foo", SymbolID::resolved(1).0))
                            ),
                            // Get a pointer to the env's address in the closure
                            Instr::GetElementPointer {
                                dest: Register(5),
                                base: Register(1),
                                ty: IRType::closure(),
                                index: 1
                            },
                            // Get a pointer to the fn's address in the closure
                            Instr::GetElementPointer {
                                dest: Register(6),
                                base: Register(1),
                                ty: IRType::closure(),
                                index: 0
                            },
                            // Store the env into the closure
                            Instr::Store {
                                ty: IRType::Pointer,
                                val: Register(3),
                                location: Register(5)
                            },
                            // Store the fn into the closure
                            Instr::Store {
                                ty: IRType::Pointer,
                                val: Register(4),
                                location: Register(6)
                            },
                            // Return a pointer to the closure
                            Instr::Ret(IRType::Pointer, Some(Register(1)))
                        ],
                    }],
                    env_ty: IRType::Struct(SymbolID::ENV, vec![]),
                    env_reg: Register(0)
                },
            ]
        )
    }

    #[test]
    fn lowers_int() {
        let lowered = lower("123").unwrap();
        assert_lowered_functions!(
            lowered,
            vec![IRFunction {
                ty: IRType::Func(vec![], IRType::Void.into()),
                name: "@main".into(),
                blocks: vec![BasicBlock {
                    id: BasicBlockID(0),
                    instructions: vec![
                        Instr::ConstantInt(Register(1), 123),
                        Instr::Ret(IRType::Int, Some(Register(1)))
                    ],
                }],
                env_ty: IRType::Struct(SymbolID::ENV, vec![]),
                env_reg: Register(0)
            }]
        )
    }

    #[test]
    fn lowers_float() {
        let lowered = lower("123.").unwrap();
        assert_lowered_functions!(
            lowered,
            vec![IRFunction {
                ty: IRType::Func(vec![], IRType::Void.into()),
                name: "@main".into(),
                blocks: vec![BasicBlock {
                    id: BasicBlockID(0),
                    instructions: vec![
                        Instr::ConstantFloat(Register(1), 123.),
                        Instr::Ret(IRType::Float, Some(Register(1)))
                    ],
                }],
                env_ty: IRType::Struct(SymbolID::ENV, vec![]),
                env_reg: Register(0),
            }],
        )
    }

    #[test]
    fn lowers_bools() {
        let lowered = lower("true\nfalse").unwrap();
        assert_lowered_functions!(
            lowered,
            vec![IRFunction {
                ty: IRType::Func(vec![], IRType::Void.into()),
                name: "@main".into(),
                blocks: vec![BasicBlock {
                    id: BasicBlockID(0),
                    instructions: vec![
                        Instr::ConstantBool(Register(1), true),
                        Instr::ConstantBool(Register(2), false),
                        Instr::Ret(IRType::Bool, Some(Register(2))),
                    ],
                }],
                env_ty: IRType::Struct(SymbolID::ENV, vec![]),
                env_reg: Register(0),
            }]
        )
    }

    #[test]
    fn lowers_add() {
        let lowered = lower("1 + 2").unwrap();
        assert_lowered_functions!(
            lowered,
            vec![IRFunction {
                ty: IRType::Func(vec![], IRType::Void.into()),
                name: "@main".into(),
                blocks: vec![BasicBlock {
                    id: BasicBlockID(0),
                    instructions: vec![
                        Instr::ConstantInt(Register(1), 1),
                        Instr::ConstantInt(Register(2), 2),
                        Instr::Add(Register(3), IRType::Int, Register(1), Register(2)),
                        Instr::Ret(IRType::Int, Some(Register(3)))
                    ],
                }],
                env_ty: IRType::Struct(SymbolID::ENV, vec![]),
                env_reg: Register(0),
            }]
        )
    }

    #[test]
    fn lowers_sub() {
        let lowered = lower("2 - 1").unwrap();
        assert_lowered_functions!(
            lowered,
            vec![IRFunction {
                ty: IRType::Func(vec![], IRType::Void.into()),
                name: "@main".into(),
                blocks: vec![BasicBlock {
                    id: BasicBlockID(0),
                    instructions: vec![
                        Instr::ConstantInt(Register(1), 2),
                        Instr::ConstantInt(Register(2), 1),
                        Instr::Sub(Register(3), IRType::Int, Register(1), Register(2)),
                        Instr::Ret(IRType::Int, Some(Register(3)))
                    ],
                }],
                env_ty: IRType::Struct(SymbolID::ENV, vec![]),
                env_reg: Register(0),
            }],
        )
    }

    #[test]
    fn lowers_mul() {
        let lowered = lower("2 * 1").unwrap();
        assert_lowered_functions!(
            lowered,
            vec![IRFunction {
                ty: IRType::Func(vec![], IRType::Void.into()),
                name: "@main".into(),
                blocks: vec![BasicBlock {
                    id: BasicBlockID(0),
                    instructions: vec![
                        Instr::ConstantInt(Register(1), 2),
                        Instr::ConstantInt(Register(2), 1),
                        Instr::Mul(Register(3), IRType::Int, Register(1), Register(2)),
                        Instr::Ret(IRType::Int, Some(Register(3)))
                    ],
                }],
                env_ty: IRType::Struct(SymbolID::ENV, vec![]),
                env_reg: Register(0),
            }]
        )
    }

    #[test]
    fn lowers_div() {
        let lowered = lower("2 / 1").unwrap();
        assert_lowered_functions!(
            lowered,
            vec![IRFunction {
                ty: IRType::Func(vec![], IRType::Void.into()),
                name: "@main".into(),
                blocks: vec![BasicBlock {
                    id: BasicBlockID(0),
                    instructions: vec![
                        Instr::ConstantInt(Register(1), 2),
                        Instr::ConstantInt(Register(2), 1),
                        Instr::Div(Register(3), IRType::Int, Register(1), Register(2)),
                        Instr::Ret(IRType::Int, Some(Register(3)))
                    ],
                }],
                env_ty: IRType::Struct(SymbolID::ENV, vec![]),
                env_reg: Register(0),
            }]
        )
    }

    #[test]
    fn lowers_assignment() {
        let lowered = lower("let a = 123\na").unwrap();
        assert_lowered_functions!(
            lowered,
            vec![IRFunction {
                ty: IRType::Func(vec![], IRType::Void.into()),
                name: "@main".into(),
                blocks: vec![BasicBlock {
                    id: BasicBlockID(0),
                    instructions: vec![
                        Instr::ConstantInt(Register(1), 123),
                        Instr::Ret(IRType::Int, Some(Register(1))),
                    ],
                }],
                env_ty: IRType::Struct(SymbolID::ENV, vec![]),
                env_reg: Register(0),
            }]
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

        let expected = vec![IRFunction {
            ty: IRType::Func(vec![], IRType::Void.into()),
            name: "@main".into(),
            blocks: vec![
                // if block
                BasicBlock {
                    id: BasicBlockID(0),
                    instructions: vec![
                        Instr::ConstantBool(Register(1), true),
                        Instr::Branch {
                            cond: Register(1),
                            true_target: BasicBlockID(1),
                            false_target: BasicBlockID(2),
                        },
                    ],
                },
                // if block
                BasicBlock {
                    id: BasicBlockID(1),
                    instructions: vec![
                        Instr::ConstantInt(Register(2), 123),
                        Instr::Jump(BasicBlockID(3)),
                    ],
                },
                // else block
                BasicBlock {
                    id: BasicBlockID(2),
                    instructions: vec![
                        Instr::ConstantInt(Register(3), 456),
                        Instr::Jump(BasicBlockID(3)),
                    ],
                },
                // converge block
                BasicBlock {
                    id: BasicBlockID(3),
                    instructions: vec![
                        Instr::Phi(
                            Register(4),
                            IRType::Int,
                            PhiPredecessors(vec![
                                (Register(2), BasicBlockID(1)),
                                (Register(3), BasicBlockID(2)),
                            ]),
                        ),
                        Instr::ConstantInt(Register(5), 789),
                        Instr::Ret(IRType::Int, Some(Register(5))),
                    ],
                },
            ],
            env_ty: IRType::Struct(SymbolID::ENV, vec![]),
            env_reg: Register(0),
        }];

        assert_lowered_functions!(lowered, expected,);
    }

    #[test]
    fn lowers_basic_enum() {
        let lowered = lower(
            "enum Foo {
                    case fizz, buzz
                }
                
                Foo.buzz",
        )
        .unwrap();
        assert_lowered_functions!(
            lowered,
            vec![IRFunction {
                ty: IRType::Func(vec![], IRType::Void.into()),
                name: "@main".into(),
                blocks: vec![BasicBlock {
                    id: BasicBlockID(0),
                    instructions: vec![
                        Instr::TagVariant(Register(1), IRType::Enum(vec![]), 1, vec![].into()),
                        Instr::Ret(IRType::Enum(vec![]), Some(Register(1)))
                    ],
                }],
                env_ty: IRType::Struct(SymbolID::ENV, vec![]),
                env_reg: Register(0)
            }]
        )
    }

    #[test]
    fn lowers_builtin_optional() {
        let lowered = lower("Optional.some(123)").unwrap();
        assert_lowered_functions!(
            lowered,
            vec![IRFunction {
                ty: IRType::Func(vec![], IRType::Void.into()),
                name: "@main".into(),
                blocks: vec![BasicBlock {
                    id: BasicBlockID(0),
                    instructions: vec![
                        Instr::ConstantInt(Register(1), 123),
                        Instr::TagVariant(
                            Register(2),
                            IRType::Enum(vec![IRType::Int]),
                            0,
                            RegisterList(vec![Register(1)])
                        ),
                        Instr::Ret(IRType::Enum(vec![IRType::Int]), Some(Register(2)))
                    ],
                }],
                env_ty: IRType::Struct(SymbolID::ENV, vec![]),
                env_reg: Register(0)
            }]
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

        assert_lowered_functions!(
            lowered,
            vec![IRFunction {
                ty: IRType::Func(vec![], IRType::Void.into()),
                name: "@main".into(),
                blocks: vec![
                    BasicBlock {
                        id: BasicBlockID::ENTRY,
                        instructions: vec![
                            Instr::ConstantInt(Register(1), 123),
                            Instr::Jump(BasicBlockID(2))
                        ],
                    },
                    BasicBlock {
                        id: BasicBlockID(1),
                        instructions: vec![
                            Instr::Phi(
                                Register(8),
                                IRType::Float,
                                PhiPredecessors(vec![
                                    (Register(4), BasicBlockID(5)),
                                    (Register(7), BasicBlockID(6))
                                ])
                            ),
                            Instr::Ret(IRType::Float, Some(Register(8)))
                        ]
                    },
                    BasicBlock {
                        id: BasicBlockID(2),
                        instructions: vec![
                            Instr::ConstantInt(Register(2), 123),
                            Instr::Eq(Register(3), IRType::Int, Register(1), Register(2)),
                            Instr::Branch {
                                cond: Register(3),
                                true_target: BasicBlockID(5),
                                false_target: BasicBlockID(3)
                            },
                        ]
                    },
                    BasicBlock {
                        id: BasicBlockID(3),
                        instructions: vec![
                            Instr::ConstantInt(Register(5), 456),
                            Instr::Eq(Register(6), IRType::Int, Register(1), Register(5)),
                            Instr::Branch {
                                cond: Register(6),
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
                            Instr::ConstantFloat(Register(4), 3.14),
                            Instr::Jump(BasicBlockID(1))
                        ]
                    },
                    BasicBlock {
                        id: BasicBlockID(6),
                        instructions: vec![
                            Instr::ConstantFloat(Register(7), 2.71),
                            Instr::Jump(BasicBlockID(1))
                        ]
                    },
                ],
                env_ty: IRType::Struct(SymbolID::ENV, vec![]),
                env_reg: Register(0),
            }]
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

        assert_lowered_functions!(
            lowered,
            vec![IRFunction {
                ty: IRType::Func(vec![], IRType::Void.into()),
                name: "@main".into(),
                blocks: vec![
                    // Block 0: Dispatch
                    BasicBlock {
                        id: BasicBlockID::ENTRY,
                        instructions: vec![
                            // Scrutinee: Optional.some(123)
                            Instr::ConstantInt(Register(1), 123),
                            Instr::TagVariant(
                                Register(2),
                                IRType::Enum(vec![IRType::Int]),
                                0,
                                RegisterList(vec![Register(1)])
                            ),
                            Instr::Jump(BasicBlockID(2)),
                        ],
                    },
                    // Block 1: Merge Point
                    BasicBlock {
                        id: BasicBlockID(1),
                        instructions: vec![
                            Instr::Phi(
                                Register(11),
                                IRType::Int,
                                PhiPredecessors(vec![
                                    (Register(6), BasicBlockID(5)),  // from .some arm
                                    (Register(10), BasicBlockID(6)), // from .none arm
                                ])
                            ),
                            Instr::Ret(IRType::Int, Some(Register(11))),
                        ]
                    },
                    BasicBlock {
                        id: BasicBlockID(2),
                        instructions: vec![
                            Instr::GetEnumTag(Register(3), Register(2)),
                            Instr::ConstantInt(Register(4), 0), // Tag for .some
                            Instr::Eq(Register(5), IRType::Int, Register(3), Register(4)),
                            Instr::Branch {
                                cond: Register(5),
                                true_target: BasicBlockID(5),
                                false_target: BasicBlockID(3)
                            },
                        ]
                    },
                    // Pattern 2
                    BasicBlock {
                        id: BasicBlockID(3),
                        instructions: vec![
                            Instr::GetEnumTag(Register(7), Register(2)),
                            Instr::ConstantInt(Register(8), 1), // Tag for .none
                            Instr::Eq(Register(9), IRType::Int, Register(7), Register(8)),
                            Instr::Branch {
                                cond: Register(9),
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
                            Instr::GetEnumValue(Register(6), IRType::Int, Register(2), 0, 0),
                            Instr::Jump(BasicBlockID(1)),
                        ]
                    },
                    // Block 2: Body for .some(x) -> x
                    BasicBlock {
                        id: BasicBlockID(6),
                        instructions: vec![
                            Instr::ConstantInt(Register(10), 456),
                            Instr::Jump(BasicBlockID(1)),
                        ]
                    },
                ],
                env_ty: IRType::Struct(SymbolID::ENV, vec![]),
                env_reg: Register(0),
            }]
        )
    }

    #[test]
    fn lowers_enum_match() {
        let lowered = lower(
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
        assert_lowered_functions!(
            lowered,
            vec![IRFunction {
                ty: IRType::Func(vec![], IRType::Void.into()),
                name: "@main".into(),
                blocks: vec![
                    BasicBlock {
                        id: BasicBlockID(0,),
                        instructions: vec![
                            TagVariant(
                                Register(1,),
                                IRType::Enum(vec![],),
                                1,
                                RegisterList(vec![],),
                            ),
                            Jump(BasicBlockID(2,),),
                        ],
                    },
                    BasicBlock {
                        id: BasicBlockID(1,),
                        instructions: vec![
                            Phi(
                                Register(10,),
                                IRType::Int,
                                PhiPredecessors(vec![
                                    (Register(5,), BasicBlockID(5,),),
                                    (Register(9,), BasicBlockID(6,),),
                                ],),
                            ),
                            Ret(IRType::Int, Some(Register(10,),),),
                        ],
                    },
                    BasicBlock {
                        id: BasicBlockID(2,),
                        instructions: vec![
                            GetEnumTag(Register(2,), Register(1,),),
                            ConstantInt(Register(3,), 0,),
                            Eq(Register(4,), IRType::Int, Register(2,), Register(3,),),
                            Branch {
                                cond: Register(4,),
                                true_target: BasicBlockID(5,),
                                false_target: BasicBlockID(3,),
                            },
                        ],
                    },
                    BasicBlock {
                        id: BasicBlockID(3,),
                        instructions: vec![
                            GetEnumTag(Register(6,), Register(1,),),
                            ConstantInt(Register(7,), 1,),
                            Eq(Register(8,), IRType::Int, Register(6,), Register(7,),),
                            Branch {
                                cond: Register(8,),
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
                            ConstantInt(Register(5,), 123,),
                            Jump(BasicBlockID(1,),),
                        ],
                    },
                    BasicBlock {
                        id: BasicBlockID(6,),
                        instructions: vec![
                            ConstantInt(Register(9,), 456,),
                            Jump(BasicBlockID(1,),),
                        ],
                    },
                ],
                env_ty: IRType::Struct(SymbolID(-2147483647,), vec![],),
                env_reg: Register(0,),
            },]
        )
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
        let env_struct_type = IRType::Struct(SymbolID(0), vec![IRType::Int]);

        assert_lowered_functions!(
            lowered,
            vec![
                IRFunction {
                    ty: add_func_type.clone(),
                    name: format!("@_{}_add", SymbolID::resolved(1).0),
                    blocks: vec![BasicBlock {
                        id: BasicBlockID(0),
                        instructions: vec![
                            Instr::GetElementPointer {
                                dest: Register(2),
                                ty: IRType::closure(),
                                base: Register(0),
                                index: 0
                            },
                            Instr::Load {
                                dest: Register(3),
                                ty: IRType::Int,
                                addr: Register(2)
                            },
                            Instr::Add(Register(4), IRType::Int, Register(3), Register(1)),
                            Instr::Ret(IRType::Int, Some(Register(4))),
                        ],
                    }],
                    env_ty: IRType::Struct(SymbolID::ENV, vec![IRType::Int]),
                    env_reg: Register(0)
                },
                IRFunction {
                    ty: IRType::Func(vec![], IRType::Void.into()),
                    name: "@main".into(),
                    blocks: vec![BasicBlock {
                        id: BasicBlockID(0),
                        instructions: vec![
                            // === Part 1: Setup `let x = 1` and environment ===
                            // The environment struct now holds the VALUE of x, not a pointer.
                            Instr::ConstantInt(Register(1), 1),
                            Instr::Alloc {
                                dest: Register(2),
                                count: None,
                                ty: IRType::closure()
                            },
                            Instr::MakeStruct {
                                dest: Register(3),
                                ty: env_struct_type.clone(),
                                values: RegisterList(vec![Register(1)])
                            },
                            Instr::Alloc {
                                dest: Register(4),
                                count: None,
                                ty: env_struct_type.clone()
                            },
                            Instr::Store {
                                val: Register(3),
                                location: Register(4),
                                ty: env_struct_type.clone()
                            },
                            Instr::Ref(
                                Register(5),
                                add_func_type.clone(),
                                RefKind::Func(format!("@_{}_add", SymbolID::resolved(1).0))
                            ),
                            Instr::GetElementPointer {
                                dest: Register(6),
                                base: Register(2),
                                index: 1,
                                ty: IRType::closure()
                            },
                            Instr::GetElementPointer {
                                dest: Register(7),
                                base: Register(2),
                                index: 0,
                                ty: IRType::closure()
                            },
                            Instr::Store {
                                val: Register(4),
                                location: Register(6),
                                ty: IRType::Pointer
                            },
                            Instr::Store {
                                val: Register(5),
                                location: Register(7),
                                ty: IRType::Pointer
                            },
                            Instr::ConstantInt(Register(8), 2), // The argument `y`.
                            // Unpack the closure
                            Instr::GetElementPointer {
                                dest: Register(9),
                                base: Register(2),
                                index: 0,
                                ty: IRType::closure()
                            },
                            Instr::Load {
                                dest: Register(10),
                                ty: IRType::Func(vec![IRType::Int], IRType::Int.into()),
                                addr: Register(9)
                            },
                            Instr::GetElementPointer {
                                dest: Register(11),
                                base: Register(2),
                                index: 1,
                                ty: IRType::closure()
                            },
                            Instr::Load {
                                dest: Register(12),
                                ty: IRType::Pointer,
                                addr: Register(11)
                            }, // Load func_ptr
                            // Make the call. The `args` list includes the env_ptr (%11) and the explicit arg `y` (%8).
                            Instr::Call {
                                dest_reg: Register(13),
                                ty: IRType::Int,
                                callee: Register(10).into(),
                                args: RegisterList(vec![Register(12), Register(8)]),
                            },
                            Instr::Ret(IRType::Int, Some(Register(13))),
                        ],
                    }],
                    env_ty: IRType::Struct(SymbolID::ENV, vec![]),
                    env_reg: Register(0),
                },
            ]
        )
    }

    #[test]
    fn lowers_struct_initializer() {
        let lowered = lower(
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

        assert_lowered_functions!(
            lowered,
            vec![
                IRFunction {
                    ty: IRType::Func(
                        vec![IRType::Int],
                        IRType::Struct(SymbolID::resolved(1), vec![IRType::Int]).into()
                    ),
                    name: format!("@_{}_Person_init", SymbolID::resolved(1).0),
                    blocks: vec![BasicBlock {
                        id: BasicBlockID(0),
                        instructions: vec![
                            // self.age = age
                            Instr::GetElementPointer {
                                dest: Register(2),
                                base: Register(0), // self is in register 0
                                ty: IRType::Struct(SymbolID::resolved(1), vec![IRType::Int]),
                                index: 0
                            },
                            Instr::Store {
                                ty: IRType::Int,
                                val: Register(1), // age is in register 1
                                location: Register(2)
                            },
                            Instr::Load {
                                ty: IRType::Struct(SymbolID::resolved(1), vec![IRType::Int]),
                                dest: Register(3),
                                addr: Register(0)
                            },
                            Instr::Ret(
                                IRType::Struct(SymbolID::resolved(1), vec![IRType::Int]),
                                Some(Register(3))
                            )
                        ],
                    }],
                    env_ty: IRType::Struct(SymbolID::resolved(1), vec![IRType::Int]),
                    env_reg: Register(0)
                },
                IRFunction {
                    ty: IRType::Func(vec![], IRType::Void.into()),
                    name: "@main".into(),
                    blocks: vec![BasicBlock {
                        id: BasicBlockID(0),
                        instructions: vec![
                            Instr::ConstantInt(Register(1), 123),
                            Instr::Alloc {
                                dest: Register(2),
                                ty: IRType::Struct(SymbolID::resolved(1), vec![IRType::Int]),
                                count: None
                            },
                            Instr::Ref(
                                Register(3),
                                IRType::Func(
                                    vec![IRType::Int],
                                    IRType::Struct(SymbolID::resolved(1), vec![IRType::Int]).into()
                                ),
                                RefKind::Func(format!("@_{}_Person_init", SymbolID::resolved(1).0))
                            ),
                            Instr::Call {
                                dest_reg: Register(4),
                                ty: IRType::Struct(SymbolID::resolved(1), vec![IRType::Int]).into(),
                                callee: Callee::Register(Register(3)),
                                args: RegisterList(vec![Register(2), Register(1)])
                            },
                            Instr::Ret(
                                IRType::Struct(SymbolID::resolved(1), vec![IRType::Int]),
                                Some(Register(4))
                            )
                        ],
                    }],
                    env_ty: IRType::Struct(SymbolID::ENV, vec![]),
                    env_reg: Register(0),
                },
            ]
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

        let person_struct_ty = IRType::Struct(SymbolID::resolved(1), vec![IRType::Int]);
        let person_init_func_ty = IRType::Func(vec![IRType::Int], person_struct_ty.clone().into());

        assert_lowered_functions!(
            lowered,
            vec![
                IRFunction {
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
                                index: 0
                            },
                            Instr::Store {
                                ty: IRType::Int,
                                val: Register(1), // age is in register 1
                                location: Register(2)
                            },
                            Instr::Load {
                                ty: person_struct_ty.clone(),
                                dest: Register(3),
                                addr: Register(0)
                            },
                            // return self
                            Instr::Ret(person_struct_ty.clone(), Some(Register(3)))
                        ],
                    }],
                    env_ty: person_struct_ty.clone(),
                    env_reg: Register(0),
                },
                IRFunction {
                    ty: IRType::Func(vec![], IRType::Void.into()),
                    name: "@main".into(),
                    blocks: vec![BasicBlock {
                        id: BasicBlockID(0),
                        instructions: vec![
                            // Person(age: 123)
                            Instr::ConstantInt(Register(1), 123),
                            Instr::Alloc {
                                dest: Register(2),
                                count: None,
                                ty: person_struct_ty.clone(),
                            },
                            Instr::Ref(
                                Register(3),
                                person_init_func_ty.clone(),
                                RefKind::Func(format!("@_{}_Person_init", SymbolID::resolved(1).0))
                            ),
                            Instr::Call {
                                dest_reg: Register(4),
                                ty: person_struct_ty.clone(),
                                callee: Callee::Register(Register(3)),
                                args: RegisterList(vec![Register(2), Register(1)])
                            },
                            // .age
                            Instr::GetElementPointer {
                                dest: Register(5),
                                base: Register(4),
                                ty: person_struct_ty,
                                index: 0,
                            },
                            Instr::Load {
                                dest: Register(6),
                                ty: IRType::Int,
                                addr: Register(5)
                            },
                            Instr::Ret(IRType::Int, Some(Register(6)))
                        ],
                    }],
                    env_ty: IRType::Struct(SymbolID::ENV, vec![]),
                    env_reg: Register(0)
                },
            ]
        )
    }
}
