#[cfg(test)]
pub mod tests {
    use crate::{
        assert_eq_diff,
        compiling::{
            driver::{Driver, Source},
            module::ModuleId,
        },
        ir::{
            basic_block::{BasicBlock, BasicBlockId},
            function::Function,
            instruction::{Instruction, InstructionMeta},
            ir_ty::IrTy,
            list::List,
            lowerer::Lowerer,
            program::Program,
            register::Register,
            terminator::Terminator,
            value::Value,
        },
        label::Label,
        name::Name,
        name_resolution::symbol::{GlobalId, InstanceMethodId, Symbol, SynthesizedId},
        node_id::NodeID,
    };

    fn meta() -> List<InstructionMeta> {
        vec![InstructionMeta::Source(NodeID::ANY)].into()
    }

    pub fn lower(input: &str) -> Program {
        let driver = Driver::new(vec![Source::from(input)], Default::default());
        let mut typed = driver
            .parse()
            .unwrap()
            .resolve_names()
            .unwrap()
            .typecheck()
            .unwrap();

        let lowerer = Lowerer::new(
            &mut typed.phase.asts,
            &mut typed.phase.types,
            &mut typed.phase.symbols,
            &typed.config.modules,
        );
        lowerer.lower().unwrap()
    }

    #[test]
    fn lowers_int_literal() {
        let program = lower("func main() { 123 }");
        assert_eq!(
            program.functions,
            indexmap::indexmap!(GlobalId::from(1).into() => Function {
                register_count: 1,
                name: Name::Resolved(GlobalId::from(1).into(), "main".into()),
                params: vec![].into(),
                ty: IrTy::Func(vec![], IrTy::Int.into()),
                blocks: vec![BasicBlock {
                    id: BasicBlockId(0),
                    instructions: vec![
                        Instruction::Constant { ty: IrTy::Int, dest: 0.into(), val: 123.into(), meta: vec![InstructionMeta::Source(NodeID::ANY)].into(), }
                    ],
                    terminator: Terminator::Ret {
                        val: Value::Reg(0),
                        ty: IrTy::Int
                    }
                }],
            })
        );
    }

    #[test]
    fn lowers_float_literal() {
        let program = lower("func main() { 1.23 }");
        assert_eq!(
            program.functions,
            indexmap::indexmap!(GlobalId::from(1).into() => Function {
                name: Name::Resolved(GlobalId::from(1).into(), "main".into()),
                register_count: 1,
                params: vec![].into(),
                ty: IrTy::Func(vec![], IrTy::Float.into()),
                blocks: vec![BasicBlock {
                id: BasicBlockId(0),
                instructions: vec![
                    Instruction::Constant {
                      ty: IrTy::Float,
                      dest: 0.into(),
                      val: 1.23.into(),
                      meta: vec![InstructionMeta::Source(NodeID::ANY)].into()
                    }
                ],
                terminator: Terminator::Ret {
                    val: Value::Reg(0),
                    ty: IrTy::Float
                }
                }],
            })
        );
    }

    #[test]
    fn synthesizes_main() {
        let program = lower("123");
        assert_eq!(
            program.functions,
            indexmap::indexmap!(SynthesizedId::from(1).into() => Function {
                name: Name::Resolved(SynthesizedId::from(1).into(), "main".into()),
                params: vec![].into(),
                register_count: 1,
                ty: IrTy::Func(vec![], IrTy::Int.into()),
                    blocks: vec![BasicBlock {
                    id: BasicBlockId(0),
                    instructions: vec![
                        Instruction::Constant { ty: IrTy::Int, dest: 0.into(), val: 123.into(), meta: vec![InstructionMeta::Source(NodeID::ANY)].into(), }
                    ],
                    terminator: Terminator::Ret {
                        val: Value::Reg(0),
                        ty: IrTy::Int
                    }
                }],
            })
        );
    }

    #[test]
    fn lowers_variables() {
        let program = lower("let a = 123 ; a");
        assert_eq!(
            program.functions,
            indexmap::indexmap!(SynthesizedId::from(1).into() => Function {
                name: Name::Resolved(SynthesizedId::from(1).into(), "main".into()),
                params: vec![].into(),
                register_count: 1,
                ty: IrTy::Func(vec![], IrTy::Int.into()),
                    blocks: vec![BasicBlock {
                    id: BasicBlockId(0),
                    instructions: vec![
                        Instruction::Constant { ty: IrTy::Int, dest: 0.into(), val: 123.into(), meta: vec![InstructionMeta::Source(NodeID::ANY)].into(), }
                    ],
                    terminator: Terminator::Ret {
                        val: Value::Reg(0),
                        ty: IrTy::Int
                    }
                }],
            })
        );
    }

    #[test]
    fn lowers_func_call() {
        let program = lower(
            "
        func foo(x: Int) { x }
        foo(123)
        ",
        );

        assert_eq_diff!(
            *program
                .functions
                .get(&Symbol::from(SynthesizedId::from(1)))
                .unwrap(),
            Function {
                name: Name::Resolved(SynthesizedId::from(1).into(), "main".into()),
                params: vec![].into(),
                ty: IrTy::Func(vec![], IrTy::Int.into()),
                register_count: 3,
                blocks: vec![BasicBlock::<IrTy> {
                    id: BasicBlockId(0),
                    instructions: vec![
                        Instruction::Ref {
                            dest: 0.into(),
                            ty: IrTy::Func(vec![IrTy::Int], IrTy::Int.into()),
                            val: Value::Func(Name::Resolved(
                                GlobalId::from(1).into(),
                                "foo".into()
                            ))
                        },
                        Instruction::Constant {
                            ty: IrTy::Int,
                            dest: 2.into(),
                            val: 123.into(),
                            meta: meta(),
                        },
                        Instruction::Call {
                            dest: 1.into(),
                            ty: IrTy::Int,
                            callee: Value::Func(Name::Resolved(
                                GlobalId::from(1).into(),
                                "foo".into()
                            )),
                            args: vec![Value::Reg(2)].into(),
                            meta: meta()
                        }
                    ],
                    terminator: Terminator::Ret {
                        val: Value::Reg(1),
                        ty: IrTy::Int
                    }
                }],
            }
        );
        assert_eq!(
            *program
                .functions
                .get(&Symbol::from(GlobalId::from(1)))
                .unwrap(),
            Function {
                name: Name::Resolved(GlobalId::from(1).into(), "foo".into()),
                params: vec![Value::Reg(0)].into(),
                register_count: 1,
                ty: IrTy::Func(vec![IrTy::Int], IrTy::Int.into()),
                blocks: vec![BasicBlock {
                    id: BasicBlockId(0),
                    instructions: vec![],
                    terminator: Terminator::Ret {
                        val: Value::Reg(0),
                        ty: IrTy::Int
                    }
                }],
            }
        );
    }

    #[test]
    fn lowers_struct_init_and_member() {
        let program = lower(
            "
        struct Foo { let bar: Int }
        Foo(bar: 123).bar
        ",
        );

        assert_eq_diff!(
            *program
                .functions
                .get(&Symbol::from(SynthesizedId::from(2)))
                .unwrap(),
            Function {
                name: Name::Resolved(SynthesizedId::from(2).into(), "main".into()),
                params: vec![].into(),
                ty: IrTy::Func(vec![], IrTy::Int.into()),
                register_count: 4,
                blocks: vec![BasicBlock {
                    id: BasicBlockId(0),
                    instructions: vec![
                        Instruction::Constant {
                            ty: IrTy::Int,
                            dest: 1.into(),
                            val: 123.into(),
                            meta: meta()
                        },
                        Instruction::Record {
                            dest: 2.into(),
                            ty: IrTy::Record(vec![IrTy::Int]),
                            record: vec![Value::Uninit].into(),
                            meta: meta()
                        },
                        Instruction::Call {
                            dest: 0.into(),
                            ty: IrTy::Record(vec![IrTy::Int]),
                            callee: Value::Func(Name::Resolved(
                                Symbol::from(SynthesizedId::from(1)),
                                "@Foo:Struct(_:1)_init".into(),
                            )),
                            args: vec![Register(2).into(), Register(1).into()].into(),
                            meta: meta(),
                        },
                        Instruction::GetField {
                            dest: 3.into(),
                            ty: IrTy::Int,
                            record: Register(0),
                            field: Label::Positional(0),
                            meta: meta(),
                        }
                    ],
                    terminator: Terminator::Ret {
                        val: Value::Reg(3),
                        ty: IrTy::Int
                    }
                }],
            }
        );
    }

    #[test]
    fn monomorphizes_structs() {
        let program = lower(
            "
        struct Foo<T> { let bar: T }
        Foo(bar: 123).bar
        ",
        );

        assert_eq_diff!(
            *program
                .functions
                .get(&Symbol::from(SynthesizedId::from(2)))
                .unwrap(),
            Function {
                name: Name::Resolved(SynthesizedId::from(2).into(), "main".into()),
                params: vec![].into(),
                ty: IrTy::Func(vec![], IrTy::Int.into()),
                register_count: 4,
                blocks: vec![BasicBlock {
                    id: BasicBlockId(0),
                    instructions: vec![
                        Instruction::Constant {
                            ty: IrTy::Int,
                            dest: 1.into(),
                            val: 123.into(),
                            meta: meta()
                        },
                        Instruction::Record {
                            dest: 2.into(),
                            ty: IrTy::Record(vec![IrTy::Int]),
                            record: vec![Value::Uninit].into(),
                            meta: meta()
                        },
                        Instruction::Call {
                            dest: 0.into(),
                            ty: IrTy::Record(vec![IrTy::Int]),
                            callee: Value::Func(Name::Resolved(
                                Symbol::from(SynthesizedId::from(4)),
                                "@@Foo:Struct(_:1)_init:Synthesized(_:1)[Int]".into()
                            )),
                            args: vec![Register(2).into(), Register(1).into()].into(),
                            meta: meta(),
                        },
                        Instruction::GetField {
                            dest: 3.into(),
                            ty: IrTy::Int,
                            record: Register(0),
                            field: Label::Positional(0),
                            meta: meta(),
                        }
                    ],
                    terminator: Terminator::Ret {
                        val: Value::Reg(3),
                        ty: IrTy::Int
                    }
                }],
            }
        );
    }

    #[test]
    fn lowers_enum_constructor_with_no_vals() {
        let program = lower("enum Fizz { case foo, bar } ; Fizz.bar");
        assert_eq_diff!(
            *program
                .functions
                .get(&Symbol::Synthesized(SynthesizedId::from(1)))
                .unwrap(),
            Function {
                name: Name::Resolved(SynthesizedId::from(1).into(), "main".into()),
                params: vec![].into(),
                register_count: 1,
                ty: IrTy::Func(vec![], IrTy::Record(vec![IrTy::Int]).into()),
                blocks: vec![BasicBlock::<IrTy> {
                    id: BasicBlockId(0),
                    instructions: vec![Instruction::Record {
                        dest: 0.into(),
                        ty: IrTy::Record(vec![IrTy::Int]),
                        record: vec![Value::Int(1)].into(),
                        meta: meta()
                    }],
                    terminator: Terminator::Ret {
                        val: Value::Reg(0),
                        ty: IrTy::Record(vec![IrTy::Int]),
                    }
                }],
            }
        )
    }

    #[test]
    fn lowers_enum_constructor_with_vals() {
        let program = lower(
            "
            enum Fizz { case foo(Int, Float), bar(Float, Int) }
            Fizz.bar(1.23, 456)",
        );
        assert_eq_diff!(
            *program
                .functions
                .get(&Symbol::Synthesized(SynthesizedId::from(1)))
                .unwrap(),
            Function {
                name: Name::Resolved(SynthesizedId::from(1).into(), "main".into()),
                params: vec![].into(),
                register_count: 3,
                ty: IrTy::Func(
                    vec![],
                    IrTy::Record(vec![IrTy::Int, IrTy::Float, IrTy::Int]).into()
                ),
                blocks: vec![BasicBlock::<IrTy> {
                    id: BasicBlockId(0),
                    instructions: vec![
                        Instruction::Constant {
                            ty: IrTy::Float,
                            dest: 0.into(),
                            val: 1.23.into(),
                            meta: meta()
                        },
                        Instruction::Constant {
                            ty: IrTy::Int,
                            dest: 1.into(),
                            val: 456.into(),
                            meta: meta()
                        },
                        Instruction::Record {
                            dest: 2.into(),
                            ty: IrTy::Record(vec![IrTy::Int, IrTy::Float, IrTy::Int]),
                            record: vec![Value::Int(1), Value::Reg(0), Value::Reg(1)].into(),
                            meta: meta()
                        }
                    ],
                    terminator: Terminator::Ret {
                        val: Value::Reg(2),
                        ty: IrTy::Record(vec![IrTy::Int, IrTy::Float, IrTy::Int]),
                    }
                }],
            }
        )
    }

    #[test]
    fn lowers_add() {
        let program = lower("1 + 2");
        assert_eq_diff!(
            *program
                .functions
                .get(&Symbol::Synthesized(SynthesizedId::from(1)))
                .unwrap(),
            Function {
                name: Name::Resolved(SynthesizedId::from(1).into(), "main".into()),
                params: vec![].into(),
                register_count: 3,
                ty: IrTy::Func(vec![], IrTy::Int.into()),
                blocks: vec![BasicBlock::<IrTy> {
                    id: BasicBlockId(0),
                    instructions: vec![
                        Instruction::Constant {
                            ty: IrTy::Int,
                            dest: 1.into(),
                            val: 2.into(),
                            meta: vec![InstructionMeta::Source(NodeID::ANY)].into(),
                        },
                        Instruction::Constant {
                            ty: IrTy::Int,
                            dest: 2.into(),
                            val: 1.into(),
                            meta: vec![InstructionMeta::Source(NodeID::ANY)].into(),
                        },
                        Instruction::Call {
                            dest: Register(0),
                            ty: IrTy::Int,
                            callee: Value::Func(Name::Resolved(
                                Symbol::InstanceMethod(InstanceMethodId {
                                    module_id: ModuleId::Core,
                                    local_id: 1
                                }),
                                "add".into()
                            )),
                            args: vec![Register(2).into(), Register(1).into()].into(),
                            meta: meta()
                        },
                    ],
                    terminator: Terminator::Ret {
                        val: Value::Reg(0),
                        ty: IrTy::Int
                    }
                }],
            }
        );
        assert!(
            program
                .functions
                .get(&Symbol::InstanceMethod(InstanceMethodId {
                    module_id: ModuleId::Core,
                    local_id: 1
                }))
                .is_some()
        )
    }

    #[test]
    fn lowers_struct_method() {
        let program = lower(
            "
        struct Foo {
            let bar: Int

            func getBar() {
                self.bar
            }
        }

        Foo(bar: 123).getBar()
        ",
        );

        assert_eq_diff!(
            *program
                .functions
                .get(&Symbol::from(SynthesizedId::from(2)))
                .unwrap(),
            Function {
                name: Name::Resolved(SynthesizedId::from(2).into(), "main".into()),
                params: vec![].into(),
                ty: IrTy::Func(vec![], IrTy::Int.into()),
                register_count: 4,
                blocks: vec![BasicBlock::<IrTy> {
                    id: BasicBlockId(0),
                    instructions: vec![
                        Instruction::Constant {
                            ty: IrTy::Int,
                            dest: 2.into(),
                            val: 123.into(),
                            meta: meta()
                        },
                        Instruction::Record {
                            dest: 3.into(),
                            ty: IrTy::Record(vec![IrTy::Int]),
                            record: vec![Value::Uninit].into(),
                            meta: meta()
                        },
                        Instruction::Call {
                            dest: 1.into(),
                            ty: IrTy::Record(vec![IrTy::Int]),
                            callee: Value::Func(Name::Resolved(
                                Symbol::from(SynthesizedId::from(1)),
                                "@Foo:Struct(_:1)_init".into()
                            )),
                            args: vec![Register(3).into(), Register(2).into()].into(),
                            meta: meta(),
                        },
                        Instruction::Call {
                            dest: 0.into(),
                            ty: IrTy::Int,
                            callee: Value::Func(Name::Resolved(
                                InstanceMethodId::from(1).into(),
                                "getBar".into()
                            )),
                            args: vec![Register(1).into()].into(),
                            meta: meta(),
                        },
                    ],
                    terminator: Terminator::Ret {
                        val: Value::Reg(0),
                        ty: IrTy::Int
                    }
                }],
            }
        );
    }

    #[test]
    fn embedded_ir() {
        let program = lower(
            "
        __IR<Int>(\"$? = add int 1 2\")
        ",
        );
        assert_eq!(
            program.functions,
            indexmap::indexmap!(SynthesizedId::from(1).into() => Function {
                name: Name::Resolved(SynthesizedId::from(1).into(), "main".into()),
                params: vec![].into(),
                ty: IrTy::Func(vec![], IrTy::Int.into()),
                register_count: 1,
                blocks: vec![BasicBlock {
                    id: BasicBlockId(0),
                    instructions: vec![Instruction::Add {
                        dest: 0.into(),
                        ty: IrTy::Int,
                        a: Value::Int(1),
                        b: Value::Int(2),
                        meta: vec![].into(),
                    }],
                    terminator: Terminator::Ret {
                        val: Value::Reg(0),
                        ty: IrTy::Int
                    }
                }],
            })
        );
    }

    #[test]
    fn embedded_ir_uses_variables() {
        let program = lower(
            "
        let a = 1
        let b = 2
        __IR<Int>(\"$? = add int %0 %1\")
        ",
        );
        assert_eq!(
            *program
                .functions
                .get(&Symbol::from(SynthesizedId::from(1)))
                .unwrap(),
            Function {
                name: Name::Resolved(SynthesizedId::from(1).into(), "main".into()),
                params: vec![].into(),
                ty: IrTy::Func(vec![], IrTy::Int.into()),
                register_count: 3,
                blocks: vec![BasicBlock {
                    id: BasicBlockId(0),
                    instructions: vec![
                        Instruction::Constant {
                            ty: IrTy::Int,
                            dest: 0.into(),
                            val: 1.into(),
                            meta: vec![InstructionMeta::Source(NodeID::ANY)].into()
                        },
                        Instruction::Constant {
                            ty: IrTy::Int,
                            dest: 1.into(),
                            val: 2.into(),
                            meta: vec![InstructionMeta::Source(NodeID::ANY)].into()
                        },
                        Instruction::Add {
                            dest: 2.into(),
                            ty: IrTy::Int,
                            a: Value::Reg(0),
                            b: Value::Reg(1),
                            meta: vec![].into(),
                        }
                    ],
                    terminator: Terminator::Ret {
                        val: Value::Reg(2),
                        ty: IrTy::Int
                    }
                }],
            }
        );
    }

    #[test]
    fn monomorphizes_simple_generic_func() {
        let program = lower(
            "
            func id(x) { x }
            id(123)
            id(1.23)
        ",
        );

        assert_eq_diff!(
            *program
                .functions
                .get(&Symbol::from(SynthesizedId::from(1)))
                .unwrap(),
            Function {
                name: Name::Resolved(SynthesizedId::from(1).into(), "main".into()),
                params: vec![].into(),
                ty: IrTy::Func(vec![], IrTy::Float.into()),
                register_count: 5,
                blocks: vec![BasicBlock::<IrTy> {
                    id: BasicBlockId(0),
                    instructions: vec![
                        Instruction::Ref {
                            dest: 0.into(),
                            ty: IrTy::Func(vec![IrTy::Void], IrTy::Void.into()),
                            val: Value::Func(Name::Resolved(
                                Symbol::Global(GlobalId::from(1)),
                                "id".into()
                            ))
                        },
                        Instruction::Constant {
                            ty: IrTy::Int,
                            dest: 2.into(),
                            val: 123.into(),
                            meta: vec![InstructionMeta::Source(NodeID::ANY)].into()
                        },
                        Instruction::Call {
                            dest: 1.into(),
                            ty: IrTy::Int,
                            callee: Value::Func(Name::Resolved(
                                Symbol::Synthesized(SynthesizedId::from(4)),
                                "@id:Global(_:1)[Int]".into()
                            )),
                            args: vec![Value::Reg(2)].into(),
                            meta: meta(),
                        },
                        Instruction::Constant {
                            ty: IrTy::Float,
                            dest: 4.into(),
                            val: 1.23.into(),
                            meta: vec![InstructionMeta::Source(NodeID::ANY)].into()
                        },
                        Instruction::Call {
                            dest: 3.into(),
                            ty: IrTy::Float,
                            callee: Value::Func(Name::Resolved(
                                Symbol::Synthesized(SynthesizedId::from(7)),
                                "@id:Global(_:1)[Float]".into()
                            )),
                            args: vec![Value::Reg(4)].into(),
                            meta: meta(),
                        },
                    ],
                    terminator: Terminator::Ret {
                        val: Value::Reg(3),
                        ty: IrTy::Float
                    }
                }],
            }
        );

        assert_eq_diff!(
            *program
                .functions
                .get(&Symbol::from(SynthesizedId::from(3)))
                .unwrap(),
            Function {
                name: Name::Resolved(SynthesizedId::from(3).into(), "@id:Global(_:1)[Int]".into()),
                params: vec![Value::Reg(0)].into(),
                ty: IrTy::Func(vec![IrTy::Int], IrTy::Int.into()),
                register_count: 1,
                blocks: vec![BasicBlock::<IrTy> {
                    id: BasicBlockId(0),
                    instructions: vec![],
                    terminator: Terminator::Ret {
                        val: Value::Reg(0),
                        ty: IrTy::Int
                    }
                }],
            }
        );

        assert_eq_diff!(
            *program
                .functions
                .get(&Symbol::from(SynthesizedId::from(5)))
                .unwrap(),
            Function {
                name: Name::Resolved(
                    SynthesizedId::from(5).into(),
                    "@id:Global(_:1)[Float]".into()
                ),
                params: vec![Value::Reg(0)].into(),
                ty: IrTy::Func(vec![IrTy::Float], IrTy::Float.into()),
                register_count: 1,
                blocks: vec![BasicBlock::<IrTy> {
                    id: BasicBlockId(0),
                    instructions: vec![],
                    terminator: Terminator::Ret {
                        val: Value::Reg(0),
                        ty: IrTy::Float
                    }
                }],
            }
        );
    }

    #[test]
    fn lowers_if_stmt() {
        let program = lower(
            "
        if false {
          456
        }
        123
        ",
        );
        assert_eq_diff!(
            *program
                .functions
                .get(&Symbol::Synthesized(SynthesizedId::from(1)))
                .unwrap(),
            Function::<IrTy> {
                name: Name::Resolved(SynthesizedId::from(1).into(), "main".into()),
                params: vec![].into(),
                ty: IrTy::Func(vec![], IrTy::Int.into()),
                register_count: 1,
                blocks: vec![
                    BasicBlock {
                        id: BasicBlockId(0),
                        instructions: vec![Instruction::Constant {
                            dest: 0.into(),
                            ty: IrTy::Bool,
                            val: Value::Bool(false),
                            meta: vec![].into(),
                        }],
                        terminator: Terminator::Branch {
                            cond: Value::Reg(0),
                            conseq: BasicBlockId(1),
                            alt: BasicBlockId(2),
                        }
                    },
                    BasicBlock {
                        id: BasicBlockId(0),
                        instructions: vec![Instruction::Add {
                            dest: 0.into(),
                            ty: IrTy::Int,
                            a: Value::Int(1),
                            b: Value::Int(2),
                            meta: vec![].into(),
                        }],
                        terminator: Terminator::Ret {
                            val: Value::Reg(0),
                            ty: IrTy::Int
                        }
                    },
                    BasicBlock {
                        id: BasicBlockId(0),
                        instructions: vec![Instruction::Add {
                            dest: 0.into(),
                            ty: IrTy::Int,
                            a: Value::Int(1),
                            b: Value::Int(2),
                            meta: vec![].into(),
                        }],
                        terminator: Terminator::Ret {
                            val: Value::Reg(0),
                            ty: IrTy::Int
                        }
                    }
                ],
            }
        );
    }
}
