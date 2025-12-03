#[cfg(test)]
pub mod tests {
    use std::str::FromStr;

    use itertools::Itertools;

    use crate::{
        assert_eq_diff,
        compiling::{
            driver::{Driver, Source},
            module::{Module, ModuleId},
        },
        ir::{
            basic_block::{BasicBlock, BasicBlockId, Phi, PhiSource},
            function::Function,
            instruction::{CmpOperator, Instruction, InstructionMeta},
            ir_ty::IrTy,
            list::List,
            lowerer::Lowerer,
            program::Program,
            register::Register,
            terminator::Terminator,
            value::{Addr, Value},
        },
        label::Label,
        name::Name,
        name_resolution::symbol::{
            EnumId, GlobalId, InstanceMethodId, StructId, Symbol, SynthesizedId,
        },
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
            &typed.config,
        );
        lowerer.lower().unwrap()
    }

    pub fn lower_module(input: &str) -> Module {
        let driver = Driver::new(vec![Source::from(input)], Default::default());
        driver
            .parse()
            .unwrap()
            .resolve_names()
            .unwrap()
            .typecheck()
            .unwrap()
            .lower()
            .unwrap()
            .module("TestModule")
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
                    phis: Default::default(),
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
                phis: Default::default(),
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
                    phis: Default::default(),
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
                    phis: Default::default(),
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
                    phis: Default::default(),
                    instructions: vec![
                        Instruction::Ref {
                            dest: 0.into(),
                            ty: IrTy::Func(vec![IrTy::Int], IrTy::Int.into()),
                            val: Value::Func(GlobalId::from(1).into())
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
                            callee: Value::Reg(0),
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
                    phis: Default::default(),
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
                    phis: Default::default(),
                    instructions: vec![
                        Instruction::Constant {
                            ty: IrTy::Int,
                            dest: 1.into(),
                            val: 123.into(),
                            meta: meta()
                        },
                        Instruction::Nominal {
                            sym: Symbol::Struct(StructId::from(1)),
                            dest: 2.into(),
                            ty: IrTy::Record(
                                Some(Symbol::Struct(StructId::from(1))),
                                vec![IrTy::Int]
                            ),
                            record: vec![Value::Uninit].into(),
                            meta: meta()
                        },
                        Instruction::Call {
                            dest: 0.into(),
                            ty: IrTy::Record(
                                Some(Symbol::Struct(StructId::from(1))),
                                vec![IrTy::Int]
                            ),
                            callee: Value::Func(Symbol::from(SynthesizedId::from(1))),
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
                    phis: Default::default(),
                    instructions: vec![
                        Instruction::Constant {
                            ty: IrTy::Int,
                            dest: 1.into(),
                            val: 123.into(),
                            meta: meta()
                        },
                        Instruction::Nominal {
                            sym: Symbol::Struct(StructId::from(1)),
                            dest: 2.into(),
                            ty: IrTy::Record(
                                Some(Symbol::Struct(StructId::from(1))),
                                vec![IrTy::Int]
                            ),
                            record: vec![Value::Uninit].into(),
                            meta: meta()
                        },
                        Instruction::Call {
                            dest: 0.into(),
                            ty: IrTy::Record(
                                Some(Symbol::Struct(StructId::from(1))),
                                vec![IrTy::Int]
                            ),
                            callee: Value::Func(Symbol::from(SynthesizedId::from(4))),
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
                ty: IrTy::Func(
                    vec![],
                    IrTy::Record(Some(Symbol::Enum(EnumId::from(1))), vec![IrTy::Int]).into()
                ),
                blocks: vec![BasicBlock::<IrTy> {
                    id: BasicBlockId(0),
                    phis: Default::default(),
                    instructions: vec![Instruction::Nominal {
                        sym: Symbol::Enum(EnumId::from(1)),
                        dest: 0.into(),
                        ty: IrTy::Record(Some(Symbol::Enum(EnumId::from(1))), vec![IrTy::Int]),
                        record: vec![Value::Int(1)].into(),
                        meta: meta()
                    }],
                    terminator: Terminator::Ret {
                        val: Value::Reg(0),
                        ty: IrTy::Record(Some(Symbol::Enum(EnumId::from(1))), vec![IrTy::Int]),
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
                    IrTy::Record(
                        Some(Symbol::Enum(EnumId::from(1))),
                        vec![IrTy::Int, IrTy::Float, IrTy::Int]
                    )
                    .into()
                ),
                blocks: vec![BasicBlock::<IrTy> {
                    id: BasicBlockId(0),
                    phis: Default::default(),
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
                        Instruction::Nominal {
                            sym: Symbol::Enum(EnumId::from(1)),
                            dest: 2.into(),
                            ty: IrTy::Record(
                                Some(Symbol::Enum(EnumId::from(1))),
                                vec![IrTy::Int, IrTy::Float, IrTy::Int]
                            ),
                            record: vec![Value::Int(1), Value::Reg(0), Value::Reg(1)].into(),
                            meta: meta()
                        }
                    ],
                    terminator: Terminator::Ret {
                        val: Value::Reg(2),
                        ty: IrTy::Record(
                            Some(Symbol::Enum(EnumId::from(1))),
                            vec![IrTy::Int, IrTy::Float, IrTy::Int]
                        ),
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
                    phis: Default::default(),
                    instructions: vec![
                        Instruction::Constant {
                            ty: IrTy::Int,
                            dest: 1.into(),
                            val: 1.into(),
                            meta: vec![InstructionMeta::Source(NodeID::ANY)].into(),
                        },
                        Instruction::Constant {
                            ty: IrTy::Int,
                            dest: 2.into(),
                            val: 2.into(),
                            meta: vec![InstructionMeta::Source(NodeID::ANY)].into(),
                        },
                        Instruction::Call {
                            dest: Register(0),
                            ty: IrTy::Int,
                            callee: Value::Func(Symbol::InstanceMethod(InstanceMethodId {
                                module_id: ModuleId::Core,
                                local_id: 3
                            })),
                            args: vec![Register(1).into(), Register(2).into()].into(),
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
                    local_id: 3
                }))
                .is_some()
        )
    }

    #[test]
    fn lowers_default_implementations() {
        let program = lower("1 <= 2");

        // The original lte method should still be imported
        assert!(
            program
                .functions
                .get(&Symbol::InstanceMethod(InstanceMethodId {
                    module_id: ModuleId::Core,
                    local_id: 18
                }))
                .is_some()
        );

        // There should be a specialized function for lte with witnesses
        let has_specialization = program.functions.values().any(|f| {
            f.name.name_str().contains("lte") && f.name.name_str().contains("InstanceMethod")
        });
        assert!(has_specialization, "expected specialized lte function");
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
                    phis: Default::default(),
                    instructions: vec![
                        Instruction::Constant {
                            ty: IrTy::Int,
                            dest: 2.into(),
                            val: 123.into(),
                            meta: meta()
                        },
                        Instruction::Nominal {
                            sym: Symbol::Struct(StructId::from(1)),
                            dest: 3.into(),
                            ty: IrTy::Record(
                                Some(Symbol::Struct(StructId::from(1))),
                                vec![IrTy::Int]
                            ),
                            record: vec![Value::Uninit].into(),
                            meta: meta()
                        },
                        Instruction::Call {
                            dest: 1.into(),
                            ty: IrTy::Record(
                                Some(Symbol::Struct(StructId::from(1))),
                                vec![IrTy::Int]
                            ),
                            callee: Value::Func(Symbol::from(SynthesizedId::from(1))),
                            args: vec![Register(3).into(), Register(2).into()].into(),
                            meta: meta(),
                        },
                        Instruction::Call {
                            dest: 0.into(),
                            ty: IrTy::Int,
                            callee: Value::Func(InstanceMethodId::from(1).into()),
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
                    phis: Default::default(),
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
                    phis: Default::default(),
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
                    phis: Default::default(),
                    instructions: vec![
                        Instruction::Ref {
                            dest: 0.into(),
                            ty: IrTy::Func(vec![IrTy::Void], IrTy::Void.into()),
                            val: Value::Func(Symbol::Global(GlobalId::from(1)))
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
                            callee: Value::Reg(0),
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
                            callee: Value::Reg(0),
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
                    phis: Default::default(),
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
                    phis: Default::default(),
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
                        phis: Default::default(),
                        instructions: vec![],
                        terminator: Terminator::Branch {
                            cond: Value::Bool(false),
                            conseq: BasicBlockId(1),
                            alt: BasicBlockId(2),
                        }
                    },
                    BasicBlock {
                        id: BasicBlockId(1),
                        phis: Default::default(),
                        instructions: vec![Instruction::Constant {
                            dest: Register::DROP,
                            ty: IrTy::Int,
                            val: Value::Int(456),
                            meta: meta()
                        }],
                        terminator: Terminator::Jump {
                            to: BasicBlockId(2)
                        }
                    },
                    BasicBlock {
                        id: BasicBlockId(2),
                        phis: Default::default(),
                        instructions: vec![Instruction::Constant {
                            dest: 0.into(),
                            ty: IrTy::Int,
                            val: Value::Int(123),
                            meta: meta()
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

    #[test]
    fn lowers_match() {
        let program = lower(
            "
        match 789 {
            123 -> 1,
            456 -> 2,
            789 -> 3,
        }
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
                // allocator got up to Register(9), so next is 10
                register_count: 7,
                blocks: vec![
                    BasicBlock {
                        id: BasicBlockId(0),
                        phis: vec![],
                        instructions: vec![
                            Instruction::Constant {
                                dest: Register(1),
                                ty: IrTy::Int,
                                val: Value::Int(789),
                                meta: meta(), // NodeID::ANY-based helper
                            },
                            Instruction::Cmp {
                                dest: Register(5),
                                lhs: Value::Reg(1),
                                rhs: Value::Int(123),
                                ty: IrTy::Int,
                                op: CmpOperator::Equals,
                                meta: meta(),
                            },
                        ],
                        terminator: Terminator::Branch {
                            cond: Value::Reg(5),
                            conseq: BasicBlockId(2),
                            alt: BasicBlockId(5),
                        },
                    },
                    BasicBlock {
                        id: BasicBlockId(1),
                        phis: vec![Phi {
                            dest: Register(0),
                            ty: IrTy::Int,
                            sources: vec![
                                PhiSource {
                                    from_id: BasicBlockId(2),
                                    value: Register(2).into(),
                                },
                                PhiSource {
                                    from_id: BasicBlockId(3),
                                    value: Register(3).into(),
                                },
                                PhiSource {
                                    from_id: BasicBlockId(4),
                                    value: Register(4).into(),
                                },
                            ]
                            .into(),
                        }],
                        instructions: vec![],
                        terminator: Terminator::Ret {
                            val: Value::Reg(0),
                            ty: IrTy::Int,
                        },
                    },
                    BasicBlock {
                        id: BasicBlockId(2),
                        phis: vec![],
                        instructions: vec![Instruction::Constant {
                            dest: Register(2),
                            ty: IrTy::Int,
                            val: Value::Int(1),
                            meta: meta(),
                        },],
                        terminator: Terminator::Jump {
                            to: BasicBlockId(1),
                        },
                    },
                    BasicBlock {
                        id: BasicBlockId(3),
                        phis: vec![],
                        instructions: vec![Instruction::Constant {
                            dest: Register(3),
                            ty: IrTy::Int,
                            val: Value::Int(2),
                            meta: meta(),
                        },],
                        terminator: Terminator::Jump {
                            to: BasicBlockId(1),
                        },
                    },
                    BasicBlock {
                        id: BasicBlockId(4),
                        phis: vec![],
                        instructions: vec![Instruction::Constant {
                            dest: Register(4),
                            ty: IrTy::Int,
                            val: Value::Int(3),
                            meta: meta(),
                        },],
                        terminator: Terminator::Jump {
                            to: BasicBlockId(1),
                        },
                    },
                    BasicBlock {
                        id: BasicBlockId(5),
                        phis: vec![],
                        instructions: vec![Instruction::Cmp {
                            dest: Register(6),
                            lhs: Value::Reg(1),
                            rhs: Value::Int(456),
                            ty: IrTy::Int,
                            op: CmpOperator::Equals,
                            meta: meta(),
                        },],
                        terminator: Terminator::Branch {
                            cond: Value::Reg(6),
                            conseq: BasicBlockId(3),
                            alt: BasicBlockId(6),
                        },
                    },
                    BasicBlock {
                        id: BasicBlockId(6),
                        phis: vec![],
                        instructions: vec![],
                        terminator: Terminator::Jump {
                            to: BasicBlockId(4),
                        },
                    },
                ]
            }
        );
    }

    #[test]
    fn lowers_loop() {
        let program = lower(
            "
            loop {
                123
            }
            ",
        );

        assert_eq!(
            *program
                .functions
                .get(&Symbol::Synthesized(SynthesizedId::from(1)))
                .unwrap()
                .blocks,
            vec![
                BasicBlock::from_str(
                    "
                #0:
                    jmp #1   
                    "
                )
                .unwrap(),
                BasicBlock::from_str(
                    "
                #1:
                    jmp #2
                    "
                )
                .unwrap(),
                BasicBlock::from_str(
                    "
                #2:
                    %4294967295 = const int 123 (id:0:1)
                    jmp #1

                    "
                )
                .unwrap(),
                BasicBlock::from_str(
                    "
                #3:
                   ret void void 

                    "
                )
                .unwrap()
            ]
        )
    }

    #[test]
    fn lowers_string_literal() {
        let program = lower("\"hello\"");
        assert_eq!(
            *program
                .functions
                .get(&Symbol::Synthesized(SynthesizedId::from(1)))
                .unwrap()
                .blocks,
            vec![BasicBlock {
                id: BasicBlockId(0),
                phis: Default::default(),
                instructions: vec![Instruction::Nominal {
                    dest: 0.into(),
                    sym: Symbol::String,
                    ty: IrTy::Record(
                        Some(Symbol::String),
                        vec![IrTy::RawPtr, IrTy::Int, IrTy::Int]
                    ),
                    record: vec![Value::RawPtr(Addr(0)), Value::Int(5), Value::Int(5)].into(),
                    meta: meta()
                }],
                terminator: Terminator::Ret {
                    val: Register(0).into(),
                    ty: IrTy::Record(
                        Some(Symbol::String),
                        vec![IrTy::RawPtr, IrTy::Int, IrTy::Int]
                    ),
                }
            }]
        );
        assert_eq!(
            program.static_memory.data[0..5],
            "hello".bytes().collect_vec()
        )
    }

    #[test]
    fn lowers_closure() {
        let program = lower(
            "
        let a = 123
        func b() { a }
        b()
        a // Make sure we know to load from heap now since it's a capture
        ",
        );

        println!("{program}");

        assert_eq_diff!(
            program
                .functions
                .get(&Symbol::Synthesized(SynthesizedId::from(1)))
                .unwrap()
                .blocks,
            &[BasicBlock {
                id: BasicBlockId(0),
                phis: Default::default(),
                instructions: vec![
                    Instruction::Alloc {
                        dest: 0.into(),
                        ty: IrTy::Int,
                        count: Value::Int(1),
                    },
                    Instruction::Constant {
                        dest: 1.into(),
                        ty: IrTy::Int,
                        val: Value::Int(123),
                        meta: meta()
                    },
                    Instruction::Store {
                        value: Value::Reg(1),
                        ty: IrTy::Int,
                        addr: Value::Reg(0)
                    },
                    Instruction::Ref {
                        dest: 2.into(),
                        ty: IrTy::Func(
                            vec![IrTy::Record(None, vec![IrTy::RawPtr,])],
                            IrTy::Int.into()
                        ),
                        val: Value::Closure {
                            func: GlobalId::from(2).into(),
                            env: vec![Value::Reg(0)].into()
                        }
                    },
                    Instruction::Call {
                        dest: 3.into(),
                        ty: IrTy::Int,
                        callee: Value::Reg(2),
                        args: vec![].into(),
                        meta: meta(),
                    },
                    Instruction::Load {
                        dest: 4.into(),
                        ty: IrTy::Int,
                        addr: Value::Reg(0),
                    }
                ],
                terminator: Terminator::Ret {
                    val: Value::Reg(4),
                    ty: IrTy::Int,
                }
            }]
        );

        assert_eq_diff!(
            program
                .functions
                .get(&Symbol::Global(GlobalId::from(2)))
                .unwrap()
                .blocks,
            &[BasicBlock {
                id: BasicBlockId(0),
                phis: Default::default(),
                instructions: vec![
                    Instruction::GetField {
                        dest: 1.into(),
                        ty: IrTy::RawPtr,
                        record: 0.into(),
                        field: Label::Positional(0),
                        meta: vec![].into()
                    },
                    Instruction::Load {
                        dest: 2.into(),
                        ty: IrTy::Int,
                        addr: Value::Reg(1)
                    }
                ],
                terminator: Terminator::Ret {
                    val: Value::Reg(2),
                    ty: IrTy::Int,
                }
            }]
        );
    }
}
