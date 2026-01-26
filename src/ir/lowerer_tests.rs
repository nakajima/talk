#[cfg(test)]
pub mod tests {
    use std::str::FromStr;

    use itertools::Itertools;
    use rustc_hash::FxHashMap;

    use crate::{
        assert_eq_diff,
        compiling::{
            driver::{Driver, DriverConfig, Source},
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
            value::{Addr, RecordId, Value},
        },
        label::Label,
        name_resolution::symbol::{
            EffectId, EnumId, GlobalId, InstanceMethodId, StructId, Symbol, SynthesizedId,
            set_symbol_names,
        },
        node_id::NodeID,
    };

    fn meta() -> List<InstructionMeta> {
        vec![InstructionMeta::Source(NodeID::ANY)].into()
    }

    pub fn lower_bare(input: &str) -> Module {
        let driver = Driver::new_bare(
            vec![Source::from(input)],
            DriverConfig::new("TestDriver").executable(),
        );
        let typed = driver
            .parse()
            .unwrap()
            .resolve_names()
            .unwrap()
            .typecheck()
            .unwrap();

        typed.lower().unwrap().module("TestModule")
    }

    pub fn lower(input: &str) -> Program {
        let driver = Driver::new(
            vec![Source::from(input)],
            DriverConfig::new("TestDriver").executable(),
        );
        let mut typed = driver
            .parse()
            .unwrap()
            .resolve_names()
            .unwrap()
            .typecheck()
            .unwrap();

        let lowerer = Lowerer::new(&mut typed.phase, &typed.config);
        lowerer.lower().unwrap()
    }

    pub fn lower_module(input: &str) -> (Module, FxHashMap<Symbol, String>) {
        let driver = Driver::new(
            vec![Source::from(input)],
            DriverConfig::new("TestDriver").executable(),
        );
        let lowered = driver
            .parse()
            .unwrap()
            .resolve_names()
            .unwrap()
            .typecheck()
            .unwrap()
            .lower()
            .unwrap();
        let display_names = lowered.display_symbol_names();
        let module = lowered.module("TestModule");
        (module, display_names)
    }

    #[test]
    fn lowers_int_literal() {
        let program = lower("func main() { 123 }");
        assert_eq!(
            program.functions,
            indexmap::indexmap!(GlobalId::from(1).into() => Function {
                register_count: 1,
                name: GlobalId::from(1).into() ,
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
                self_out: None,
            })
        );
    }

    #[test]
    fn lowers_float_literal() {
        let program = lower("func main() { 1.23 }");
        assert_eq!(
            program.functions,
            indexmap::indexmap!(GlobalId::from(1).into() => Function {
                name: GlobalId::from(1).into(),
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
                self_out: None,
            })
        );
    }

    #[test]
    fn synthesizes_main() {
        let program = lower("123");
        assert_eq!(
            program.functions,
            indexmap::indexmap!(Symbol::Main => Function {
                name: Symbol::Main,
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
                self_out: None,
            })
        );
    }

    #[test]
    fn lowers_variables() {
        let program = lower("let a = 123 ; a");
        assert_eq!(
            program.functions,
            indexmap::indexmap!(Symbol::Main => Function {
                name: Symbol::Main,
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
                self_out: None,
            })
        );
    }

    #[test]
    fn lowers_mutated_local_to_pointer() {
        let program = lower("let i = 0; i = 1; i");

        assert_eq_diff!(
            program.functions.get(&Symbol::Main).unwrap().blocks,
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
                        val: Value::Int(0),
                        meta: meta(),
                    },
                    Instruction::Store {
                        value: Value::Reg(1),
                        ty: IrTy::Int,
                        addr: Value::Reg(0),
                    },
                    Instruction::Constant {
                        dest: 2.into(),
                        ty: IrTy::Int,
                        val: Value::Int(1),
                        meta: meta(),
                    },
                    Instruction::Store {
                        value: Value::Reg(2),
                        ty: IrTy::Int,
                        addr: Value::Reg(0),
                    },
                    Instruction::Load {
                        dest: 3.into(),
                        ty: IrTy::Int,
                        addr: Value::Reg(0),
                    },
                ],
                terminator: Terminator::Ret {
                    val: Value::Reg(3),
                    ty: IrTy::Int,
                },
            }]
        );
    }

    #[test]
    fn lowers_mutated_param_to_pointer() {
        let program = lower(
            "
        func inc(x: Int) { x = 1; x }
        inc(0)
        ",
        );

        assert_eq_diff!(
            program
                .functions
                .get(&Symbol::from(GlobalId::from(1)))
                .unwrap()
                .blocks,
            &[BasicBlock {
                id: BasicBlockId(0),
                phis: Default::default(),
                instructions: vec![
                    Instruction::Alloc {
                        dest: 1.into(),
                        ty: IrTy::Int,
                        count: Value::Int(1),
                    },
                    Instruction::Store {
                        value: Value::Reg(0),
                        ty: IrTy::Int,
                        addr: Value::Reg(1),
                    },
                    Instruction::Constant {
                        dest: 2.into(),
                        ty: IrTy::Int,
                        val: Value::Int(1),
                        meta: meta(),
                    },
                    Instruction::Store {
                        value: Value::Reg(2),
                        ty: IrTy::Int,
                        addr: Value::Reg(1),
                    },
                    Instruction::Load {
                        dest: 3.into(),
                        ty: IrTy::Int,
                        addr: Value::Reg(1),
                    },
                    // Load for self_out (final value of first param)
                    Instruction::Load {
                        dest: 4.into(),
                        ty: IrTy::Int,
                        addr: Value::Reg(1),
                    },
                ],
                terminator: Terminator::Ret {
                    val: Value::Reg(3),
                    ty: IrTy::Int,
                },
            }]
        );
    }

    #[test]
    fn lowers_mutated_member_base_to_pointer() {
        let program = lower(
            "
        let a = { b: 1 }
        a.b = 2
        a
        ",
        );

        assert_eq_diff!(
            program.functions.get(&Symbol::Main).unwrap().blocks,
            &[BasicBlock {
                id: BasicBlockId(0),
                phis: Default::default(),
                instructions: vec![
                    Instruction::Alloc {
                        dest: 0.into(),
                        ty: IrTy::Record(None, vec![IrTy::Int]),
                        count: Value::Int(1),
                    },
                    Instruction::Constant {
                        dest: 1.into(),
                        ty: IrTy::Int,
                        val: Value::Int(1),
                        meta: meta(),
                    },
                    Instruction::Record {
                        dest: 2.into(),
                        ty: IrTy::Record(None, vec![IrTy::Int]),
                        record: vec![Value::Reg(1)].into(),
                        meta: vec![
                            InstructionMeta::Source(NodeID::ANY),
                            InstructionMeta::RecordId(RecordId::Record(0)),
                        ]
                        .into(),
                    },
                    Instruction::Store {
                        value: Value::Reg(2),
                        ty: IrTy::Record(None, vec![IrTy::Int]),
                        addr: Value::Reg(0),
                    },
                    Instruction::Constant {
                        dest: 3.into(),
                        ty: IrTy::Int,
                        val: Value::Int(2),
                        meta: meta(),
                    },
                    Instruction::Load {
                        dest: 4.into(),
                        ty: IrTy::Record(None, vec![IrTy::Int]),
                        addr: Value::Reg(0),
                    },
                    Instruction::SetField {
                        dest: 5.into(),
                        val: Value::Reg(3),
                        ty: IrTy::Record(None, vec![IrTy::Int]),
                        record: Register(4),
                        field: Label::Positional(0),
                        meta: vec![].into(),
                    },
                    Instruction::Store {
                        value: Value::Reg(5),
                        ty: IrTy::Record(None, vec![IrTy::Int]),
                        addr: Value::Reg(0),
                    },
                    Instruction::Load {
                        dest: 6.into(),
                        ty: IrTy::Record(None, vec![IrTy::Int]),
                        addr: Value::Reg(0),
                    },
                ],
                terminator: Terminator::Ret {
                    val: Value::Reg(6),
                    ty: IrTy::Record(None, vec![IrTy::Int]),
                },
            }]
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
            *program.functions.get(&Symbol::Main).unwrap(),
            Function {
                name: Symbol::Main,
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
                            self_dest: None,
                            meta: meta()
                        }
                    ],
                    terminator: Terminator::Ret {
                        val: Value::Reg(1),
                        ty: IrTy::Int
                    }
                }],
                self_out: None,
            }
        );
        assert_eq!(
            *program
                .functions
                .get(&Symbol::from(GlobalId::from(1)))
                .unwrap(),
            Function {
                name: GlobalId::from(1).into(),
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
                self_out: Some(Register(0)),
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

        assert_eq!(
            program
                .record_labels
                .get(&RecordId::Nominal(Symbol::Struct(StructId::from(1))))
                .unwrap(),
            &["bar".to_string()]
        );

        assert_eq_diff!(
            *program.functions.get(&Symbol::Main).unwrap(),
            Function {
                name: Symbol::Main,
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
                            self_dest: None,
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
                self_out: None,
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
            *program.functions.get(&Symbol::Main).unwrap(),
            Function {
                name: Symbol::Main,
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
                            callee: Value::Func(Symbol::from(SynthesizedId::from(2))),
                            args: vec![Register(2).into(), Register(1).into()].into(),
                            self_dest: None,
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
                self_out: None,
            }
        );
    }

    #[test]
    fn lowers_enum_constructor_with_no_vals() {
        let program = lower("enum Fizz { case foo, bar } ; Fizz.bar");
        assert_eq_diff!(
            *program.functions.get(&Symbol::Main).unwrap(),
            Function {
                name: Symbol::Main,
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
                self_out: None,
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
            *program.functions.get(&Symbol::Main).unwrap(),
            Function {
                name: Symbol::Main,
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
                            dest: 1.into(),
                            val: 1.23.into(),
                            meta: meta()
                        },
                        Instruction::Constant {
                            ty: IrTy::Int,
                            dest: 2.into(),
                            val: 456.into(),
                            meta: meta()
                        },
                        Instruction::Nominal {
                            sym: Symbol::Enum(EnumId::from(1)),
                            dest: 0.into(),
                            ty: IrTy::Record(
                                Some(Symbol::Enum(EnumId::from(1))),
                                vec![IrTy::Int, IrTy::Float, IrTy::Int]
                            ),
                            record: vec![Value::Int(1), Value::Reg(1), Value::Reg(2)].into(),
                            meta: meta()
                        }
                    ],
                    terminator: Terminator::Ret {
                        val: Value::Reg(0),
                        ty: IrTy::Record(
                            Some(Symbol::Enum(EnumId::from(1))),
                            vec![IrTy::Int, IrTy::Float, IrTy::Int]
                        ),
                    }
                }],
                self_out: None,
            }
        )
    }

    #[test]
    fn lowers_add() {
        let program = lower("1 + 2");
        assert_eq_diff!(
            *program.functions.get(&Symbol::Main).unwrap(),
            Function {
                name: Symbol::Main,
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
                            self_dest: None,
                            meta: meta()
                        },
                    ],
                    terminator: Terminator::Ret {
                        val: Value::Reg(0),
                        ty: IrTy::Int
                    }
                }],
                self_out: None,
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
        let (module, display_names) = lower_module("1 <= 2");
        let _s = set_symbol_names(display_names.clone());
        let program = module.program;

        // The original lte method should still be imported
        assert!(
            program
                .functions
                .get(&Symbol::InstanceMethod(InstanceMethodId {
                    module_id: ModuleId::Core,
                    local_id: 18
                }))
                .is_some(),
            "did not find {:?} in {:?}",
            Symbol::InstanceMethod(InstanceMethodId {
                module_id: ModuleId::Core,
                local_id: 18
            }),
            program.functions.keys().collect_vec()
        );

        // There should be a specialized function for lte with witnesses
        let _s = set_symbol_names(display_names.clone());
        let has_specialization = program
            .functions
            .values()
            .any(|f| format!("{f}").contains("lte"));
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
            *program.functions.get(&Symbol::Main).unwrap(),
            Function {
                name: Symbol::Main,
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
                            self_dest: None,
                            meta: meta(),
                        },
                        Instruction::Call {
                            dest: 0.into(),
                            ty: IrTy::Int,
                            callee: Value::Func(InstanceMethodId::from(1).into()),
                            args: vec![Register(1).into()].into(),
                            self_dest: None,
                            meta: meta(),
                        },
                    ],
                    terminator: Terminator::Ret {
                        val: Value::Reg(0),
                        ty: IrTy::Int
                    }
                }],
                self_out: None,
            }
        );
    }

    #[test]
    fn simple_embedded_ir() {
        let program = lower(
            "
        @_ir { %? = add Int 1 2 }
        ",
        );
        assert_eq!(
            program.functions,
            indexmap::indexmap!(Symbol::Main => Function {
                name: Symbol::Main,
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
                        meta: meta(),
                    }],
                    terminator: Terminator::Ret {
                        val: Value::Reg(0),
                        ty: IrTy::Int
                    }
                }],
                self_out: None,
            })
        );
    }

    #[test]
    fn embedded_ir_uses_variables() {
        let program = lower(
            "
        @_ir(1, 2) { %? = add Int $0 $1 }
        ",
        );
        assert_eq!(
            *program.functions.get(&Symbol::Main).unwrap(),
            Function {
                name: Symbol::Main,
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
                            meta: meta()
                        }
                    ],
                    terminator: Terminator::Ret {
                        val: Value::Reg(2),
                        ty: IrTy::Int
                    }
                }],
                self_out: None,
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
            *program.functions.get(&Symbol::Main).unwrap(),
            Function {
                name: Symbol::Main,
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
                            callee: Value::Func(SynthesizedId::from(1).into()),
                            args: vec![Value::Reg(2)].into(),
                            self_dest: None,
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
                            callee: Value::Func(SynthesizedId::from(2).into()),
                            args: vec![Value::Reg(4)].into(),
                            self_dest: None,
                            meta: meta(),
                        },
                    ],
                    terminator: Terminator::Ret {
                        val: Value::Reg(3),
                        ty: IrTy::Float
                    }
                }],
                self_out: None,
            }
        );

        assert_eq_diff!(
            *program
                .functions
                .get(&Symbol::Synthesized(1.into()))
                .unwrap(),
            Function {
                name: Symbol::Synthesized(1.into()),
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
                self_out: Some(Register(0)),
            }
        );

        assert_eq_diff!(
            *program
                .functions
                .get(&Symbol::Synthesized(2.into()))
                .unwrap(),
            Function {
                name: Symbol::Synthesized(2.into()),
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
                self_out: Some(Register(0)),
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
            *program.functions.get(&Symbol::Main).unwrap(),
            Function::<IrTy> {
                name: Symbol::Main,
                params: vec![].into(),
                ty: IrTy::Func(vec![], IrTy::Int.into()),
                register_count: 3,
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
                            dest: Register(0),
                            ty: IrTy::Int,
                            val: Value::Int(456),
                            meta: meta()
                        }],
                        terminator: Terminator::Jump {
                            to: BasicBlockId(3)
                        }
                    },
                    BasicBlock {
                        id: BasicBlockId(2),
                        phis: Default::default(),
                        instructions: Default::default(),
                        terminator: Terminator::Jump {
                            to: BasicBlockId(3)
                        }
                    },
                    BasicBlock {
                        id: BasicBlockId(3),
                        phis: vec![Phi {
                            dest: 1.into(),
                            ty: IrTy::Int,
                            sources: vec![
                                PhiSource {
                                    from_id: BasicBlockId(1),
                                    value: Value::Reg(0)
                                },
                                PhiSource {
                                    from_id: BasicBlockId(2),
                                    value: Value::Void
                                }
                            ]
                            .into()
                        }],
                        instructions: vec![Instruction::Constant {
                            dest: 2.into(),
                            ty: IrTy::Int,
                            val: Value::Int(123),
                            meta: meta()
                        }],
                        terminator: Terminator::Ret {
                            val: Value::Reg(2),
                            ty: IrTy::Int
                        }
                    }
                ],
                self_out: None,
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
            *program.functions.get(&Symbol::Main).unwrap(),
            Function::<IrTy> {
                name: Symbol::Main,
                params: vec![].into(),
                ty: IrTy::Func(vec![], IrTy::Int.into()),
                register_count: 8,
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
                            conseq: BasicBlockId(5),
                            alt: BasicBlockId(8),
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
                        instructions: vec![],
                        terminator: Terminator::Jump {
                            to: BasicBlockId(2),
                        },
                    },
                    BasicBlock {
                        id: BasicBlockId(6),
                        phis: vec![],
                        instructions: vec![],
                        terminator: Terminator::Jump {
                            to: BasicBlockId(3),
                        },
                    },
                    BasicBlock {
                        id: BasicBlockId(7),
                        phis: vec![],
                        instructions: vec![],
                        terminator: Terminator::Jump {
                            to: BasicBlockId(4),
                        },
                    },
                    BasicBlock {
                        id: BasicBlockId(8),
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
                            conseq: BasicBlockId(6),
                            alt: BasicBlockId(9),
                        },
                    },
                    BasicBlock {
                        id: BasicBlockId(9),
                        phis: vec![],
                        instructions: vec![Instruction::Cmp {
                            dest: Register(7),
                            lhs: Value::Reg(1),
                            rhs: Value::Int(789),
                            ty: IrTy::Int,
                            op: CmpOperator::Equals,
                            meta: meta(),
                        },],
                        terminator: Terminator::Branch {
                            cond: Value::Reg(7),
                            conseq: BasicBlockId(7),
                            alt: BasicBlockId(10),
                        },
                    },
                    BasicBlock {
                        id: BasicBlockId(10),
                        phis: vec![],
                        instructions: vec![],
                        terminator: Terminator::Unreachable,
                    },
                ],
                self_out: None,
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

        assert_eq_diff!(
            program.functions.get(&Symbol::Main).unwrap().blocks,
            &[
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
                    br true #2 #3
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
            *program.functions.get(&Symbol::Main).unwrap().blocks,
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
    fn lowers_array_literal() {
        let program = lower("[1,2,3]");
        assert_eq_diff!(
            program.functions.get(&Symbol::Main).unwrap().blocks,
            &[BasicBlock {
                id: BasicBlockId(0),
                phis: Default::default(),
                instructions: vec![
                    Instruction::Constant {
                        dest: 0.into(),
                        ty: IrTy::Int,
                        val: Value::Int(1),
                        meta: meta()
                    },
                    Instruction::Constant {
                        dest: 1.into(),
                        ty: IrTy::Int,
                        val: Value::Int(2),
                        meta: meta()
                    },
                    Instruction::Constant {
                        dest: 2.into(),
                        ty: IrTy::Int,
                        val: Value::Int(3),
                        meta: meta()
                    },
                    Instruction::Record {
                        dest: 3.into(),
                        ty: IrTy::Record(None, vec![IrTy::Int, IrTy::Int, IrTy::Int]),
                        record: vec![Value::Reg(0), Value::Reg(1), Value::Reg(2)].into(),
                        meta: meta(),
                    },
                    Instruction::Alloc {
                        dest: 4.into(),
                        ty: IrTy::Record(None, vec![IrTy::Int, IrTy::Int, IrTy::Int]),
                        count: Value::Int(1)
                    },
                    Instruction::Store {
                        value: Value::Reg(3),
                        ty: IrTy::Record(None, vec![IrTy::Int, IrTy::Int, IrTy::Int]),
                        addr: Value::Reg(4),
                    },
                    Instruction::Nominal {
                        dest: 5.into(),
                        sym: Symbol::Array,
                        ty: IrTy::Record(
                            Some(Symbol::Array),
                            vec![IrTy::RawPtr, IrTy::Int, IrTy::Int]
                        ),
                        record: vec![Value::Reg(4), Value::Int(3), Value::Int(3)].into(),
                        meta: vec![
                            InstructionMeta::Source(NodeID::ANY),
                            InstructionMeta::RecordId(RecordId::Nominal(Symbol::Array)),
                        ]
                        .into(),
                    }
                ],
                terminator: Terminator::Ret {
                    val: Register(5).into(),
                    ty: IrTy::Record(
                        Some(Symbol::Array),
                        vec![IrTy::RawPtr, IrTy::Int, IrTy::Int]
                    ),
                }
            }]
        );
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

        assert_eq_diff!(
            program.functions.get(&Symbol::Main).unwrap().blocks,
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
                        self_dest: None,
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

    #[test]
    fn specializes_transitive_conformance_default_methods() {
        let module = lower_bare(
            "
            protocol A {
                func default() { 123 }
            }

            protocol B: A {
                func callsDefault() { self.default() }
            }

            extend Int: B {}

            123.callsDefault()
        ",
        );

        assert_eq!(
            *module.program.functions.get(&Symbol::Main).unwrap(),
            Function {
                name: Symbol::Main,
                params: vec![].into(),
                ty: IrTy::Func(vec![], IrTy::Int.into()),
                register_count: 2,
                blocks: vec![BasicBlock {
                    id: BasicBlockId(0),
                    phis: Default::default(),
                    instructions: vec![
                        Instruction::Constant {
                            ty: IrTy::Int,
                            dest: 1.into(),
                            val: 123.into(),
                            meta: meta(),
                        },
                        Instruction::Call {
                            dest: 0.into(),
                            ty: IrTy::Int,
                            callee: Value::Func(SynthesizedId::from(1).into()),
                            args: vec![Register(1).into()].into(),
                            self_dest: None,
                            meta: meta(),
                        },
                    ],
                    terminator: Terminator::Ret {
                        val: Value::Reg(0),
                        ty: IrTy::Int,
                    },
                }],
                self_out: None,
            }
        );

        assert_eq_diff!(
            *module
                .program
                .functions
                .get(&Symbol::Synthesized(SynthesizedId::from(1)))
                .unwrap(),
            Function {
                name: Symbol::Synthesized(SynthesizedId::from(1)),
                params: vec![Value::Reg(0)].into(),
                ty: IrTy::Func(vec![IrTy::Int], IrTy::Int.into()),
                register_count: 3,
                blocks: vec![BasicBlock {
                    id: BasicBlockId(0),
                    phis: Default::default(),
                    instructions: vec![
                        Instruction::Constant {
                            dest: 2.into(),
                            ty: IrTy::Int,
                            val: Register(0).into(),
                            meta: Default::default(),
                        },
                        Instruction::Call {
                            dest: 1.into(),
                            ty: IrTy::Int,
                            callee: Value::Func(InstanceMethodId::from(1).into()),
                            args: vec![Register(0).into()].into(),
                            self_dest: Some(Register(2)),
                            meta: meta(),
                        },
                    ],
                    terminator: Terminator::Ret {
                        val: Value::Reg(1),
                        ty: IrTy::Int,
                    },
                }],
                self_out: Some(Register(2)),
            }
        );
    }

    #[test]
    fn lowers_simple_effect() {
        let module = lower_bare(
            "
        effect 'fizz(x: Int) -> Int

        @handle 'fizz { x in
            continue x
        }

        func fizzes() {
            let a = 1
            let b = 'fizz(2)
            (a, b)
        }
        ",
        );

        println!("{}", module.program);

        assert_eq!(
            *module
                .program
                .functions
                .get(&Symbol::Global(GlobalId::from(1)))
                .unwrap(),
            Function::<IrTy> {
                name: GlobalId::from(1).into(),
                params: vec![].into(),
                blocks: vec![BasicBlock {
                    id: BasicBlockId(0),
                    phis: Default::default(),
                    instructions: vec![
                        Instruction::Constant {
                            dest: 0.into(),
                            ty: IrTy::Int,
                            val: Value::Int(1),
                            meta: meta()
                        },
                        Instruction::Constant {
                            dest: 2.into(),
                            ty: IrTy::Int,
                            val: Value::Int(2),
                            meta: meta()
                        },
                        Instruction::Ref {
                            dest: 3.into(),
                            ty: IrTy::Record(None, vec![IrTy::Int, IrTy::Int]),
                            val: Value::Closure {
                                func: Symbol::Synthesized(SynthesizedId::from(2)),
                                env: vec![Value::Reg(0), Value::Reg(1)].into()
                            },
                        },
                        Instruction::Call {
                            dest: 1.into(),
                            ty: IrTy::Func(vec![IrTy::Int], IrTy::Void.into()),
                            callee: Value::Func(Symbol::Effect(EffectId::from(1))),
                            args: vec![Value::Reg(3), Value::Reg(2)].into(),
                            self_dest: None,
                            meta: meta()
                        }
                    ],
                    terminator: Terminator::Ret {
                        val: Value::Reg(1),
                        ty: IrTy::Record(None, vec![IrTy::Int, IrTy::Int])
                    }
                }],
                ty: IrTy::Func(
                    vec![],
                    IrTy::Record(None, vec![IrTy::Int, IrTy::Int]).into()
                ),
                register_count: 4,
                self_out: None,
            }
        );
    }
}
