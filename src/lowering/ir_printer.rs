pub use self::printer::{IRPrinter, pretty_print_ir};

mod printer {
    use crate::{
        SymbolID,
        lowering::ir::{
            BasicBlock, BasicBlockID, IRFunction, Instr, RefKind, Register, Terminator,
        },
        name::Name,
    };

    pub struct IRPrinter {
        pub buffer: String,
        pub indent_level: usize,
    }

    impl IRPrinter {
        pub fn new() -> Self {
            Self {
                buffer: String::new(),
                indent_level: 0,
            }
        }

        pub fn print_functions(&mut self, functions: &[IRFunction]) -> String {
            for (i, function) in functions.iter().enumerate() {
                if i > 0 {
                    self.write_line("");
                }
                self.print_function(function);
            }
            self.buffer.clone()
        }

        pub fn print_function(&mut self, function: &IRFunction) {
            // Function signature
            self.write(&format!(
                "@{} : $() -> () {{",
                Self::format_name(&function.name)
            ));
            self.write_line("");

            // Function body
            self.indent();
            for (i, block) in function.blocks.iter().enumerate() {
                if i > 0 {
                    self.write_line("");
                }
                self.print_basic_block(block);
            }
            self.dedent();

            self.write_line("}");
        }

        pub(super) fn print_basic_block(&mut self, block: &BasicBlock) {
            // Block label
            let label = block.label.as_ref().map(|l| l.as_str()).unwrap_or("entry");
            self.write(&format!("{}:", label));

            // Predecessors comment (if not entry block)
            if block.id.0 > 0 {
                self.write(&format!(" // preds: {}", Self::format_block_id(block.id)));
            }
            self.write_line("");

            // Instructions
            self.indent();
            for instr in &block.instructions {
                self.print_instruction(instr);
            }

            // Terminator
            self.print_terminator(&block.terminator);
            self.dedent();
        }

        pub(super) fn print_instruction(&mut self, instr: &Instr) {
            match instr {
                Instr::ConstantInt(reg, value) => {
                    self.write_line(&format!(
                        "{} = constant ${} : Int",
                        Self::format_register(reg),
                        value
                    ));
                }
                Instr::ConstantFloat(reg, value) => {
                    self.write_line(&format!(
                        "{} = constant ${} : Float",
                        Self::format_register(reg),
                        value
                    ));
                }
                Instr::ConstantBool(reg, value) => {
                    self.write_line(&format!(
                        "{} = constant ${} : Bool",
                        Self::format_register(reg),
                        if *value { "true" } else { "false" }
                    ));
                }
                Instr::Add(dest, lhs, rhs) => {
                    self.write_line(&format!(
                        "{} = add {}, {} : Int",
                        Self::format_register(dest),
                        Self::format_register(lhs),
                        Self::format_register(rhs)
                    ));
                }
                Instr::Sub(dest, lhs, rhs) => {
                    self.write_line(&format!(
                        "{} = sub {}, {} : Int",
                        Self::format_register(dest),
                        Self::format_register(lhs),
                        Self::format_register(rhs)
                    ));
                }
                Instr::Mul(dest, lhs, rhs) => {
                    self.write_line(&format!(
                        "{} = mul {}, {} : Int",
                        Self::format_register(dest),
                        Self::format_register(lhs),
                        Self::format_register(rhs)
                    ));
                }
                Instr::Div(dest, lhs, rhs) => {
                    self.write_line(&format!(
                        "{} = div {}, {} : Int",
                        Self::format_register(dest),
                        Self::format_register(lhs),
                        Self::format_register(rhs)
                    ));
                }
                Instr::StoreLocal(dest, src) => {
                    self.write_line(&format!(
                        "store {} to {}",
                        Self::format_register(src),
                        Self::format_register(dest)
                    ));
                }
                Instr::LoadLocal(dest, src) => {
                    self.write_line(&format!(
                        "{} = load {}",
                        Self::format_register(dest),
                        Self::format_register(src)
                    ));
                }
                Instr::Phi(dest, sources) => {
                    let phi_args = sources
                        .iter()
                        .map(|(reg, bb)| {
                            format!(
                                "{}: {}",
                                Self::format_block_id(*bb),
                                Self::format_register(reg)
                            )
                        })
                        .collect::<Vec<_>>()
                        .join(", ");
                    self.write_line(&format!(
                        "{} = phi [{}]",
                        Self::format_register(dest),
                        phi_args
                    ));
                }
                Instr::Ref(dest, ref_kind) => match ref_kind {
                    RefKind::Func(symbol_id) => {
                        self.write_line(&format!(
                            "{} = function_ref @{} : $() -> ()",
                            Self::format_register(dest),
                            Self::format_symbol_id(symbol_id)
                        ));
                    }
                },
                Instr::Call {
                    dest_reg,
                    callee,
                    args,
                } => {
                    let args_str = args
                        .iter()
                        .map(Self::format_register)
                        .collect::<Vec<_>>()
                        .join(", ");

                    if let Some(dest) = dest_reg {
                        self.write_line(&format!(
                            "{} = apply @{}({}) : $() -> ()",
                            Self::format_register(dest),
                            Self::format_symbol_id(callee),
                            args_str
                        ));
                    } else {
                        self.write_line(&format!(
                            "apply @{}({}) : $() -> ()",
                            Self::format_symbol_id(callee),
                            args_str
                        ));
                    }
                }
            }
        }

        pub(super) fn print_terminator(&mut self, terminator: &Terminator) {
            match terminator {
                Terminator::Ret(Some(reg)) => {
                    self.write_line(&format!("return {}", Self::format_register(reg)));
                }
                Terminator::Ret(None) => {
                    self.write_line("return");
                }
                Terminator::Unreachable => {
                    self.write_line("unreachable");
                }
                Terminator::Jump(target) => {
                    self.write_line(&format!("br {}", Self::format_block_label(*target)));
                }
                Terminator::JumpUnless(cond, target) => {
                    self.write_line(&format!(
                        "cond_br {}, ^cont, {}",
                        Self::format_register(cond),
                        Self::format_block_label(*target)
                    ));
                }
            }
        }

        // Formatting helpers
        pub(super) fn format_register(reg: &Register) -> String {
            format!("%{}", reg.0)
        }

        pub(super) fn format_block_id(id: BasicBlockID) -> String {
            if id.0 == 0 {
                "entry".to_string()
            } else {
                format!("bb{}", id.0)
            }
        }

        pub(super) fn format_block_label(id: BasicBlockID) -> String {
            format!("^{}", Self::format_block_id(id))
        }

        pub(super) fn format_symbol_id(id: &SymbolID) -> String {
            match id.0 {
                i32::MIN => "main".to_string(),
                id if id < 0 => format!("builtin_{}", -id),
                id => format!("sym_{}", id),
            }
        }

        pub(super) fn format_name(name: &Name) -> String {
            match name {
                Name::Raw(s) => s.clone(),
                Name::Resolved(_, s) => s.clone(),
            }
        }

        // Indentation helpers
        pub(super) fn indent(&mut self) {
            self.indent_level += 1;
        }

        fn dedent(&mut self) {
            self.indent_level = self.indent_level.saturating_sub(1);
        }

        fn write(&mut self, s: &str) {
            self.buffer.push_str(s);
        }

        fn write_line(&mut self, s: &str) {
            for _ in 0..self.indent_level {
                self.buffer.push_str("  ");
            }
            self.buffer.push_str(s);
            self.buffer.push('\n');
        }
    }

    // Pretty print extension for IRFunction
    impl IRFunction {
        pub fn pretty_print(&self) -> String {
            let mut printer = IRPrinter::new();
            printer.print_function(self);
            printer.buffer
        }
    }

    // Pretty print for a vector of functions
    pub fn pretty_print_ir(functions: &[IRFunction]) -> String {
        let mut printer = IRPrinter::new();
        printer.print_functions(functions)
    }

    // Display implementation for easier debugging
    impl std::fmt::Display for IRFunction {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            write!(f, "{}", self.pretty_print())
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        SymbolID,
        lowering::ir::{
            BasicBlock, BasicBlockID, IRFunction, Instr, RefKind, Register, Terminator,
        },
        name::Name,
        type_checker::Ty,
    };

    #[test]
    fn test_format_register() {
        assert_eq!(IRPrinter::format_register(&Register(0)), "%0");
        assert_eq!(IRPrinter::format_register(&Register(42)), "%42");
        assert_eq!(IRPrinter::format_register(&Register(999)), "%999");
    }

    #[test]
    fn test_format_block_id() {
        assert_eq!(IRPrinter::format_block_id(BasicBlockID(0)), "entry");
        assert_eq!(IRPrinter::format_block_id(BasicBlockID(1)), "bb1");
        assert_eq!(IRPrinter::format_block_id(BasicBlockID(42)), "bb42");
    }

    #[test]
    fn test_format_block_label() {
        assert_eq!(IRPrinter::format_block_label(BasicBlockID(0)), "^entry");
        assert_eq!(IRPrinter::format_block_label(BasicBlockID(1)), "^bb1");
        assert_eq!(IRPrinter::format_block_label(BasicBlockID(42)), "^bb42");
    }

    #[test]
    fn test_format_symbol_id() {
        assert_eq!(IRPrinter::format_symbol_id(&SymbolID(i32::MIN)), "main");
        assert_eq!(IRPrinter::format_symbol_id(&SymbolID(-1)), "builtin_1");
        assert_eq!(IRPrinter::format_symbol_id(&SymbolID(-5)), "builtin_5");
        assert_eq!(IRPrinter::format_symbol_id(&SymbolID(0)), "sym_0");
        assert_eq!(IRPrinter::format_symbol_id(&SymbolID(42)), "sym_42");
    }

    #[test]
    fn test_format_name() {
        assert_eq!(
            IRPrinter::format_name(&Name::Raw("hello".to_string())),
            "hello"
        );
        assert_eq!(
            IRPrinter::format_name(&Name::Resolved(SymbolID(1), "world".to_string())),
            "world"
        );
    }

    #[test]
    fn test_print_constant_int() {
        let mut printer = IRPrinter::new();
        printer.indent();
        printer.print_instruction(&Instr::ConstantInt(Register(0), 123));
        assert_eq!(printer.buffer, "  %0 = constant $123 : Int\n");
    }

    #[test]
    fn test_print_constant_float() {
        let mut printer = IRPrinter::new();
        printer.indent();
        printer.print_instruction(&Instr::ConstantFloat(Register(1), 3.14));
        assert_eq!(printer.buffer, "  %1 = constant $3.14 : Float\n");
    }

    #[test]
    fn test_print_constant_bool() {
        let mut printer = IRPrinter::new();
        printer.indent();
        printer.print_instruction(&Instr::ConstantBool(Register(2), true));
        assert_eq!(printer.buffer, "  %2 = constant $true : Bool\n");

        let mut printer = IRPrinter::new();
        printer.indent();
        printer.print_instruction(&Instr::ConstantBool(Register(3), false));
        assert_eq!(printer.buffer, "  %3 = constant $false : Bool\n");
    }

    #[test]
    fn test_print_arithmetic_instructions() {
        let mut printer = IRPrinter::new();
        printer.indent();

        printer.print_instruction(&Instr::Add(Register(2), Register(0), Register(1)));
        printer.print_instruction(&Instr::Sub(Register(3), Register(2), Register(1)));
        printer.print_instruction(&Instr::Mul(Register(4), Register(3), Register(0)));
        printer.print_instruction(&Instr::Div(Register(5), Register(4), Register(2)));

        let expected = "  %2 = add %0, %1 : Int\n  %3 = sub %2, %1 : Int\n  %4 = mul %3, %0 : Int\n  %5 = div %4, %2 : Int\n";
        assert_eq!(printer.buffer, expected);
    }

    #[test]
    fn test_print_phi_instruction() {
        let mut printer = IRPrinter::new();
        printer.indent();

        let phi = Instr::Phi(
            Register(3),
            vec![
                (Register(1), BasicBlockID(1)),
                (Register(2), BasicBlockID(2)),
            ],
        );
        printer.print_instruction(&phi);

        assert_eq!(printer.buffer, "  %3 = phi [bb1: %1, bb2: %2]\n");
    }

    #[test]
    fn test_print_function_ref() {
        let mut printer = IRPrinter::new();
        printer.indent();

        let ref_instr = Instr::Ref(Register(0), RefKind::Func(SymbolID(42)));
        printer.print_instruction(&ref_instr);

        assert_eq!(printer.buffer, "  %0 = function_ref @sym_42 : $() -> ()\n");
    }

    #[test]
    fn test_print_call_with_result() {
        let mut printer = IRPrinter::new();
        printer.indent();

        let call = Instr::Call {
            dest_reg: Some(Register(5)),
            callee: SymbolID(1),
            args: vec![Register(2), Register(3)],
        };
        printer.print_instruction(&call);

        assert_eq!(printer.buffer, "  %5 = apply @sym_1(%2, %3) : $() -> ()\n");
    }

    #[test]
    fn test_print_call_without_result() {
        let mut printer = IRPrinter::new();
        printer.indent();

        let call = Instr::Call {
            dest_reg: None,
            callee: SymbolID(1),
            args: vec![Register(2)],
        };
        printer.print_instruction(&call);

        assert_eq!(printer.buffer, "  apply @sym_1(%2) : $() -> ()\n");
    }

    #[test]
    fn test_print_terminators() {
        let mut printer = IRPrinter::new();
        printer.indent();

        // Return with value
        printer.print_terminator(&Terminator::Ret(Some(Register(0))));
        assert_eq!(printer.buffer, "  return %0\n");

        // Return without value
        printer.buffer.clear();
        printer.print_terminator(&Terminator::Ret(None));
        assert_eq!(printer.buffer, "  return\n");

        // Unreachable
        printer.buffer.clear();
        printer.print_terminator(&Terminator::Unreachable);
        assert_eq!(printer.buffer, "  unreachable\n");

        // Jump
        printer.buffer.clear();
        printer.print_terminator(&Terminator::Jump(BasicBlockID(2)));
        assert_eq!(printer.buffer, "  br ^bb2\n");

        // Conditional jump
        printer.buffer.clear();
        printer.print_terminator(&Terminator::JumpUnless(Register(0), BasicBlockID(3)));
        assert_eq!(printer.buffer, "  cond_br %0, ^cont, ^bb3\n");
    }

    #[test]
    fn test_print_basic_block() {
        let block = BasicBlock {
            id: BasicBlockID(0),
            label: None,
            instructions: vec![
                Instr::ConstantInt(Register(0), 42),
                Instr::ConstantInt(Register(1), 10),
                Instr::Add(Register(2), Register(0), Register(1)),
            ],
            terminator: Terminator::Ret(Some(Register(2))),
        };

        let mut printer = IRPrinter::new();
        printer.print_basic_block(&block);

        let expected = "entry:\n  %0 = constant $42 : Int\n  %1 = constant $10 : Int\n  %2 = add %0, %1 : Int\n  return %2\n";
        assert_eq!(printer.buffer, expected);
    }

    #[test]
    fn test_print_basic_block_with_label() {
        let block = BasicBlock {
            id: BasicBlockID(1),
            label: Some("loop_header".to_string()),
            instructions: vec![],
            terminator: Terminator::Jump(BasicBlockID(2)),
        };

        let mut printer = IRPrinter::new();
        printer.print_basic_block(&block);

        let expected = "loop_header: // preds: bb1\n  br ^bb2\n";
        assert_eq!(printer.buffer, expected);
    }

    #[test]
    fn test_print_empty_function() {
        let function = IRFunction {
            ty: Ty::Func(vec![], Box::new(Ty::Void)),
            name: Name::Resolved(SymbolID(1), "empty".to_string()),
            blocks: vec![BasicBlock {
                id: BasicBlockID(0),
                label: None,
                instructions: vec![],
                terminator: Terminator::Ret(None),
            }],
        };

        let mut printer = IRPrinter::new();
        printer.print_function(&function);

        let expected = "@empty : $() -> () {\n  entry:\n    return\n}\n";
        assert_eq!(printer.buffer, expected);
    }

    #[test]
    fn test_print_multi_block_function() {
        let function = IRFunction {
            ty: Ty::Func(vec![], Box::new(Ty::Void)),
            name: Name::Resolved(SymbolID(1), "conditional".to_string()),
            blocks: vec![
                BasicBlock {
                    id: BasicBlockID(0),
                    label: None,
                    instructions: vec![Instr::ConstantBool(Register(0), true)],
                    terminator: Terminator::JumpUnless(Register(0), BasicBlockID(2)),
                },
                BasicBlock {
                    id: BasicBlockID(1),
                    label: Some("then".to_string()),
                    instructions: vec![Instr::ConstantInt(Register(1), 1)],
                    terminator: Terminator::Jump(BasicBlockID(3)),
                },
                BasicBlock {
                    id: BasicBlockID(2),
                    label: Some("else".to_string()),
                    instructions: vec![Instr::ConstantInt(Register(2), 0)],
                    terminator: Terminator::Jump(BasicBlockID(3)),
                },
                BasicBlock {
                    id: BasicBlockID(3),
                    label: Some("merge".to_string()),
                    instructions: vec![Instr::Phi(
                        Register(3),
                        vec![
                            (Register(1), BasicBlockID(1)),
                            (Register(2), BasicBlockID(2)),
                        ],
                    )],
                    terminator: Terminator::Ret(Some(Register(3))),
                },
            ],
        };

        let result = function.pretty_print();
        let expected = "@conditional : $() -> () {\n  entry:\n    %0 = constant $true : Bool\n    cond_br %0, ^cont, ^bb2\n\n  then: // preds: bb1\n    %1 = constant $1 : Int\n    br ^bb3\n\n  else: // preds: bb2\n    %2 = constant $0 : Int\n    br ^bb3\n\n  merge: // preds: bb3\n    %3 = phi [bb1: %1, bb2: %2]\n    return %3\n}\n";
        assert_eq!(result, expected);
    }

    #[test]
    fn test_pretty_print_ir_multiple_functions() {
        let functions = vec![
            IRFunction {
                ty: Ty::Func(vec![], Box::new(Ty::Void)),
                name: Name::Resolved(SymbolID(1), "foo".to_string()),
                blocks: vec![BasicBlock {
                    id: BasicBlockID(0),
                    label: None,
                    instructions: vec![Instr::ConstantInt(Register(0), 123)],
                    terminator: Terminator::Ret(Some(Register(0))),
                }],
            },
            IRFunction {
                ty: Ty::Func(vec![], Box::new(Ty::Void)),
                name: Name::Resolved(SymbolID(i32::MIN), "main".to_string()),
                blocks: vec![BasicBlock {
                    id: BasicBlockID(0),
                    label: None,
                    instructions: vec![
                        Instr::Ref(Register(0), RefKind::Func(SymbolID(1))),
                        Instr::Call {
                            dest_reg: Some(Register(1)),
                            callee: SymbolID(1),
                            args: vec![],
                        },
                    ],
                    terminator: Terminator::Ret(Some(Register(1))),
                }],
            },
        ];

        let result = pretty_print_ir(&functions);
        let expected = "@foo : $() -> () {\n  entry:\n    %0 = constant $123 : Int\n    return %0\n}\n\n@main : $() -> () {\n  entry:\n    %0 = function_ref @sym_1 : $() -> ()\n    %1 = apply @sym_1() : $() -> ()\n    return %1\n}\n";
        assert_eq!(result, expected);
    }

    #[test]
    fn test_display_implementation() {
        let function = IRFunction {
            ty: Ty::Func(vec![], Box::new(Ty::Void)),
            name: Name::Raw("test".to_string()),
            blocks: vec![BasicBlock {
                id: BasicBlockID(0),
                label: None,
                instructions: vec![],
                terminator: Terminator::Ret(None),
            }],
        };

        let display_output = format!("{}", function);
        let pretty_print_output = function.pretty_print();
        assert_eq!(display_output, pretty_print_output);
    }

    #[test]
    fn test_store_and_load_instructions() {
        let mut printer = IRPrinter::new();
        printer.indent();

        printer.print_instruction(&Instr::StoreLocal(Register(0), Register(1)));
        printer.print_instruction(&Instr::LoadLocal(Register(2), Register(0)));

        let expected = "  store %1 to %0\n  %2 = load %0\n";
        assert_eq!(printer.buffer, expected);
    }
}
