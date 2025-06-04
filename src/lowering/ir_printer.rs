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
        buffer: String,
        indent_level: usize,
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

        fn print_basic_block(&mut self, block: &BasicBlock) {
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

        fn print_instruction(&mut self, instr: &Instr) {
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

        fn print_terminator(&mut self, terminator: &Terminator) {
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
        fn format_register(reg: &Register) -> String {
            format!("%{}", reg.0)
        }

        fn format_block_id(id: BasicBlockID) -> String {
            if id.0 == 0 {
                "entry".to_string()
            } else {
                format!("bb{}", id.0)
            }
        }

        fn format_block_label(id: BasicBlockID) -> String {
            format!("^{}", Self::format_block_id(id))
        }

        fn format_symbol_id(id: &SymbolID) -> String {
            match id.0 {
                i32::MIN => "main".to_string(),
                id if id < 0 => format!("builtin_{}", -id),
                id => format!("sym_{}", id),
            }
        }

        fn format_name(name: &Name) -> String {
            match name {
                Name::Raw(s) => s.clone(),
                Name::Resolved(_, s) => s.clone(),
            }
        }

        // Indentation helpers
        fn indent(&mut self) {
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
