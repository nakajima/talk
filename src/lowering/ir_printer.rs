use crate::lowering::{
    instr::Instr,
    lowerer::{BasicBlock, BasicBlockID, IRFunction, IRProgram, IRType, RefKind, Register},
};

pub fn print(program: &IRProgram) -> String {
    let mut printer = IRPrinter::default();
    for func in &program.functions {
        print_func(func, &mut printer);
    }
    printer.buffer
}

#[derive(Default)]
pub struct IRPrinter {
    pub buffer: String,
    pub indent_level: usize,
}

impl IRPrinter {
    fn puts(&mut self, line: &str) {
        for _ in 0..self.indent_level {
            self.buffer.push_str("  ");
        }
        self.buffer.push_str(line);
        self.buffer.push('\n');
    }
}

fn print_func(func: &IRFunction, printer: &mut IRPrinter) {
    printer.puts(&print_func_def(func));
    printer.indent_level += 1;
    for block in &func.blocks {
        print_basic_block(block, printer)
    }
    printer.indent_level -= 1;
    printer.puts("");
}

fn print_func_def(func: &IRFunction) -> String {
    format!(
        "func {}{}",
        func.name,
        print_func_sig(func.args(), func.ret())
    )
}

fn print_func_sig(args: &[IRType], ret: &IRType) -> String {
    let mut res = String::new();

    res.push('(');

    for (i, arg) in args.iter().enumerate() {
        if i > 0 {
            res.push_str(", ");
        }

        res.push_str(&format!(
            "{} {}",
            &format_ir_ty(arg),
            format_register(&Register(i as u32)),
        ));
    }

    res.push(')');
    res.push(' ');
    res.push_str(&format_ir_ty(ret));

    res
}

fn format_ir_ty(ty: &IRType) -> String {
    match ty {
        IRType::Bool => "bool".into(),
        IRType::Void => "void".into(),
        IRType::Int => "int".into(),
        IRType::Float => "float".into(),
        IRType::Func(args, ret) => print_func_sig(args, ret),
        IRType::TypeVar(name) => name.into(),
        IRType::Enum(types) => format!(
            "enum({})",
            types
                .iter()
                .map(format_ir_ty)
                .collect::<Vec<String>>()
                .join(", ")
        ),
    }
}

fn print_basic_block(block: &BasicBlock, printer: &mut IRPrinter) {
    printer.puts(&format!("{}:", format_block_id(&block.id)));
    printer.indent_level += 1;

    for instruction in &block.instructions {
        printer.puts(&format_instruction(instruction))
    }

    printer.indent_level -= 1;
}

fn format_instruction(instruction: &Instr) -> String {
    match instruction {
        Instr::ConstantInt(register, val) => {
            format!("{} = int {};", format_register(register), val)
        }
        Instr::ConstantFloat(register, val) => {
            format!("{} = float {};", format_register(register), val)
        }
        Instr::ConstantBool(register, val) => {
            format!("{} = bool {};", format_register(register), val)
        }
        Instr::Add(dest, ty, lhs, rhs) => {
            format!(
                "{} = add {} {}, {};",
                format_register(dest),
                format_ir_ty(ty),
                format_register(lhs),
                format_register(rhs)
            )
        }
        Instr::Sub(dest, ty, lhs, rhs) => format!(
            "{} = sub {} {}, {};",
            format_register(dest),
            format_ir_ty(ty),
            format_register(lhs),
            format_register(rhs)
        ),
        Instr::Mul(dest, ty, lhs, rhs) => format!(
            "{} = mul {} {}, {};",
            format_register(dest),
            format_ir_ty(ty),
            format_register(lhs),
            format_register(rhs)
        ),
        Instr::Div(dest, ty, lhs, rhs) => format!(
            "{} = div {} {}, {};",
            format_register(dest),
            format_ir_ty(ty),
            format_register(lhs),
            format_register(rhs)
        ),
        Instr::StoreLocal(_register, _irtype, _register1) => todo!(),
        Instr::LoadLocal(_register, _irtype, _register1) => todo!(),
        Instr::Phi(register, irtype, items) => {
            let phi_args = items
                .iter()
                .map(|(reg, bb)| format!("{}: {}", format_block_id(bb), format_register(reg)))
                .collect::<Vec<_>>()
                .join(", ");

            format!(
                "{} = phi {} [{}];",
                format_register(register),
                format_ir_ty(irtype),
                phi_args
            )
        }
        Instr::Ref(register, _ty, RefKind::Func(name)) => {
            format!("{} = {};", format_register(register), name)
        }
        Instr::Call {
            dest_reg,
            callee,
            args,
            ty: ret,
        } => format!(
            "{} = call {} {}{};",
            if let Some(dest) = dest_reg {
                format_register(dest)
            } else {
                "void".into()
            },
            format_ir_ty(ret),
            callee,
            format_args(args)
        ),
        Instr::JumpUnless(register, basic_block_id) => format!(
            "jump_unless {} {};",
            format_register(register),
            format_block_id(basic_block_id)
        ),
        Instr::JumpIf(register, basic_block_id) => format!(
            "jump_if {} {};",
            format_register(register),
            format_block_id(basic_block_id)
        ),
        Instr::Ret(ret) => format!(
            "ret{};",
            if let Some((ty, register)) = ret {
                format!(" {} {}", format_ir_ty(ty), format_register(register))
            } else {
                "".into()
            }
        ),
        Instr::Unreachable => "unreachable".to_string(),
        Instr::Jump(basic_block_id) => format!("jump {}", basic_block_id.0),
        Instr::TagVariant(dest, IRType::Enum(generics), tag, values) => format!(
            "{} = tag {} [{}] {}",
            format_register(dest),
            tag,
            format_args(values),
            {
                let strings = generics.iter().map(format_ir_ty).collect::<Vec<String>>();
                strings.join(", ")
            }
        ),
        Instr::TagVariant(_, _, _, _) => todo!(),
        Instr::Eq(dest, ty, op1, op2) => {
            format!(
                "{} = eq {} {} {}",
                format_register(dest),
                format_ir_ty(ty),
                format_register(op1),
                format_register(op2)
            )
        }
        Instr::Ne(dest, ty, op1, op2) => {
            format!(
                "{} = ne {} {} {}",
                format_register(dest),
                format_ir_ty(ty),
                format_register(op1),
                format_register(op2)
            )
        }
        Instr::GetEnumTag(dest, tag) => {
            format!(
                "{} = gettag {}",
                format_register(dest),
                format_register(tag)
            )
        }
        Instr::GetEnumValue(dest, ty, scrutinee, tag, index) => {
            format!(
                "{} = getval {} {} {} {}",
                format_register(dest),
                format_ir_ty(ty),
                format_register(scrutinee),
                tag,
                index
            )
        }
        Instr::LessThan(register, irtype, register1, register2) => {
            format!(
                "{} = lt {} {} {};",
                format_register(register),
                format_ir_ty(irtype),
                format_register(register1),
                format_register(register2)
            )
        }
        Instr::LessThanEq(register, irtype, register1, register2) => {
            format!(
                "{} = lte {} {} {};",
                format_register(register),
                format_ir_ty(irtype),
                format_register(register1),
                format_register(register2)
            )
        }
        Instr::GreaterThan(register, irtype, register1, register2) => {
            format!(
                "{} = gt {} {} {};",
                format_register(register),
                format_ir_ty(irtype),
                format_register(register1),
                format_register(register2)
            )
        }
        Instr::GreaterThanEq(register, irtype, register1, register2) => {
            format!(
                "{} = gte {} {} {};",
                format_register(register),
                format_ir_ty(irtype),
                format_register(register1),
                format_register(register2)
            )
        }
    }
}

fn format_args(args: &Vec<Register>) -> String {
    let mut res = String::new();

    res.push('(');
    for (i, arg) in args.iter().enumerate() {
        if i > 0 {
            res.push_str(", ");
        }

        res.push_str(&format_register(arg));
    }

    res.push(')');
    res
}

fn format_register(register: &Register) -> String {
    format!("%{}", register.0)
}

fn format_block_id(id: &BasicBlockID) -> String {
    if id.0 == 0 {
        "entry".to_string()
    } else {
        format!("#{}", id.0)
    }
}

#[cfg(test)]
mod tests {
    use indoc::formatdoc;

    use crate::{
        check,
        lowering::{
            ir_printer::print,
            lowerer::{IRError, IRProgram, Lowerer},
        },
    };

    fn lower(input: &'static str) -> Result<IRProgram, IRError> {
        let typed = check(input).unwrap();
        let lowerer = Lowerer::new(typed);
        lowerer.lower()
    }

    #[test]
    fn prints_func() {
        let program = lower(
            "
        func add(x) { 1 + x }
        ",
        )
        .unwrap();

        let func = print(&program);
        assert_eq!(
            func,
            formatdoc!(
                r#"
                func @_5_add(int %0) int
                  entry:
                    %1 = int 1;
                    %2 = add int %1, %0;
                    ret int %2;

                func @main() void
                  entry:
                    %0 = @_5_add;
                    ret (int %0) int %0;

                "#
            )
        )
    }
}
