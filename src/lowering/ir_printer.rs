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
        print_func_sig_with_args(func.args(), func.ret())
    )
}

fn print_func_sig(args: &[IRType], ret: &IRType) -> String {
    let mut res = String::new();

    res.push('(');

    for (i, arg) in args.iter().enumerate() {
        if i > 0 {
            res.push_str(", ");
        }

        res.push_str(&format!("{}", &format_ir_ty(arg),));
    }

    res.push(')');
    res.push(' ');
    res.push_str(&format_ir_ty(ret));

    res
}

fn print_func_sig_with_args(args: &[IRType], ret: &IRType) -> String {
    let mut res = String::new();

    res.push('(');

    for (i, arg) in args.iter().enumerate() {
        if i > 0 {
            res.push_str(", ");
        }

        res.push_str(&format!(
            "{} {}",
            &format_ir_ty(arg),
            &format_register(&Register(i as u32))
        ));
    }

    res.push(')');
    res.push(' ');
    res.push_str(&format_ir_ty(ret));

    res
}

pub fn format_ir_ty(ty: &IRType) -> String {
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

pub fn format_optional_register(reg: &Option<Register>) -> String {
    match reg {
        Some(reg) => format_register(reg),
        None => "void".into(),
    }
}

pub fn format_registers(args: &Vec<Register>) -> String {
    format_args(args)
}

pub fn format_ref_kind(kind: &RefKind) -> String {
    match kind {
        RefKind::Func(name) => name.into(),
    }
}

pub fn print_basic_block(block: &BasicBlock, printer: &mut IRPrinter) {
    printer.puts(&format!("{}:", format_block_id(&block.id)));
    printer.indent_level += 1;

    for instruction in &block.instructions {
        printer.puts(&format_instruction(instruction))
    }

    printer.indent_level -= 1;
}

pub fn format_instruction(instruction: &Instr) -> String {
    format!("{}", instruction)
}

pub fn format_args(args: &Vec<Register>) -> String {
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

pub fn format_register(register: &Register) -> String {
    format!("%{}", register.0)
}

pub fn format_block_id(id: &BasicBlockID) -> String {
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
                    %0 = ref (int) int @_5_add;
                    ret (int) int %0;

                "#
            )
        )
    }
}
