use crate::lowering::{
    instr::Instr,
    ir_module::IRModule,
    ir_type::IRType,
    lowerer::{BasicBlock, BasicBlockID, IRFunction, RefKind, Register},
};

pub fn print(program: &IRModule) -> String {
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
        print_func_sig_with_args(func.args(), &func.env_ty, func.ret())
    )
}

fn print_func_sig_with_args(args: &[IRType], env_ty: &IRType, ret: &IRType) -> String {
    let mut res = String::new();

    res.push('(');
    res.push_str(&format!("{env_ty} %0"));

    for (i, arg) in args.iter().enumerate() {
        // if i > 0 {
        res.push_str(", ");
        // }

        res.push_str(&format!(
            "{} {}",
            &format_ir_ty(arg),
            &format_register(&Register(i as i32))
        ));
    }

    res.push(')');
    res.push(' ');
    res.push_str(&format_ir_ty(ret));

    res
}

pub fn format_ir_ty(ty: &IRType) -> String {
    format!("{ty}")
}

pub fn format_optional_register(reg: &Option<Register>) -> String {
    match reg {
        Some(reg) => format_register(reg),
        None => "void".into(),
    }
}

pub fn format_registers(args: &[Register]) -> String {
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
    format!("{instruction}")
}

pub fn format_args(args: &[Register]) -> String {
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
    use crate::{
        SymbolTable, check,
        lowering::{
            ir_module::IRModule,
            ir_printer::print,
            lowerer::{IRError, Lowerer},
        },
    };

    fn lower(input: &'static str) -> Result<IRModule, IRError> {
        let typed = check(input).unwrap();
        let mut symbol_table = SymbolTable::default();
        let lowerer = Lowerer::new(typed, &mut symbol_table);
        let mut module = IRModule::new();
        lowerer.lower(&mut module)?;
        Ok(module)
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
            func.trim(),
            r#"func @_5_add({} %0, int %0) int
  entry:
    %2 = int 1;
    %3 = add int %2, %1;
    ret int %3;

func @main({} %0) void
  entry:
    %1 = alloc {ptr, ptr};
    %2 = struct {} ();
    %3 = alloc {};
    store {} %2 %3;
    %4 = ref (int) int @_5_add;
    %5 = getelementptr {ptr, ptr} %1 1;
    %6 = getelementptr {ptr, ptr} %1 0;
    store ptr %3 %5;
    store ptr %4 %6;
    ret ptr %1;
                "#
            .trim()
        )
    }
}
