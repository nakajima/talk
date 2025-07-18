use crate::lowering::{
    instr::Instr,
    ir_function::IRFunction,
    ir_module::IRModule,
    ir_type::IRType,
    lowerer::{BasicBlock, BasicBlockID, RefKind},
    register::Register,
};

pub fn print(program: &IRModule) -> String {
    let mut printer = IRPrinter::default();
    printer.puts("Constants:");
    printer.indent_level = 2;
    for constant in program.constants.iter() {
        printer.puts(&format!("- {constant:?}",));
    }
    printer.indent_level = 0;
    for func in &program.functions {
        print_func(func, &mut printer);
    }
    printer.buffer
}

pub fn format_func(function: &IRFunction) -> String {
    let mut printer = IRPrinter::default();
    print_func(function, &mut printer);
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

    fn print(&mut self, line: &str) {
        for _ in 0..self.indent_level {
            self.buffer.push_str("  ");
        }
        self.buffer.push_str(line);
    }
}

fn print_func(func: &IRFunction, printer: &mut IRPrinter) {
    printer.print(&print_func_def(func));

    if func.blocks.is_empty() {
        printer.puts(";");
    } else {
        printer.puts("");
    }

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

fn print_func_sig_with_args(args: &[IRType], env_ty: &Option<IRType>, ret: &IRType) -> String {
    let mut res = String::new();

    res.push('(');

    let env_param_offset = if let Some(env_ty) = env_ty {
        res.push_str(&format!("{env_ty} %0"));
        1
    } else {
        0
    };

    for (i, arg) in args.iter().enumerate() {
        if env_param_offset > 0 {
            res.push_str(", ");
        }

        res.push_str(&format!(
            "{} {}",
            &format_ir_ty(arg),
            &format_register(&Register(i as i32 + env_param_offset))
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
        None => "Void".into(),
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
        SymbolID,
        compiling::driver::{Driver, DriverConfig},
        lowering::{ir_error::IRError, ir_module::IRModule, ir_printer::print},
    };

    fn lower(input: &'static str) -> Result<IRModule, IRError> {
        let mut driver = Driver::new(
            "IRPrinterTest",
            DriverConfig {
                executable: true,
                include_prelude: false,
                include_comments: false,
            },
        );
        driver.update_file(&"-".into(), input.into());
        let module = driver.lower().into_iter().next().unwrap().module();
        Ok(module)
    }

    #[test]
    fn prints_func() {
        let program = lower(
            "
        func add(x: Int) -> Int { x + 1 }
        ",
        )
        .unwrap();

        let func = print(&program);
        assert_eq!(
            func.trim(),
            format!(
                r#"Constants:
func @_{}_add(int %0) int
  entry:
    %1 = int 1;
    %2 = add int %0, %1;
    ret int %2;

func @main() void
  entry:
    %0 = ref (int) int @_{}_add;
    ret ptr %0;
                "#,
                SymbolID(1).0,
                SymbolID(1).0,
            )
            .trim()
        )
    }
}
