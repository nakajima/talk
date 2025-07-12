use iai::{black_box, main};
use talk::{
    analysis::module_pass_manager::ModulePassManager,
    compiling::driver::Driver,
    interpret::{interpreter::IRInterpreter, io::test_io::TestIO},
};

fn run(code: &str) {
    let mut driver = Driver::with_str(code);
    let lowered = driver.lower();
    let io = TestIO::new();
    for unit in lowered {
        let module = ModulePassManager::run(&unit.env, unit.module());
        let interpreter = IRInterpreter::new(module, &io, &driver.symbol_table);
        black_box(interpreter.run().unwrap());
    }
}

fn bench_fib() {
    const CODE: &str = r#"
func fib(n) {
    if n <= 1 { return n }
    fib(n - 2) + fib(n - 1)
}

let i = 0
let n = 0
loop i < 20 {
    n = fib(i)
    i = i + 1
}

n
"#;
    run(CODE);
}

fn bench_loop_sum() {
    const CODE: &str = r#"
let i = 0
let sum = 0
loop i < 1000 {
    sum = sum + i
    i = i + 1
}

sum
"#;
    run(CODE);
}

iai::main!(bench_fib, bench_loop_sum);
