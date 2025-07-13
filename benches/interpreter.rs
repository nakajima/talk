use criterion::{Criterion, criterion_group, criterion_main};
use std::hint::black_box;
use talk::{
    analysis::module_pass_manager::ModulePassManager,
    compiling::driver::Driver,
    interpret::{interpreter::IRInterpreter, io::test_io::TestIO},
};

fn bench_fib(c: &mut Criterion) {
    let mut driver = Driver::with_str(
        r#"
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
        "#,
    );

    let unit = driver.lower().into_iter().next().unwrap();
    let module = ModulePassManager::run(&unit.env, unit.module());
    let io = TestIO::new();

    c.bench_function("fib_20", |b| {
        b.iter(|| black_box(IRInterpreter::new(module.clone(), &io, &driver.symbol_table).run()))
    });
}

fn bench_loop_sum(c: &mut Criterion) {
    let mut driver = Driver::with_str(
        r#"
        let i = 0
        let sum = 0
        loop i < 1000 {
            sum = sum + i
            i = i + 1
        }

        sum
        "#,
    );

    let unit = driver.lower().into_iter().next().unwrap();
    let module = ModulePassManager::run(&unit.env, unit.module());
    let io = TestIO::new();

    c.bench_function("loop_sum_1000", |b| {
        b.iter(|| black_box(IRInterpreter::new(module.clone(), &io, &driver.symbol_table).run()))
    });
}

criterion_group!(benches, bench_fib, bench_loop_sum);
criterion_main!(benches);
