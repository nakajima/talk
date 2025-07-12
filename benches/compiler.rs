use criterion::{BenchmarkId, Criterion, black_box, criterion_group, criterion_main};
use talk::{
    analysis::module_pass_manager::ModulePassManager,
    compiling::{compilation_unit::CompilationUnit, driver::Driver},
    lowering::ir_module::IRModule,
};

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

fn bench_compile_phases(c: &mut Criterion) {
    let mut group = c.benchmark_group("compiler_phases");

    group.bench_function(BenchmarkId::new("parse", "fib"), |b| {
        b.iter(|| {
            let driver = Driver::with_str(black_box(CODE));
            black_box(driver.parse());
        });
    });

    group.bench_function(BenchmarkId::new("resolve", "fib"), |b| {
        b.iter(|| {
            let mut driver = Driver::with_str(black_box(CODE));
            let parsed = driver.parse();
            for unit in parsed {
                black_box(unit.resolved(&mut driver.symbol_table, &driver.config));
            }
        });
    });

    group.bench_function(BenchmarkId::new("type", "fib"), |b| {
        b.iter(|| {
            let mut driver = Driver::with_str(black_box(CODE));
            let parsed = driver.parse();
            for unit in parsed {
                let resolved = unit.resolved(&mut driver.symbol_table, &driver.config);
                black_box(resolved.typed(&mut driver.symbol_table, &driver.config));
            }
        });
    });

    group.bench_function(BenchmarkId::new("lower", "fib"), |b| {
        b.iter(|| {
            let mut driver = Driver::with_str(black_box(CODE));
            let parsed = driver.parse();
            for unit in parsed {
                let resolved = unit.resolved(&mut driver.symbol_table, &driver.config);
                let typed = resolved.typed(&mut driver.symbol_table, &driver.config);
                black_box(typed.lower(&mut driver.symbol_table, &driver.config, IRModule::new()));
            }
        });
    });

    group.bench_function(BenchmarkId::new("passes", "fib"), |b| {
        b.iter(|| {
            let mut driver = Driver::with_str(black_box(CODE));
            let parsed = driver.parse();
            for unit in parsed {
                let resolved = unit.resolved(&mut driver.symbol_table, &driver.config);
                let typed = resolved.typed(&mut driver.symbol_table, &driver.config);
                let lowered =
                    typed.lower(&mut driver.symbol_table, &driver.config, IRModule::new());
                black_box(ModulePassManager::run(&lowered.env, lowered.module()));
            }
        });
    });

    group.finish();
}

criterion_group!(benches, bench_compile_phases);
criterion_main!(benches);
