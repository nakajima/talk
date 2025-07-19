use criterion::{Criterion, criterion_group, criterion_main};
use std::hint::black_box;
use talk::{
    analysis::module_pass_manager::ModulePassManager, compiling::driver::Driver,
    lowering::ir_module::IRModule, prelude,
};

const CODE: &str = include_str!("../dev/fixtures/bench.tlk");

fn bench_parse(c: &mut Criterion) {
    c.bench_function("parse", |b| {
        b.iter(|| {
            let driver = Driver::with_str(CODE);
            black_box(driver.parse());
        })
    });
}

fn bench_resolve(c: &mut Criterion) {
    c.bench_function("resolve", |b| {
        b.iter(|| {
            let mut driver = Driver::with_str(CODE);
            for unit in driver.parse() {
                black_box(unit.resolved(
                    &mut driver.symbol_table,
                    &driver.config,
                    &driver.module_env,
                ));
            }
        })
    });
}

fn bench_typecheck(c: &mut Criterion) {
    c.bench_function("typecheck", |b| {
        b.iter(|| {
            let mut driver = Driver::with_str(CODE);
            for unit in driver.parse() {
                let resolved =
                    unit.resolved(&mut driver.symbol_table, &driver.config, &driver.module_env);
                black_box(resolved.typed(
                    &mut driver.symbol_table,
                    &driver.config,
                    &driver.module_env,
                ));
            }
        })
    });
}

fn bench_lower(c: &mut Criterion) {
    c.bench_function("lower", |b| {
        b.iter(|| {
            let mut driver = Driver::with_str(CODE);
            for unit in driver.parse() {
                let resolved =
                    unit.resolved(&mut driver.symbol_table, &driver.config, &driver.module_env);
                let typed =
                    resolved.typed(&mut driver.symbol_table, &driver.config, &driver.module_env);
                let module = IRModule::new();
                black_box(typed.lower(
                    &mut driver.symbol_table,
                    &driver.config,
                    module,
                    &driver.module_env,
                ));
            }
        })
    });
}

fn bench_passes(c: &mut Criterion) {
    c.bench_function("module_passes", |b| {
        b.iter(|| {
            let mut driver = Driver::with_str(CODE);
            for unit in driver.parse() {
                let resolved =
                    unit.resolved(&mut driver.symbol_table, &driver.config, &driver.module_env);
                let typed =
                    resolved.typed(&mut driver.symbol_table, &driver.config, &driver.module_env);
                let module = IRModule::new();
                let lowered = typed.lower(
                    &mut driver.symbol_table,
                    &driver.config,
                    module,
                    &driver.module_env,
                );
                black_box(ModulePassManager::run(&lowered.env, lowered.module()));
            }
        })
    });
}

criterion_group!(
    compiler_benches,
    bench_parse,
    bench_resolve,
    bench_typecheck,
    bench_lower,
    bench_passes
);
criterion_main!(compiler_benches);
