use std::time::Instant;

use talk::compiling::driver::{Driver, DriverConfig, Source};
use talk::vm::{interp, io::CaptureIO, schedule};

fn compile_module(source: &str) -> talk::vm::Module {
    let driver = Driver::new(vec![Source::from(source)], DriverConfig::new("Bench"));
    let typed = driver.parse().unwrap().resolve_names().unwrap().type_check();
    assert!(!typed.has_errors(), "{:?}", typed.diagnostics());
    let mut lowered = typed.lower();
    assert!(lowered.phase.diagnostics.is_empty(), "{:?}", lowered.phase.diagnostics);
    schedule::schedule(
        &mut lowered.phase.program,
        lowered.phase.main,
        &lowered.phase.entry_funcs,
    )
    .unwrap()
}

fn main() {
    let source = "1 + 2\n";

    let t0 = Instant::now();
    let module = compile_module(source);
    let cold_compile = t0.elapsed();

    let t1 = Instant::now();
    let module2 = compile_module(source);
    let warm_compile = t1.elapsed();

    let mut io = CaptureIO::default();
    let t2 = Instant::now();
    let _ = interp::run(&module, &mut io).unwrap();
    let one_run = t2.elapsed();

    let iterations = 100_000;
    let t3 = Instant::now();
    for _ in 0..iterations {
        let mut io = CaptureIO::default();
        let _ = interp::run(&module2, &mut io).unwrap();
    }
    let many_runs = t3.elapsed();

    println!("cold_compile_ms={:.3}", cold_compile.as_secs_f64() * 1000.0);
    println!("warm_compile_ms={:.3}", warm_compile.as_secs_f64() * 1000.0);
    println!("one_vm_run_us={:.3}", one_run.as_secs_f64() * 1_000_000.0);
    println!(
        "avg_vm_run_us={:.3}",
        many_runs.as_secs_f64() * 1_000_000.0 / iterations as f64
    );
    println!("static_bytes={}", module.statics.len());
}
