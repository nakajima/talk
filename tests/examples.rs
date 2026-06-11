//! Example tests: each runnable example executes on BOTH engines (the
//! reference evaluator is the trusted baseline the VM is checked
//! against) and its stdout must match the frozen text in
//! `examples/expected/<name>.stdout`. The list grows per backend
//! milestone until every example runs.

use std::path::PathBuf;
use talk::compiling::driver::{Driver, DriverConfig, Source};

fn lowered(files: &[&str]) -> Driver<talk::compiling::driver::Lowered> {
    let sources: Vec<Source> = files
        .iter()
        .map(|f| Source::from(PathBuf::from(format!("examples/{f}"))))
        .collect();
    let name = files[0].to_string();
    let typed = Driver::new(sources, DriverConfig::new(name))
        .parse()
        .expect("parse")
        .resolve_names()
        .expect("resolve")
        .type_check();
    assert!(
        !typed.has_errors(),
        "type errors in {files:?}: {:?}",
        typed.diagnostics()
    );
    let lowered = typed.lower();
    assert!(
        lowered.phase.diagnostics.is_empty(),
        "lowering {files:?}: {:?}",
        lowered.phase.diagnostics
    );
    lowered
}

/// Both engines, identical stdout, matching the frozen expectation file.
fn expect_stdout(name: &str, files: &[&str]) {
    let mut driver = lowered(files);
    let (_, vm_out) = driver.run_vm_with_output().expect("vm");
    let (_, evaluator_out) = driver.eval_with_output().expect("evaluator");
    let expected = std::fs::read_to_string(format!("examples/expected/{name}.stdout"))
        .expect("expected-output file");
    assert_eq!(vm_out, expected, "{name}: vm stdout vs expected");
    assert_eq!(
        evaluator_out, expected,
        "{name}: evaluator stdout vs expected"
    );
}

#[test]
fn hello_world() {
    expect_stdout("HelloWorld", &["HelloWorld.tlk"]);
}

#[test]
fn strings() {
    expect_stdout("Strings", &["Strings.tlk"]);
}

#[test]
fn struct_example() {
    expect_stdout("Struct", &["Struct.tlk"]);
}

#[test]
fn identity() {
    expect_stdout("Identity", &["Identity.tlk"]);
}

#[test]
fn loop_example() {
    expect_stdout("Loop", &["Loop.tlk"]);
}

#[test]
fn imports_exports() {
    expect_stdout("Imports", &["Imports.tlk", "Exports.tlk"]);
}

#[test]
fn fib() {
    // VM-only: fib(24) is far past the reference evaluator's step
    // budget; the recursion scheme itself is covered on both engines at
    // smaller depth in src/vm/vm_tests.rs.
    let driver = lowered(&["Fib.tlk"]);
    let (value, out) = driver.run_vm_with_output().expect("vm");
    assert_eq!(value, talk::vm::interp::Value::I64(46368));
    assert_eq!(out, "");
}
