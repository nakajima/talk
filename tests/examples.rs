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
    let mut lowered = typed.lower();
    assert!(
        lowered.phase.diagnostics.is_empty(),
        "lowering {files:?}: {:?}",
        lowered.phase.diagnostics
    );
    // Post-lowering verifier: T-Prog + WF over the whole program (the
    // LLVM-verifier habit — Lattner & Adve, CGO 2004).
    let verified = lowered.phase.program.verify();
    assert!(verified.is_ok(), "verifier {files:?}: {:?}", verified.err());
    lowered
}

/// Both engines, identical stdout, matching the frozen expectation file.
fn expect_stdout(name: &str, files: &[&str]) {
    let (vm_out, evaluator_out) = both_engine_stdout(files, false);
    assert_stdout_expected(name, &vm_out, &evaluator_out);
}

/// [`expect_stdout`] with the container-element-teardown deficit fenced
/// (docs/confidence-and-core-plan.md, Track B): each caller enumerates an
/// example whose containers leak buffers today.
fn expect_stdout_expecting_container_element_leak(name: &str, files: &[&str]) {
    let (vm_out, evaluator_out) = both_engine_stdout(files, true);
    assert_stdout_expected(name, &vm_out, &evaluator_out);
}

fn both_engine_stdout(files: &[&str], leak_fenced: bool) -> (String, String) {
    let mut driver = lowered(files);
    let (_, vm_out) = driver.run_vm_with_output().expect("vm");
    let (_, evaluator_out) = if leak_fenced {
        driver
            .eval_expecting_container_element_leak()
            .expect("evaluator")
    } else {
        driver.eval_with_output().expect("evaluator")
    };
    (vm_out, evaluator_out)
}

fn assert_stdout_expected(name: &str, vm_out: &str, evaluator_out: &str) {
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
fn graphemes() {
    expect_stdout("Graphemes", &["Graphemes.tlk"]);
}

#[test]
fn strings() {
    expect_stdout_expecting_container_element_leak("Strings", &["Strings.tlk"]);
}

#[test]
fn struct_example() {
    expect_stdout("Struct", &["Struct.tlk"]);
}

#[test]
fn identity() {
    expect_stdout_expecting_container_element_leak("Identity", &["Identity.tlk"]);
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
fn array() {
    expect_stdout_expecting_container_element_leak("Array", &["Array.tlk"]);
}

#[test]
fn iteratin() {
    expect_stdout_expecting_container_element_leak("Iteratin", &["Iteratin.tlk"]);
}

#[test]
fn for_loop() {
    expect_stdout_expecting_container_element_leak("ForLoop", &["ForLoop.tlk"]);
}

#[test]
fn show() {
    // Float's 1.229999999999999 is the documented core epsilon-loop wart;
    // both engines agree.
    expect_stdout_expecting_container_element_leak("Show", &["Show.tlk"]);
}

#[test]
fn sum() {
    // Prints the if/else value, then the final bare expression is the
    // program value.
    let mut driver = lowered(&["Sum.tlk"]);
    let (value, out) = driver.run_vm_with_output().expect("vm");
    assert_eq!(value, talk::vm::interp::Value::I64(11));
    assert_eq!(out, "7\n");
    let (evaluator_value, evaluator_out) = driver.eval_with_output().expect("evaluator");
    assert_eq!(evaluator_value, talk::lambda_g::eval::EvalValue::I64(11));
    assert_eq!(evaluator_out, "7\n");
}

#[test]
fn protocols() {
    let mut driver = lowered(&["Protocols.tlk"]);
    let (value, out) = driver.run_vm_with_output().expect("vm");
    assert_eq!(value, talk::vm::interp::Value::I64(123));
    assert_eq!(out, "");
    let (evaluator_value, evaluator_out) = driver.eval_with_output().expect("evaluator");
    assert_eq!(evaluator_value, talk::lambda_g::eval::EvalValue::I64(123));
    assert_eq!(evaluator_out, "");
}

#[test]
fn anon_func() {
    // The statement-level `func` literal parses as a declaration; the
    // program value is the parenthesized `(123)` statement.
    let mut driver = lowered(&["AnonFunc.tlk"]);
    let (value, out) = driver.run_vm_with_output().expect("vm");
    assert_eq!(value, talk::vm::interp::Value::I64(123));
    assert_eq!(out, "");
    let (evaluator_value, evaluator_out) = driver.eval_with_output().expect("evaluator");
    assert_eq!(evaluator_value, talk::lambda_g::eval::EvalValue::I64(123));
    assert_eq!(evaluator_out, "");
}

#[test]
fn capture() {
    let mut driver = lowered(&["Capture.tlk"]);
    let (value, out) = driver.run_vm_with_output().expect("vm");
    assert_eq!(value, talk::vm::interp::Value::I64(3));
    assert_eq!(out, "");
    let (evaluator_value, evaluator_out) = driver.eval_with_output().expect("evaluator");
    assert_eq!(evaluator_value, talk::lambda_g::eval::EvalValue::I64(3));
    assert_eq!(evaluator_out, "");
}

#[test]
fn trailing_block() {
    // CaptureIO's sleep is a no-op, so the two 1-second sleeps cost
    // nothing here; `talk run` sleeps for real.
    expect_stdout("TrailingBlock", &["TrailingBlock.tlk"]);
}

#[test]
fn sleep() {
    expect_stdout("Sleep", &["Sleep.tlk"]);
}

#[test]
fn effects() {
    // The abort effect: the lexical handler prints the payload; the line
    // after the perform never runs.
    expect_stdout("Effects", &["Effects.tlk"]);
}

#[test]
fn match_bind() {
    // No printing: the assertion is the program value, on both engines.
    let mut driver = lowered(&["MatchBind.tlk"]);
    let (value, out) = driver.run_vm_with_output().expect("vm");
    assert_eq!(value, talk::vm::interp::Value::I64(22));
    assert_eq!(out, "");
    let (evaluator_value, evaluator_out) = driver.eval_with_output().expect("evaluator");
    assert_eq!(evaluator_value, talk::lambda_g::eval::EvalValue::I64(22));
    assert_eq!(evaluator_out, "");
}

#[test]
fn structural_typing() {
    let mut driver = lowered(&["StructuralTyping.tlk"]);
    let (value, out) = driver.run_vm_with_output().expect("vm");
    assert_eq!(value, talk::vm::interp::Value::Bool(true));
    assert_eq!(out, "");
    let (evaluator_value, evaluator_out) = driver.eval_with_output().expect("evaluator");
    assert_eq!(evaluator_value, talk::lambda_g::eval::EvalValue::Bool(true));
    assert_eq!(evaluator_out, "");
}

#[test]
fn file_io() {
    // print_raw and write_string: io_write splices straight to stdout
    // (no trailing newlines — these are raw writes).
    expect_stdout("FileIO", &["FileIO.tlk"]);
}

#[test]
fn chat_client() {
    // Under CaptureIO every read returns zero bytes (empty simulated
    // streams), so the client prints nothing and exits its loop; the
    // program value is the close result.
    let mut driver = lowered(&["ChatClient.tlk"]);
    let (value, out) = driver.run_vm_with_output().expect("vm");
    assert_eq!(value, talk::vm::interp::Value::I64(0));
    assert_eq!(out, "");
    // Container-element-teardown fence (Track B): the client's read
    // buffers leak today.
    let (evaluator_value, evaluator_out) = driver
        .eval_expecting_container_element_leak()
        .expect("evaluator");
    assert_eq!(evaluator_value, talk::lambda_g::eval::EvalValue::I64(0));
    assert_eq!(evaluator_out, "");
}

#[test]
fn server_examples_compile() {
    // The four server programs loop forever (manual `talk run`
    // targets), so they cannot pin stdout; they must still lower and
    // pass the verifier cleanly.
    lowered(&["ChatServer.tlk"]);
    lowered(&["Http.tlk"]);
    lowered(&["WebApi.tlk"]);
    lowered(&["Website.tlk"]);
}

#[test]
fn fib() {
    // VM-only: fib(24) is far past the reference evaluator's step
    // budget; the recursion scheme itself is covered on both engines at
    // smaller depth in src/vm/vm_tests.rs.
    let mut driver = lowered(&["Fib.tlk"]);
    let (value, out) = driver.run_vm_with_output().expect("vm");
    assert_eq!(value, talk::vm::interp::Value::Void);
    assert_eq!(out, "46368\n");
}
