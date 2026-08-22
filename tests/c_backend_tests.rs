//! C backend end to end: the emitted C must compute what the
//! interpreter computes.
//!
//! These tests drive the `talk` binary — the product seam — which is
//! why they live in the root crate rather than in `talk-c`: the same
//! finalized MIR feeds both adapters, so these tests are differential:
//! compile the program both ways and compare the answer. The
//! structure-level emission tests live at the emitter's own seam in
//! `talk-c/tests/emission.rs`.
//!
//! The focused cases below pin individual constructs; the two corpus
//! tests run every program the project already pins, which is what makes
//! this more than a set of cases chosen to pass.

use std::path::{Path, PathBuf};
use std::process::Command;

/// A tight scalar loop: `Scalar`, `Copy`, `Call`, `Branch`, `Goto`.
const ARITH: &str = "\
pub func bench() -> Int {
	let total = 0
	let i = 0
	loop i < 10000 {
		total = total + i * 3 - i / 2
		i = i + 1
	}
	total
}
";

/// Struct construction and field reads: `Record`, `GetField`.
const FIELDS: &str = "\
struct Point {
	let x: Int
	let y: Int
}
func dist2(p: &Point, q: &Point) -> Int {
	let dx = p.x - q.x
	let dy = p.y - q.y
	dx * dx + dy * dy
}
pub func bench() -> Int {
	let total = 0
	let i = 0
	loop i < 5000 {
		let p = Point(x: i, y: i + 1)
		let q = Point(x: i * 2, y: i - 3)
		total = total + dist2(p: p, q: q) / 1000
		i = i + 1
	}
	total
}
";

/// Enum construction and match dispatch: `Variant`, `GetTag`,
/// `GetPayload`, and the `Switch` terminator.
const DISPATCH: &str = "\
enum Shape {
	case dot
	case line(Int)
	case rect(Int, Int)
}
func area(s: &Shape) -> Int {
	match s {
		.dot -> 1,
		.line(len) -> len,
		.rect(w, h) -> w * h
	}
}
pub func bench() -> Int {
	let total = 0
	let i = 0
	loop i < 5000 {
		let s = if i / 3 * 3 == i {
			Shape.dot
		} else if (i + 1) / 3 * 3 == i + 1 {
			Shape.line(i)
		} else {
			Shape.rect(i, 2)
		}
		total = total + area(s: s)
		i = i + 1
	}
	total
}
";

/// Recursion, to pin argument passing and return delivery.
const CALLS: &str = "\
func fib(n: Int) -> Int {
	if n < 2 {
		n
	} else {
		fib(n: n - 1) + fib(n: n - 2)
	}
}
pub func bench() -> Int {
	fib(n: 20)
}
";

const BOOL: &str = "\
pub func bench() -> Bool {
	let i = 0
	let seen = false
	loop i < 10 {
		seen = seen || i == 7
		i = i + 1
	}
	seen
}
";

/// A resumed effect: the clause returns, and its value becomes the value
/// of the `'step` expression at the perform site.
const EFFECT_RESUME: &str = "\
effect 'step(n: Int) -> Int
func run(n: Int) 'step -> Int {
	let total = 0
	let i = 0
	loop i < n {
		total = total + 'step(n: i)
		i = i + 1
	}
	total
}
pub func bench() -> Int {
	#handle 'step { v in 'continue v + 1 }
	run(n: 1000)
}
";

/// A clause that does not resume: it aborts to the continuation captured
/// when the handler was installed, unwinding `inner`'s frame, and the
/// installing frame returns the clause's value.
const EFFECT_ABORT: &str = "\
effect 'bail(n: Int) -> Never
func inner(n: Int) 'bail -> Int {
	if n > 3 {
		'bail(n: n)
	}
	n
}
pub func bench() -> Int {
	#handle 'bail { n in n * 10 }
	inner(n: 7)
}
";

/// Nearest-handler routing across two installs, which is what the
/// handler-search floor exists to get right: the inner clause must not
/// re-find itself when it performs.
const EFFECT_NESTED: &str = "\
effect 'sig(n: Int) -> Int
func emit(n: Int) 'sig -> Int {
	'sig(n: n) + 1
}
func middle(n: Int) 'sig -> Int {
	#handle 'sig { v in 'continue v * 2 }
	emit(n: n) + 100
}
pub func bench() -> Int {
	#handle 'sig { v in 'continue v * 3 }
	middle(n: 5) + emit(n: 5)
}
";

/// A string literal is immortal static data behind the core `String`
/// shape, so this needs `StringLit`, `GetField`, and the retain/free pair
/// that leaves a static pointer alone.
const STRING_LITERAL: &str = "\
pub func bench() -> Int {
	let s = \"hello, world\"
	s.byte_count
}
";

/// Concatenation allocates: `Alloc`, `PtrAdd`, `MemCopy`, and the
/// reference-counted `Free` that must actually reclaim the buffer.
const STRING_CONCAT: &str = "\
pub func bench() -> Int {
	let total = 0
	let i = 0
	loop i < 200 {
		let joined = \"left\" + \"-side\"
		total = total + joined.byte_count
		i = i + 1
	}
	total
}
";

/// Cargo hands each integration-test binary its own scratch directory
/// under `target/`; nothing here escapes the build tree.
fn scratch(name: &str) -> PathBuf {
    let dir = Path::new(env!("CARGO_TARGET_TMPDIR")).join(name);
    std::fs::create_dir_all(&dir).expect("scratch directory");
    dir
}

fn write_program(dir: &Path, source: &str) -> PathBuf {
    let path = dir.join("program.tlk");
    std::fs::write(&path, source).expect("write Talk source");
    path
}

fn talk(arguments: &[&str]) -> std::process::Output {
    Command::new(env!("CARGO_BIN_EXE_talk"))
        .args(arguments)
        .output()
        .expect("run `talk`")
}

/// The interpreter's answer: the reference every C result is compared to.
fn interpreted(program: &Path) -> String {
    let output = talk(&["run", "--entry", "bench", &program.to_string_lossy()]);
    assert!(
        output.status.success(),
        "`talk run` failed:\n{}",
        String::from_utf8_lossy(&output.stderr)
    );
    String::from_utf8(output.stdout).expect("interpreted output is UTF-8")
}

/// Emit C, compile it with the host compiler, and run it.
fn compiled(dir: &Path, program: &Path) -> String {
    let output = talk(&["c", "--entry", "bench", &program.to_string_lossy()]);
    assert!(
        output.status.success(),
        "`talk c` failed:\n{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let source = dir.join("program.c");
    std::fs::write(&source, &output.stdout).expect("write emitted C");

    let binary = dir.join("program.bin");
    let compile = Command::new("cc")
        .arg("-O2")
        .arg("-std=c11")
        .arg("-Wall")
        .arg("-Werror")
        .arg(&source)
        .arg("-o")
        .arg(&binary)
        .output()
        .expect("run `cc`");
    assert!(
        compile.status.success(),
        "emitted C did not compile:\n{}\n--- source ---\n{}",
        String::from_utf8_lossy(&compile.stderr),
        String::from_utf8_lossy(&output.stdout)
    );

    let run = Command::new(&binary)
        .output()
        .expect("run compiled program");
    assert!(
        run.status.success(),
        "compiled program failed:\n{}",
        String::from_utf8_lossy(&run.stderr)
    );
    String::from_utf8(run.stdout).expect("compiled output is UTF-8")
}

fn assert_agrees(name: &str, source: &str) {
    let dir = scratch(name);
    let program = write_program(&dir, source);
    let expected = interpreted(&program);
    assert_eq!(
        compiled(&dir, &program),
        expected,
        "{name}: C backend disagrees with the interpreter"
    );
}

#[test]
fn array_result_rendering_agrees_with_the_interpreter() {
    assert_agrees(
        "array_result_rendering",
        "pub func bench() {\n\t([1, 2, 3].map { $0 * 10 }.to_array(), [true, false], [1.5, 2.0], [\"a\" + \"b\", \"c\"], [[1, 2], [3]])\n}\n",
    );
}

#[test]
fn suspension_crossing_a_resumption_boundary_traps_on_c() {
    // ADR 0065's documented divergence: a resumed extent performing a
    // suspending effect whose handler sits below the resume call works
    // on the VM but fails closed here — effect rows cannot mark
    // resume() callers, so no static resumable set can include them.
    let dir = scratch("suspend_crossing");
    let program = dir.join("crossing.tlk");
    std::fs::write(
        &program,
        "effect 'inner() -> Int\neffect 'outer() -> Int\nenum Held {\n\tcase parked(Resumption<Int, Held>)\n\tcase done(Int)\n}\nfunc inner_body() -> Int {\n\tlet x = 'inner()\n\tlet y = 'outer()\n\tx + y\n}\nfunc stash_inner() -> Held {\n\t#handle 'inner { k in\n\t\tHeld.parked(k)\n\t}\n\tHeld.done(inner_body())\n}\nfunc run_all() -> Int {\n\t#handle 'outer { k in\n\t\tresume(k: k, value: 50)\n\t}\n\tlet held = stash_inner()\n\tmatch held {\n\t\t.parked(k) -> {\n\t\t\tmatch resume(k: k, value: 7) {\n\t\t\t\t.done(value) -> value,\n\t\t\t\t.parked(again) -> {\n\t\t\t\t\tlet dropped = cancel(k: again)\n\t\t\t\t\t0 - 1\n\t\t\t\t}\n\t\t\t}\n\t\t},\n\t\t.done(value) -> value\n\t}\n}\nprint(run_all())\n",
    )
    .expect("write program");
    let emitted = talk(&["c", &program.to_string_lossy()]);
    assert!(emitted.status.success(), "emission must succeed");
    let source = dir.join("crossing.c");
    std::fs::write(&source, &emitted.stdout).expect("write C");
    let binary = dir.join("crossing.bin");
    let compile = std::process::Command::new("cc")
        .args(["-O2", "-std=c11", "-Wall", "-Werror"])
        .arg(&source)
        .arg("-o")
        .arg(&binary)
        .output()
        .expect("run cc");
    assert!(
        compile.status.success(),
        "emitted C failed to compile:\n{}",
        String::from_utf8_lossy(&compile.stderr)
    );
    let run = std::process::Command::new(&binary)
        .output()
        .expect("run binary");
    assert!(!run.status.success(), "the crossing must fail closed");
    assert!(
        String::from_utf8_lossy(&run.stderr)
            .contains("crossed a resumption boundary"),
        "expected the crossing trap, got:\n{}",
        String::from_utf8_lossy(&run.stderr)
    );
}

#[test]
fn suspending_handlers_run_on_the_c_target() {
    // ADR 0065/0068: resumption-binding handlers compile natively as
    // resumable functions — the clause resumes with a value and the
    // extent's answer returns through the whole chain. No declaration
    // marker: the clause's binder derives the kind.
    assert_agrees(
        "suspend_roundtrip",
        "effect 'ping() -> Int\nfunc body() -> Int {\n\t'ping() + 5\n}\nfunc driver() -> Int {\n\t#handle 'ping { k in\n\t\tresume(k: k, value: 100)\n\t}\n\tbody()\n}\npub func bench() -> () {\n\tprint(driver())\n}\n",
    );
}

#[test]
fn blocking_only_channel_programs_pay_no_resumable_tax() {
    // ADR 0068: the resumable set seeds from performs of effects that
    // have a resumption-binding clause somewhere in the program. A
    // program whose only park handlers are the blocking fallbacks
    // (tail-resumptive `'continue` clauses in core/Host.tlk) must
    // compile with no resumable functions — no heap frames, no status
    // checks — even though it uses channels.
    let dir = scratch("blocking_only");
    let program = write_program(
        &dir,
        "use task::{ channel }\nlet (sender, receiver) = channel<Int>()\nsender.send(value: 5)\nif let .some(value) = receiver.recv() { print(value) } else { print(0 - 1) }\n",
    );
    let emitted = talk(&["c", &program.to_string_lossy()]);
    assert!(
        emitted.status.success(),
        "emission must succeed:\n{}",
        String::from_utf8_lossy(&emitted.stderr)
    );
    let source = String::from_utf8_lossy(&emitted.stdout);
    assert!(
        !source.contains("(resumable)"),
        "a blocking-only program was taxed with resumable functions"
    );
}

#[test]
fn mixed_clause_kinds_agree_on_the_c_target() {
    // ADR 0068: one perform site serves a binding handler in one extent
    // and a tail-resumptive handler in another, chosen at runtime by
    // the matched entry's clause kind.
    assert_agrees(
        "mixed_clause_kinds",
        "effect 'step() -> Int\nenum Held {\n\tcase parked(Resumption<Int, Held>)\n\tcase done(Int)\n}\nfunc body() -> Int {\n\t'step() + 1\n}\nfunc capture_run() -> Held {\n\t#handle 'step { k in Held.parked(k) }\n\tHeld.done(body())\n}\nfunc tail_run() -> Int {\n\t#handle 'step { 'continue 10 }\n\tbody()\n}\npub func bench() -> () {\n\tmatch capture_run() {\n\t\t.parked(k) -> {\n\t\t\tmatch resume(k: k, value: 3) {\n\t\t\t\t.done(value) -> print(value),\n\t\t\t\t.parked(again) -> {\n\t\t\t\t\tlet dropped = cancel(k: again)\n\t\t\t\t\tprint(0 - 1)\n\t\t\t\t}\n\t\t\t}\n\t\t},\n\t\t.done(value) -> print(value)\n\t}\n\tprint(tail_run())\n}\n",
    );
}

#[test]
fn scalar_loop_agrees_with_the_interpreter() {
    assert_agrees("arith", ARITH);
}

#[test]
fn checked_and_unchecked_integer_arithmetic_agree_with_the_interpreter() {
    assert_agrees(
        "checked_arithmetic",
        "pub func bench() -> () {\n\tlet max = 9223372036854775807\n\tlet min = -max - 1\n\tprint(max.checked_add(1))\n\tprint(20.checked_mul(2))\n\tprint(max.unchecked_add(1))\n\tprint(min.unchecked_sub(1))\n\tprint(max.unchecked_mul(2))\n\tprint(min.unchecked_div(-1))\n}\n",
    );
}

#[test]
fn native_integer_overflow_traps() {
    for (name, expression, message) in [
        ("add", "max + one", "integer overflow in addition"),
        ("sub", "min - one", "integer overflow in subtraction"),
        ("mul", "max * two", "integer overflow in multiplication"),
        ("div", "min / negative_one", "integer overflow in division"),
    ] {
        let dir = scratch(&format!("integer_overflow_{name}"));
        let program = write_program(
            &dir,
            &format!(
                "pub func bench() -> Int {{\n\tlet max = 9223372036854775807\n\tlet min = -max - 1\n\tlet one = 1\n\tlet two = 2\n\tlet negative_one = -1\n\t{expression}\n}}\n"
            ),
        );
        let output = talk(&["c", "--entry", "bench", &program.to_string_lossy()]);
        assert!(
            output.status.success(),
            "`talk c` failed:\n{}",
            String::from_utf8_lossy(&output.stderr)
        );
        let source = dir.join("program.c");
        std::fs::write(&source, &output.stdout).expect("write emitted C");
        let binary = dir.join("program.bin");
        let compile = Command::new("cc")
            .args(["-O2", "-std=c11", "-Wall", "-Werror"])
            .arg(&source)
            .arg("-o")
            .arg(&binary)
            .output()
            .expect("run `cc`");
        assert!(
            compile.status.success(),
            "emitted C did not compile:\n{}",
            String::from_utf8_lossy(&compile.stderr)
        );
        let run = Command::new(&binary)
            .output()
            .expect("run compiled program");
        assert!(!run.status.success(), "{name} overflow must fail");
        assert!(String::from_utf8_lossy(&run.stderr).contains(message));
    }
}

#[test]
fn records_agree_with_the_interpreter() {
    assert_agrees("fields", FIELDS);
}

#[test]
fn enums_agree_with_the_interpreter() {
    assert_agrees("dispatch", DISPATCH);
}

#[test]
fn recursion_agrees_with_the_interpreter() {
    assert_agrees("calls", CALLS);
}

#[test]
fn bool_results_agree_with_the_interpreter() {
    assert_agrees("bool", BOOL);
}

#[test]
fn string_literals_agree_with_the_interpreter() {
    assert_agrees("string_literal", STRING_LITERAL);
}

#[test]
fn allocating_strings_agree_with_the_interpreter() {
    assert_agrees("string_concat", STRING_CONCAT);
}

#[test]
fn resumed_effects_agree_with_the_interpreter() {
    assert_agrees("effect_resume", EFFECT_RESUME);
}

#[test]
fn aborting_effects_agree_with_the_interpreter() {
    assert_agrees("effect_abort", EFFECT_ABORT);
}

#[test]
fn nested_handlers_agree_with_the_interpreter() {
    assert_agrees("effect_nested", EFFECT_NESTED);
}

/// The benchmark corpus end to end: whole programs, script entry, `print`
/// through the ambient IO host handler, and the byte-exact output the
/// project already pins for the interpreter. These are the project's
/// programs rather than this file's, which is what makes them worth more
/// than the focused cases above.
#[test]
fn bench_corpus_agrees_with_its_frozen_output() {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("bench");
    let mut programs: Vec<_> = std::fs::read_dir(&root)
        .expect("bench directory")
        .filter_map(Result::ok)
        .map(|entry| entry.path())
        .filter(|path| path.extension().is_some_and(|ext| ext == "tlk"))
        .collect();
    programs.sort();
    assert!(
        programs.len() >= 8,
        "bench corpus shrank: {} programs",
        programs.len()
    );

    for program in programs {
        let name = program
            .file_stem()
            .and_then(|stem| stem.to_str())
            .expect("program name")
            .to_string();
        let expected = std::fs::read_to_string(root.join(format!("expected/{name}.stdout")))
            .expect("pinned stdout");

        let dir = scratch(&format!("bench_{name}"));
        let output = talk(&["c", &program.to_string_lossy()]);
        assert!(
            output.status.success(),
            "{name}: `talk c` failed:\n{}",
            String::from_utf8_lossy(&output.stderr)
        );
        let source = dir.join("program.c");
        std::fs::write(&source, &output.stdout).expect("write emitted C");
        let binary = dir.join("program.bin");
        let compile = Command::new("cc")
            .args(["-O2", "-std=c11", "-Wall", "-Werror"])
            .arg(&source)
            .arg("-o")
            .arg(&binary)
            .output()
            .expect("run `cc`");
        assert!(
            compile.status.success(),
            "{name}: emitted C did not compile:\n{}",
            String::from_utf8_lossy(&compile.stderr)
        );
        let run = Command::new(&binary)
            .output()
            .expect("run compiled program");
        assert!(
            run.status.success(),
            "{name}: compiled program failed:\n{}",
            String::from_utf8_lossy(&run.stderr)
        );
        assert_eq!(
            String::from_utf8_lossy(&run.stdout),
            expected,
            "{name}: C backend disagrees with the pinned output"
        );
    }
}

/// Every complete program the project pins, run both ways. `heap_graph`
/// in particular builds a cycle across two regions, which is the case
/// merge-only regions exist for.
#[test]
fn program_corpus_agrees_with_the_interpreter() {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/programs");
    let mut programs: Vec<_> = std::fs::read_dir(&root)
        .expect("programs directory")
        .filter_map(Result::ok)
        .map(|entry| entry.path())
        .filter(|path| path.extension().is_some_and(|ext| ext == "tlk"))
        .collect();
    programs.sort();
    assert!(programs.len() >= 19, "program corpus shrank");

    for program in programs {
        let name = program
            .file_stem()
            .and_then(|stem| stem.to_str())
            .expect("program name")
            .to_string();
        let dir = scratch(&format!("program_{name}"));

        let interpreted = talk(&["run", &program.to_string_lossy()]);
        assert!(
            interpreted.status.success(),
            "{name}: `talk run` failed:\n{}",
            String::from_utf8_lossy(&interpreted.stderr)
        );

        let emitted = talk(&["c", &program.to_string_lossy()]);
        assert!(
            emitted.status.success(),
            "{name}: `talk c` failed:\n{}",
            String::from_utf8_lossy(&emitted.stderr)
        );
        let source = dir.join("program.c");
        std::fs::write(&source, &emitted.stdout).expect("write emitted C");
        let binary = dir.join("program.bin");
        let compile = Command::new("cc")
            .args(["-O2", "-std=c11", "-Wall", "-Werror"])
            .arg(&source)
            .arg("-o")
            .arg(&binary)
            .output()
            .expect("run `cc`");
        assert!(
            compile.status.success(),
            "{name}: emitted C did not compile:\n{}",
            String::from_utf8_lossy(&compile.stderr)
        );
        let run = Command::new(&binary)
            .output()
            .expect("run compiled program");
        assert!(
            run.status.success(),
            "{name}: compiled program failed:\n{}",
            String::from_utf8_lossy(&run.stderr)
        );
        assert_eq!(
            String::from_utf8_lossy(&run.stdout),
            String::from_utf8_lossy(&interpreted.stdout),
            "{name}: C backend disagrees with the interpreter"
        );
    }
}

/// A `Deinit` body that itself allocates: the region tearing down nests a
/// second walk behind the first. The drain loop has to finish the inner
/// one without re-entering itself, and free both.
#[test]
fn nested_region_teardown_agrees_with_the_interpreter() {
    assert_agrees(
        "nested_teardown",
        "\
let counter = 0
struct Inner 'heap {
	let id: Int
}
extend Inner: Deinit {
	consuming func deinit() -> Void {
		counter = counter + 1
		()
	}
}
struct Outer 'heap {
	let id: Int
}
extend Outer: Deinit {
	consuming func deinit() -> Void {
		let extra = Inner(id: 9)
		counter = counter + 100
		()
	}
}
func scope() -> Int {
	let o = Outer(id: 1)
	0
}
pub func bench() -> Int {
	let n = scope()
	counter
}
",
    );
}

/// Float results go through the runtime's rendering rule: the shortest
/// decimal that round-trips, positionally, with a trailing ".0" when the
/// result would otherwise look like an integer. Magnitudes are spread
/// wide because that rule is where `%g` would diverge.
#[test]
fn floats_agree_with_the_interpreter() {
    for (name, expression) in [
        ("third", "1.0 / 3.0"),
        ("integral", "2.0"),
        ("epsilon", "0.1 + 0.2"),
        ("huge", "1000000.0 * 1000000.0 * 1000000.0 * 1000000.0"),
        ("tiny", "1.0 / 1000000.0 / 1000000.0"),
        ("binary", "1.0 / 1024.0"),
        ("infinite", "1.0 / 0.0"),
    ] {
        assert_agrees(
            &format!("float_{name}"),
            &format!("pub func bench() -> Float {{\n\t{expression}\n}}\n"),
        );
    }
}

/// A closure that mutates a captured local: assignment conversion puts
/// the local in a cell the closure and its defining frame share, so both
/// see the updates.
#[test]
fn captured_mutable_cells_agree_with_the_interpreter() {
    assert_agrees(
        "cells",
        "\
func make_counter() {
\tlet i = 0
\treturn func() {
\t\ti = i + 1
\t\ti
\t}
}
pub func bench() -> Int {
\tlet counter = make_counter()
\tcounter()
\tcounter()
\tcounter()
}
",
    );
}

/// `talk build --native` is the ahead-of-time path: emit C, drive the
/// host compiler, produce an executable that depends on nothing but libc.
/// The program here does real host IO so the emitted binary is exercising
/// the operation table rather than pure computation.
#[test]
fn build_native_produces_a_standalone_executable() {
    let dir = scratch("build_native");
    let program = write_program(
        &dir,
        "\
struct Point {
	let x: Int
	let y: Int
}
let p = Point(x: 3, y: 4)
print(\"point\")
print(p.x)
print(p.y)
let total = 0
let i = 0
loop i < 100 {
	total = total + i
	i = i + 1
}
print(total)
",
    );

    let interpreted = talk(&["run", &program.to_string_lossy()]);
    assert!(
        interpreted.status.success(),
        "`talk run` failed:\n{}",
        String::from_utf8_lossy(&interpreted.stderr)
    );

    let binary = dir.join("program.bin");
    let built = talk(&[
        "build",
        "--native",
        &program.to_string_lossy(),
        "-o",
        &binary.to_string_lossy(),
    ]);
    assert!(
        built.status.success(),
        "`talk build --native` failed:\n{}",
        String::from_utf8_lossy(&built.stderr)
    );
    assert!(binary.exists(), "no executable was produced");

    let run = Command::new(&binary).output().expect("run the executable");
    assert!(
        run.status.success(),
        "the executable failed:\n{}",
        String::from_utf8_lossy(&run.stderr)
    );
    assert_eq!(
        String::from_utf8_lossy(&run.stdout),
        String::from_utf8_lossy(&interpreted.stdout),
        "the native build disagrees with the interpreter"
    );

    // The C is a build artifact, not output: it goes away unless asked for.
    assert!(
        !binary.with_extension("c").exists(),
        "the generated C should not be left behind without --keep-c"
    );
}

/// Runaway recursion has to end in a diagnostic, not a signal. The VM
/// caps live frames and reports an overflow; generated C runs on the
/// machine stack, where the same program would take SIGSEGV, so each
/// function checks the stack it has left on entry.
///
/// `status.code()` is `None` when a process dies to a signal, which is
/// what this is really asserting: the failure is orderly.
#[test]
fn runaway_recursion_reports_an_overflow_rather_than_crashing() {
    let dir = scratch("stack_overflow");
    let program = write_program(
        &dir,
        "\
func down(n: Int) -> Int {
	if n == 0 {
		0
	} else {
		down(n: n - 1) + 1
	}
}
print(down(n: 4000000))
",
    );

    let emitted = talk(&["c", &program.to_string_lossy()]);
    assert!(
        emitted.status.success(),
        "`talk c` failed:\n{}",
        String::from_utf8_lossy(&emitted.stderr)
    );
    let source = dir.join("program.c");
    std::fs::write(&source, &emitted.stdout).expect("write emitted C");
    let binary = dir.join("program.bin");
    let compile = Command::new("cc")
        .args(["-O2", "-std=c11", "-Wall", "-Werror"])
        .arg(&source)
        .arg("-o")
        .arg(&binary)
        .output()
        .expect("run `cc`");
    assert!(
        compile.status.success(),
        "emitted C did not compile:\n{}",
        String::from_utf8_lossy(&compile.stderr)
    );

    let run = Command::new(&binary).output().expect("run the program");
    assert_eq!(
        run.status.code(),
        Some(1),
        "expected an orderly exit; a `None` code means it died to a signal.\nstderr: {}",
        String::from_utf8_lossy(&run.stderr)
    );
    assert!(
        String::from_utf8_lossy(&run.stderr).contains("call stack overflow"),
        "expected the overflow diagnostic, got:\n{}",
        String::from_utf8_lossy(&run.stderr)
    );
}

/// The guard has to hold on a host whose stack is smaller than any
/// figure compiled into it, so the budget is read from the process
/// rather than assumed. Checked by running under a reduced `ulimit`,
/// which is where a fixed threshold falls back to SIGSEGV.
#[cfg(unix)]
#[test]
fn the_stack_guard_holds_on_a_small_stack() {
    let dir = scratch("small_stack");
    let program = write_program(
        &dir,
        "func down(n: Int) -> Int {
	if n == 0 {
		0
	} else {
		down(n: n - 1) + 1
	}
}
print(down(n: 4000000))
",
    );
    let emitted = talk(&["c", &program.to_string_lossy()]);
    assert!(emitted.status.success(), "`talk c` failed");
    let source = dir.join("program.c");
    std::fs::write(&source, &emitted.stdout).expect("write emitted C");
    let binary = dir.join("program.bin");
    assert!(
        Command::new("cc")
            .args(["-O2", "-std=c11"])
            .arg(&source)
            .arg("-o")
            .arg(&binary)
            .status()
            .expect("run `cc`")
            .success(),
        "emitted C did not compile"
    );

    for kilobytes in [8192, 1024, 256] {
        let run = Command::new("sh")
            .arg("-c")
            .arg(format!(
                "ulimit -s {kilobytes}; exec {}",
                binary.to_string_lossy()
            ))
            .output()
            .expect("run under a reduced stack");
        assert_eq!(
            run.status.code(),
            Some(1),
            "at ulimit -s {kilobytes} the guard did not hold; a `None` code means a signal.\nstderr: {}",
            String::from_utf8_lossy(&run.stderr)
        );
        assert!(
            String::from_utf8_lossy(&run.stderr).contains("call stack overflow"),
            "at ulimit -s {kilobytes}, expected the overflow diagnostic"
        );
    }
}

/// A result that is not a scalar still has to render the way the runtime
/// renders it, which needs the struct's and its members' names — MIR
/// carries only symbols, so those travel as static tables. Programs whose
/// result is an aggregate are otherwise accepted by the backend and then
/// fail only once compiled, which is the worst place to find out.
#[test]
fn aggregate_results_render_like_the_interpreter() {
    for (name, source) in [
        ("tuple", "let x = (1, 2)\nx\n"),
        (
            "record",
            "struct Point {\n\tlet x: Int\n\tlet y: Int\n}\nPoint(x: 3, y: 4)\n",
        ),
        (
            "variant_payload",
            "enum Shape {\n\tcase dot\n\tcase line(Int)\n}\nShape.line(7)\n",
        ),
        (
            "variant_bare",
            "enum Shape {\n\tcase dot\n\tcase line(Int)\n}\nShape.dot\n",
        ),
        ("string", "\"hi\\tthere\"\n"),
        (
            "nested",
            "struct Pair {\n\tlet left: Int\n\tlet right: Bool\n}\n(Pair(left: 1, right: true), 2)\n",
        ),
        // A protocol existential renders as its payload; the witness
        // table behind it is representation, not output.
        (
            "existential",
            "struct Wrap {\n\tlet n: Int\n}\n             extend Wrap: Showable {\n\tfunc show() -> String {\n\t\t\"wrap\"\n\t}\n}\n             let x: any Showable = Wrap(n: 7)\nx\n",
        ),
        // A Talk string is bytes, so slicing one mid-character leaves a
        // sequence that is not valid UTF-8. The runtime converts
        // lossily, and each invalid subpart has to become one U+FFFD
        // here too rather than reaching the output raw.
        (
            "lossy_utf8",
            "let s = \"\u{e9}\"\ns.utf8().slice(start: 1, byte_count: 1).to_string()\n",
        ),
    ] {
        let dir = scratch(&format!("render_{name}"));
        let program = write_program(&dir, source);
        let expected = {
            let output = talk(&["run", &program.to_string_lossy()]);
            assert!(
                output.status.success(),
                "{name}: `talk run` failed:\n{}",
                String::from_utf8_lossy(&output.stderr)
            );
            String::from_utf8(output.stdout).expect("UTF-8")
        };

        let emitted = talk(&["c", &program.to_string_lossy()]);
        assert!(
            emitted.status.success(),
            "{name}: `talk c` failed:\n{}",
            String::from_utf8_lossy(&emitted.stderr)
        );
        let source_path = dir.join("program.c");
        std::fs::write(&source_path, &emitted.stdout).expect("write emitted C");
        let binary = dir.join("program.bin");
        let compile = Command::new("cc")
            .args(["-O2", "-std=c11", "-Wall", "-Werror"])
            .arg(&source_path)
            .arg("-o")
            .arg(&binary)
            .output()
            .expect("run `cc`");
        assert!(
            compile.status.success(),
            "{name}: emitted C did not compile:\n{}",
            String::from_utf8_lossy(&compile.stderr)
        );
        let run = Command::new(&binary).output().expect("run the program");
        assert!(
            run.status.success(),
            "{name}: the compiled program failed:\n{}",
            String::from_utf8_lossy(&run.stderr)
        );
        assert_eq!(
            String::from_utf8_lossy(&run.stdout),
            expected,
            "{name}: rendering disagrees with the interpreter"
        );
    }
}

/// Cross-compiling needs more than a compiler — headers and a libc for
/// the target too — so it goes through `zig cc`. When zig is not there,
/// the failure has to say so and say what to do, rather than surfacing a
/// "command not found" from a child process.
///
/// Forced by handing the build a PATH with nothing on it, so the test
/// runs the same way on a machine that does have zig installed.
#[test]
fn cross_compiling_without_zig_explains_itself() {
    let dir = scratch("cross_without_zig");
    let program = write_program(&dir, "print(1)\n");
    let output = Command::new(env!("CARGO_BIN_EXE_talk"))
        .args(["build", "--native"])
        .arg(&program)
        .arg("-o")
        .arg(dir.join("program.bin"))
        .args(["--target", "aarch64-linux-musl"])
        .env("PATH", "/nonexistent")
        .output()
        .expect("run `talk build`");

    assert!(!output.status.success(), "the build should have failed");
    let message = String::from_utf8_lossy(&output.stderr);
    assert!(
        message.contains("needs `zig` on PATH"),
        "expected the missing-toolchain explanation, got:\n{message}"
    );
    assert!(
        message.contains("ziglang.org") && message.contains("--cc"),
        "expected both a way to install it and the escape hatch, got:\n{message}"
    );
}

/// An entry the generated `main` cannot call is refused rather than
/// emitted as something that happens to compile. The driver's own entry
/// gate catches this one before the backend sees it, which is why the
/// message is its wording rather than the backend's.
///
/// Nothing in the corpora still reaches the emitter's `unsupported`
/// path: every MIR instruction is translated, and the instruction match
/// is exhaustive, so a variant added to MIR later is a compile error in
/// the backend rather than a program that quietly does something else.
#[test]
fn an_entry_with_parameters_is_rejected() {
    let dir = scratch("entry_arity");
    let program = write_program(&dir, "pub func bench(n: Int) -> Int {\n\tn\n}\n");
    let output = talk(&["c", "--entry", "bench", &program.to_string_lossy()]);
    assert!(
        !output.status.success(),
        "a parameterized entry must be rejected"
    );
    assert!(
        String::from_utf8_lossy(&output.stderr).contains("must take no parameters"),
        "expected the entry gate's rejection, got:\n{}",
        String::from_utf8_lossy(&output.stderr)
    );
}

/// The export list every library-mode test emits from the shared
/// fixture: scalar, String, aggregate, effect, and failure cases.
const LIBRARY_EXPORTS: [&str; 9] = [
    "double", "crash", "greet", "shout", "length", "pair", "total", "handled", "leave",
];

/// ADR 0048 library mode end to end: `talk c --export` emits a real
/// library artifact — no `main`, prefixed wrappers, a header, and a
/// manifest — that links against the shared C harness. The harness takes
/// the VM oracle's answers as arguments, so scalar, String, aggregate,
/// effect, and failure cases all agree with the interpreter, and traps
/// and exit requests come back as statuses instead of terminating the
/// host.
#[test]
fn library_artifact_serves_the_shared_c_harness() {
    let dir = scratch("library");
    let fixtures = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/native-library");
    let program = fixtures.join("library.tlk");
    let oracle = interpreted(&program);
    let oracle: Vec<&str> = oracle.split_whitespace().collect();
    assert_eq!(oracle.len(), 4, "the VM oracle prints four values");

    let header = dir.join("mylib.h");
    let manifest = dir.join("mylib.manifest");
    let mut arguments = vec!["c"];
    for export in LIBRARY_EXPORTS {
        arguments.extend(["--export", export]);
    }
    let header_path = header.to_string_lossy().into_owned();
    let manifest_path = manifest.to_string_lossy().into_owned();
    let program_path = program.to_string_lossy().into_owned();
    arguments.extend(["--allow-effect", "io", "--prefix", "mylib"]);
    arguments.extend(["--header", &header_path, "--manifest", &manifest_path]);
    arguments.push(&program_path);
    let output = talk(&arguments);
    assert!(
        output.status.success(),
        "`talk c --export` failed:\n{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let library_source = String::from_utf8(output.stdout).expect("emitted C is UTF-8");
    assert!(
        !library_source.contains("int main("),
        "a library artifact must not contain a process entry"
    );
    let manifest_text = std::fs::read_to_string(&manifest).expect("read manifest");
    for export in LIBRARY_EXPORTS {
        assert!(
            manifest_text.contains(&format!("{export}\tmylib_{export}\n")),
            "manifest is missing {export}:\n{manifest_text}"
        );
    }

    let source = dir.join("library.c");
    std::fs::write(&source, &library_source).expect("write emitted C");
    let binary = dir.join("harness.bin");
    let compile = Command::new("cc")
        .arg("-O2")
        .arg("-std=c11")
        .arg("-Wall")
        .arg("-Werror")
        .arg("-I")
        .arg(&dir)
        .arg(&source)
        .arg(fixtures.join("harness.c"))
        .arg("-o")
        .arg(&binary)
        .output()
        .expect("run `cc`");
    assert!(
        compile.status.success(),
        "library + harness did not compile:\n{}",
        String::from_utf8_lossy(&compile.stderr)
    );

    let run = Command::new(&binary)
        .args(&oracle)
        .output()
        .expect("run harness");
    assert!(
        run.status.success(),
        "harness failed (exit {:?}):\n{}",
        run.status.code(),
        String::from_utf8_lossy(&run.stderr)
    );
}

/// ADR 0050 validation item 12: managed-buffer ownership must balance
/// under concurrent clone (retain), release, and uniqueness stress. The
/// harness hammers one shared allocation from many threads with balanced
/// retain/free pairs, then churns private allocations on every thread;
/// non-atomic owner transitions lose updates and fail the final balance
/// checks (or trap on a phantom double free).
const OWNERSHIP_STRESS_HARNESS: &str = r#"
#include <pthread.h>

enum { TALK_STRESS_THREADS = 8, TALK_STRESS_ITERS = 200000 };

static unsigned char *talk_stress_shared;

static void *talk_stress_shared_churn(void *arg) {
    (void)arg;
    TalkValue value = talk_pointer(talk_stress_shared);
    for (int i = 0; i < TALK_STRESS_ITERS; i++) {
        talk_retain(value);
        if (talk_is_unique(value).v.i) {
            /* The owner plus this thread's retain are always live, so a
             * unique observation means the count lost updates. */
            fprintf(stderr, "uniqueness observed through a shared count\n");
            exit(1);
        }
        talk_free(value);
    }
    return NULL;
}

static void *talk_stress_private_churn(void *arg) {
    (void)arg;
    for (int i = 0; i < TALK_STRESS_ITERS / 10; i++) {
        TalkValue buffer = talk_alloc(talk_int(32), TALK_MEM_BYTE);
        talk_retain(buffer);
        talk_free(buffer);
        talk_free(buffer);
    }
    return NULL;
}

static int talk_stress_run(void *(*worker)(void *)) {
    pthread_t threads[TALK_STRESS_THREADS];
    for (int i = 0; i < TALK_STRESS_THREADS; i++) {
        if (pthread_create(&threads[i], NULL, worker, NULL) != 0) {
            return 1;
        }
    }
    for (int i = 0; i < TALK_STRESS_THREADS; i++) {
        if (pthread_join(threads[i], NULL) != 0) {
            return 1;
        }
    }
    return 0;
}

int main(void) {
    TalkValue shared = talk_alloc(talk_int(64), TALK_MEM_BYTE);
    talk_stress_shared = shared.v.ptr;
    if (talk_stress_run(talk_stress_shared_churn) != 0) {
        return 1;
    }
    if (!talk_is_unique(shared).v.i) {
        fprintf(stderr, "shared count corrupted after balanced churn\n");
        return 1;
    }
    talk_free(shared);
    if (talk_stress_run(talk_stress_private_churn) != 0) {
        return 1;
    }
    if (talk_live_allocations != 0) {
        fprintf(stderr, "allocation balance corrupted\n");
        return 1;
    }
    printf("ok\n");
    return 0;
}
"#;

#[test]
fn native_runtime_ownership_balances_under_concurrent_stress() {
    let dir = scratch("atomic_ownership_stress");
    let mut source = String::from(talk_native_runtime::source());
    source.push_str(OWNERSHIP_STRESS_HARNESS);
    let path = dir.join("stress.c");
    std::fs::write(&path, source).expect("write stress harness");

    let binary = dir.join("stress.bin");
    let compile = Command::new("cc")
        .arg("-O2")
        .arg("-std=c11")
        .arg("-pthread")
        .arg("-Wno-unused-function")
        .arg(&path)
        .arg("-o")
        .arg(&binary)
        .output()
        .expect("run `cc`");
    assert!(
        compile.status.success(),
        "runtime + stress harness did not compile:\n{}",
        String::from_utf8_lossy(&compile.stderr)
    );

    let run = Command::new(&binary).output().expect("run stress harness");
    assert!(
        run.status.success(),
        "ownership stress failed (exit {:?}):\n{}",
        run.status.code(),
        String::from_utf8_lossy(&run.stderr)
    );
    assert_eq!(String::from_utf8_lossy(&run.stdout), "ok\n");
}
