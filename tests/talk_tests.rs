use std::collections::BTreeSet;
use std::io::Write;
use std::process::{Command, Stdio};

#[test]
fn format_does_not_add_a_blank_line_at_eof() {
    let mut child = Command::new(env!("CARGO_BIN_EXE_talk"))
        .arg("format")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .spawn()
        .expect("run `talk format`");

    child
        .stdin
        .take()
        .expect("piped stdin")
        .write_all(b"let x=1\n")
        .expect("write source");

    let output = child.wait_with_output().expect("read formatter output");
    assert!(output.status.success(), "`talk format` failed");
    assert_eq!(output.stdout, b"let x = 1\n");
}

#[test]
fn mir_is_optimized_by_default_and_no_opt_renders_raw_mir() {
    let source = b"func f() -> Int {\n\tlet x = 1 + 2\n\t4\n}\nf()\n";
    let render = |arguments: &[&str]| {
        let mut child = Command::new(env!("CARGO_BIN_EXE_talk"))
            .arg("mir")
            .args(arguments)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .expect("run `talk mir`");
        child
            .stdin
            .take()
            .expect("piped stdin")
            .write_all(source)
            .expect("write Talk source");
        child.wait_with_output().expect("read MIR output")
    };

    let optimized = render(&[]);
    assert!(
        optimized.status.success(),
        "{}",
        String::from_utf8_lossy(&optimized.stderr)
    );
    let raw = render(&["--no-opt"]);
    assert!(
        raw.status.success(),
        "{}",
        String::from_utf8_lossy(&raw.stderr)
    );

    let optimized = String::from_utf8(optimized.stdout).expect("optimized MIR is UTF-8");
    assert!(
        !optimized
            .split("\nfn")
            .any(|section| section.contains(" f ")),
        "optimized MIR retained the unreachable function:\n{optimized}"
    );
    assert!(
        !optimized.contains("PushHandler") && !optimized.contains(" _io_host "),
        "optimized MIR retained unused host handlers:\n{optimized}"
    );

    let raw = String::from_utf8(raw.stdout).expect("raw MIR is UTF-8");
    let raw_f = raw
        .split("\nfn")
        .find(|section| section.contains(" f "))
        .expect("f in raw MIR");
    assert!(
        raw_f.contains("Call"),
        "--no-opt did not retain the unused computation:\n{raw_f}"
    );
    assert!(
        raw.contains("PushHandler") && raw.contains(" _io_host "),
        "--no-opt did not retain host handlers:\n{raw}"
    );
}

fn run_source(source: &[u8], arguments: &[&str]) -> std::process::Output {
    let mut child = Command::new(env!("CARGO_BIN_EXE_talk"))
        .arg("run")
        .args(arguments)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("run `talk run`");
    child
        .stdin
        .take()
        .expect("piped stdin")
        .write_all(source)
        .expect("write Talk source");
    child.wait_with_output().expect("read run output")
}

/// `talk check` compiles every callable rigidly (check-all), exercising
/// the generic witness machinery without needing a runtime instantiation.
fn check_source(source: &[u8]) -> std::process::Output {
    // `-` pins stdin explicitly: bare `talk check` inside a package
    // checks the package workspace instead of reading stdin.
    let mut child = Command::new(env!("CARGO_BIN_EXE_talk"))
        .arg("check")
        .arg("-")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("run `talk check`");
    child
        .stdin
        .take()
        .expect("piped stdin")
        .write_all(source)
        .expect("write Talk source");
    child.wait_with_output().expect("read check output")
}

fn assert_checks(source: &[u8]) {
    let output = check_source(source);
    assert!(
        output.status.success(),
        "stderr:\n{}",
        String::from_utf8_lossy(&output.stderr)
    );
}

fn assert_runs(source: &[u8], arguments: &[&str], expected_stdout: &[u8]) {
    let output = run_source(source, arguments);
    assert!(
        output.status.success(),
        "stderr:\n{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert_eq!(
        output.stdout,
        expected_stdout,
        "stdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(output.stderr.is_empty());
}

fn for_each_corpus_case<T: Sync>(cases: &[T], run: impl Fn(&T) + Sync) {
    if cases.is_empty() {
        return;
    }
    let available = std::thread::available_parallelism().map_or(1, usize::from);
    let configured = std::env::var("TALK_TEST_JOBS")
        .ok()
        .and_then(|value| value.parse::<usize>().ok())
        .filter(|jobs| *jobs > 0);
    // Corpus tests themselves run concurrently under libtest. Use half the
    // host by default, capped at eight, to remove the serial tail without each
    // corpus monopolizing the machine. TALK_TEST_JOBS can tune CI runners.
    let default_workers = if available == 1 {
        1
    } else {
        available.div_ceil(2).min(8)
    };
    let workers = configured.unwrap_or(default_workers).min(cases.len());
    let next = std::sync::atomic::AtomicUsize::new(0);
    std::thread::scope(|scope| {
        for _ in 0..workers {
            let run = &run;
            let next = &next;
            scope.spawn(move || {
                loop {
                    let index = next.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                    let Some(case) = cases.get(index) else {
                        break;
                    };
                    run(case);
                }
            });
        }
    });
}

#[test]
fn run_renders_a_scalar_script_result_in_talk_syntax() {
    assert_runs(b"// no-core\nlet answer = 42\nanswer\n", &[], b"42\n");
}

#[test]
fn syntax_stdlib_exposes_the_self_hosted_parser() {
    assert_runs(
        b"use syntax::{ parse_expr_source, Item }\nlet outcome = parse_expr_source(source: \"1 + 2\")\nif let .some(failure) = outcome.failure {\n\tprint(failure.code + \": \" + failure.message)\n} else {\n\tlet first: Item = outcome.items[0]\n\tmatch first {\n\t\t.expr_item(_) -> print(\"parsed\"),\n\t\t_ -> print(\"wrong root\")\n\t}\n}\n",
        &[],
        b"parsed\n",
    );
}

#[test]
fn in_struct_method_call_sites_record_borrowed_param_modes() {
    // A member call's recorded callee type must be the method's own
    // signature (borrow-by-default params), not the argument-shaped type
    // the call also unifies the callee variable with: Apply unification
    // strips borrow wrappers, so the binding order decided it, and an
    // owned-looking record made lowering move the argument while the
    // callee retained it — leaking one allocation per heap argument.
    assert_runs(
        b"struct Fail {\n\tlet code: String\n\tlet message: String\n}\nstruct P {\n\tlet failed: Fail?\n\tmut func fail(code: String, message: String) -> Void {\n\t\tself.failed = .some(Fail(code: code, message: message))\n\t}\n\tmut func run() -> Void {\n\t\tself.fail(code: \"c\", message: \"a\" + \"b\")\n\t}\n}\nlet p = P(failed: .none)\np.run()\nprint(\"ok\")\n",
        &[],
        b"ok\n",
    );
}

#[test]
fn borrowed_iteration_over_copy_inline_elements() {
    // The checker erases `&T` to `T` for Copy-grade types ("the same type
    // up to representation"), so `Optional<&Scope>` — what borrowed array
    // iteration returns — and `Optional<Scope>` — what the loop's reads
    // are laid out against — must share one flat layout. An inline Copy
    // pointee narrower than a borrow slot used to shear the two, and the
    // loop trapped with "spliced field out of range".
    assert_runs(
        b"enum ScopeKind {\n\tcase lexical\n\tcase expansion\n\tcase module\n}\nstruct Scope {\n\tlet kind: ScopeKind\n\tlet namespace: Int\n\tlet ordinal: Int\n}\nextend Scope: Copy {}\nfunc contains_scope(scopes: &Array<Scope>, namespace: Int) -> Bool {\n\tfor candidate in scopes {\n\t\tif candidate.namespace == namespace { return true }\n\t}\n\tfalse\n}\nlet scopes = [Scope(kind: ScopeKind.expansion, namespace: 1, ordinal: 2)]\nif contains_scope(scopes: scopes, namespace: 1) {\n\tprint(\"found\")\n} else {\n\tprint(\"missing\")\n}\n",
        &[],
        b"found\n",
    );
}

#[test]
fn conditional_deinit_row_requires_its_context() {
    // ADR 0036: a conditional Deinit row is evidence only where its context
    // holds. Box<S> (S: Marker false) must NOT run the destructor; Box<M>
    // (M: Marker) must.
    assert_runs(
        b"protocol Marker {}\nstruct Box<T> { let value: T }\nextend<T> Box<T>: Deinit where T: Marker {\n\tconsuming func deinit() -> Void {\n\t\tprint(\"dropped\")\n\t}\n}\nstruct S {}\nstruct M {}\nextend M: Marker {}\nfunc makeS() {\n\tlet quiet = Box(value: S())\n}\nfunc makeM() {\n\tlet loud = Box(value: M())\n}\nmakeS()\nmakeM()\nprint(\"done\")\n",
        &[],
        b"dropped\ndone\n",
    );
}

#[test]
fn disjoint_inherent_extensions_dispatch_per_application() {
    assert_runs(
        b"struct Box<T> { let value: T }\nextend Box<Int> { func tag() -> Int { 1 } }\nextend Box<Bool> { func tag() -> Int { 2 } }\nprint(Box(value: 0).tag())\nprint(Box(value: true).tag())\n",
        &[],
        b"1\n2\n",
    );
}

#[test]
fn trailing_block_closures_mutate_captured_locals() {
    // Assignment conversion (celled captures) must see a trailing block as
    // a nested frame, exactly like an explicit `func` expression.
    assert_runs(
        b"func run(consume fn: () -> Void) -> Void { fn() }\nfunc outer() -> Int {\n\tlet i = 0\n\trun { i = i + 1 }\n\trun { i = i + 1 }\n\ti\n}\nprint(outer())\n",
        &[],
        b"2\n",
    );
    // The motivating shape: a counting closure passed to `Int.times`.
    assert_runs(
        b"func outer() -> Int {\n\tlet i = 0\n\t5.times { x in i = i + 1 }\n\ti\n}\nprint(outer())\n",
        &[],
        b"5\n",
    );
}

#[test]
fn closures_with_ambient_core_effects_run_without_handlers() {
    // A closure whose effect row mentions core's ambient effects ('alloc
    // here, via Array operations) must not capture a capability for them:
    // the runtime is their implicit handler and no explicit one can exist.
    assert_runs(
        b"func run(consume fn: () -> Int) -> Int { fn() }\nprint(run { [2, 3, 1].sort_by { $0 > $1 }[0] })\n",
        &[],
        b"3\n",
    );
}

#[test]
fn run_executes_core_operators() {
    assert_runs(b"let answer = 40 + 2\nanswer\n", &[], b"42\n");
    assert_runs(b"(1 + 2) <= 3\n", &[], b"true\n");
    assert_runs(b"1.5 + 2.25\n", &[], b"3.75\n");
    assert_runs(b"!(1 == 2)\n", &[], b"true\n");
}

#[test]
fn spliced_member_chains_fold_to_one_read() {
    // `o.inner.x` is statically slot 0 of `o` (ADR 0046): the chain
    // folds at emission and dead code collects the intermediate, so the
    // optimized MIR carries exactly one member read.
    let unique = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .expect("system clock after epoch")
        .as_nanos();
    let dir = std::env::temp_dir().join(format!("talk-fold-{}-{unique}", std::process::id()));
    std::fs::create_dir_all(&dir).expect("create fixture dir");
    let path = dir.join("chain.tlk");
    std::fs::write(
        &path,
        b"struct Inner {\n\tlet x: Int\n\tlet y: Int\n}\nstruct Outer {\n\tlet inner: Inner\n\tlet z: Int\n}\nfunc pick(o: Outer) -> Int {\n\to.inner.x\n}\nlet choose = pick\nprint(choose(Outer(inner: Inner(x: 7, y: 8), z: 9)))\n",
    )
    .expect("write chain program");
    let mir = Command::new(env!("CARGO_BIN_EXE_talk"))
        .args(["mir", path.to_str().expect("utf8 path")])
        .output()
        .expect("render mir");
    assert!(
        mir.status.success(),
        "{}",
        String::from_utf8_lossy(&mir.stderr)
    );
    let rendered = String::from_utf8_lossy(&mir.stdout);
    let pick = rendered
        .split("\nfn")
        .find(|section| section.contains(" pick "))
        .expect("pick in render");
    assert_eq!(
        pick.matches("Field {").count(),
        1,
        "the chain should fold to one read:\n{pick}"
    );
}

#[test]
fn inline_array_literal_and_checked_get_reach_runtime() {
    assert_runs(
        b"let values: [Int; 3] = [10, 20, 30]\n\
          let present = if let .some(value) = values.get(1) { value } else { 0 }\n\
          let missing = if let .some(value) = values.get(3) { value } else { 99 }\n\
          present + missing\n",
        &[],
        b"119\n",
    );
}

#[test]
fn inline_array_drops_owned_elements() {
    assert_runs(
        b"func lengths() -> Int {\n\
          \tlet values: [String; 2] = [\"a\" + \"b\", \"c\" + \"d\"]\n\
          \tif let .some(value) = values.get(1) { value.byte_count } else { 0 }\n\
          }\n\
          lengths()\n",
        &[],
        b"2\n",
    );
}

#[test]
fn generic_inline_array_body_specializes_for_multiple_counts() {
    assert_runs(
        b"func sum<static N: Int>(values: [Int; N]) -> Int {\n\
          \tlet total = 0\n\
          \tlet index = 0\n\
          \tloop index < N {\n\
          \t\tif let .some(value) = values.get(index) {\n\
          \t\t\ttotal = total + value\n\
          \t\t}\n\
          \t\tindex = index + 1\n\
          \t}\n\
          \ttotal\n\
          }\n\
          let pair: [Int; 2] = [1, 2]\n\
          let triple: [Int; 3] = [3, 4, 5]\n\
          sum(values: pair) + sum(values: triple)\n\
          ",
        &[],
        b"15\n",
    );
}

#[test]
fn nested_inline_arrays_preserve_exact_shape() {
    assert_runs(
        b"let matrix: [[Int; 2]; 2] = [[1, 2], [3, 4]]\n\
          if let .some(row) = matrix.get(1) {\n\
          \tif let .some(value) = row.get(0) { value } else { 0 }\n\
          } else { 0 }\n",
        &[],
        b"3\n",
    );
}

#[test]
fn static_value_generics_reach_runtime() {
    // ADR 0035 §6: a static parameter is usable as an ordinary value in
    // its declaration body; the backend substitutes the concrete value
    // during specialization. Exercises explicit static arguments, closed
    // arithmetic, inference from an argument type, and two distinct
    // instantiations of one generic body.
    assert_runs(
        b"struct Grid<static Rows: Int> {}\n\
          func width<static N: Int>() -> Int {\n\
          \tN\n\
          }\n\
          func rows<static R: Int>(g: Grid<R>) -> Int {\n\
          \tR\n\
          }\n\
          let g = Grid<7>()\n\
          width<4>() + width<2 + 1>() + rows(g: g)\n\
          ",
        &[],
        b"14\n",
    );
}

#[test]
fn func_static_default_reaches_runtime() {
    assert_runs(
        b"func number<static N: Int = 4>() -> Int {\n\
          \tN\n\
          }\n\
          number() + number<10>()\n",
        &[],
        b"14\n",
    );
}

#[test]
fn static_enum_case_param_usable_as_value() {
    assert_runs(
        b"enum Color {\n\
          \tcase red\n\
          \tcase green\n\
          }\n\
          struct Paint<static C: Color> {}\n\
          func shade<static C: Color>(p: Paint<C>) -> Color {\n\
          \tC\n\
          }\n\
          let p = Paint<Color.green>()\n\
          match shade(p: p) { .red -> print(0), .green -> print(1) }\n\
          ",
        &[],
        b"1\n",
    );
}

#[test]
fn protocol_default_body_reads_owner_static_param() {
    // ADR 0035 §6 applies to protocol defaults too: the conformance's
    // protocol application pins the owner's static parameter, and the
    // default body reads it as a value.
    assert_runs(
        b"protocol Sized<static N: Int> {\n\
          \tfunc size() -> Int { N }\n\
          }\n\
          struct Four {}\n\
          extend Four: Sized<4> {}\n\
          struct Nine {}\n\
          extend Nine: Sized<9> {}\n\
          Four().size() + Nine().size()\n",
        &[],
        b"13\n",
    );
}

#[test]
fn static_generic_func_as_value_specializes_when_type_pins_statics() {
    assert_runs(
        b"struct Grid<static Rows: Int> {}\n\
          func rows<static R: Int>(g: Grid<R>) -> Int {\n\
          \tR\n\
          }\n\
          func apply(f: (Grid<3>) -> Int, g: Grid<3>) -> Int {\n\
          \tf(g)\n\
          }\n\
          let g = Grid<3>()\n\
          apply(f: rows, g: g)\n\
          ",
        &[],
        b"3\n",
    );
}

#[test]
fn static_generic_func_as_value_rejects_unpinned_statics() {
    let output = run_source(
        b"func width<static N: Int>() -> Int {\n\
          \tN\n\
          }\n\
          func apply0(f: () -> Int) -> Int {\n\
          \tf()\n\
          }\n\
          apply0(f: width)\n\
          ",
        &[],
    );
    assert!(
        !output.status.success(),
        "unpinned static use should be rejected"
    );
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("static") || stderr.contains("infer"),
        "stderr should explain the unpinned static: {stderr}"
    );
}

#[test]
fn postfix_question_mark_propagates_second_enum_variant() {
    assert_runs(
        b"enum Outcome<Value, Failure> {\n\
          \tcase success(Value)\n\
          \tcase failure(Failure)\n\
          }\n\
          func source(ok: Bool) -> Outcome<Int, String> {\n\
          \tif ok { .success(41) } else { .failure(\"nope\") }\n\
          }\n\
          func outer(ok: Bool) -> Outcome<Bool, String> {\n\
          \tlet value = source(ok: ok)?\n\
          \tOutcome.success(value == 41)\n\
          }\n\
          match outer(ok: true) { .success(value) -> print(value), .failure(message) -> print(message) }\n\
          match outer(ok: false) { .success(value) -> print(value), .failure(message) -> print(message) }\n\
          ",
        &[],
        b"true\nnope\n",
    );

    assert_runs(
        b"func source(ok: Bool) -> Int? {\n\
          \tif ok { .some(41) } else { .none }\n\
          }\n\
          func outer(ok: Bool) -> Bool? {\n\
          \tlet value = source(ok: ok)?\n\
          \tOptional.some(value == 41)\n\
          }\n\
          match outer(ok: true) { .some(value) -> print(value), .none -> print(false) }\n\
          match outer(ok: false) { .some(value) -> print(value), .none -> print(false) }\n\
          ",
        &[],
        b"true\nfalse\n",
    );

    assert_runs(
        b"func source(ok: Bool) -> Result<Int, String> {\n\
          \tif ok { .ok(41) } else { .error(\"nope\") }\n\
          }\n\
          func outer(ok: Bool) -> Result<Bool, String> {\n\
          \tlet value = source(ok: ok)?\n\
          \tResult.ok(value == 41)\n\
          }\n\
          match outer(ok: true) { .ok(value) -> print(value), .error(message) -> print(message) }\n\
          match outer(ok: false) { .ok(value) -> print(value), .error(message) -> print(message) }\n\
          ",
        &[],
        b"true\nnope\n",
    );

    assert_runs(
        b"effect 'ask() -> Int\n\
          func source(ok: Bool) -> Result<Int, String> {\n\
          \tif ok { .ok(41) } else { .error(\"nope\") }\n\
          }\n\
          func outer(ok: Bool) -> Result<Int, String> {\n\
          \t#handle 'ask {\n\
          \t\tlet value = source(ok: ok)?\n\
          \t\t'continue value\n\
          \t}\n\
          \tResult.ok('ask())\n\
          }\n\
          match outer(ok: true) { .ok(value) -> print(value), .error(message) -> print(message) }\n\
          match outer(ok: false) { .ok(value) -> print(value), .error(message) -> print(message) }\n\
          ",
        &[],
        b"41\nnope\n",
    );
}

#[test]
fn run_explicit_capture_modes_over_owned_values() {
    // `[s]` (copy) retains a snapshot: the frame's binding stays usable.
    assert_runs(
        b"func f() -> Int {\n\
          \tlet s = \"a\" + \"b\"\n\
          \tlet g = func [s]() -> Int { s.byte_count }\n\
          \tg() + s.byte_count\n\
          }\n\
          print(f())\n",
        &[],
        b"4\n",
    );
    // `[&s]` aliases the frame's binding.
    assert_runs(
        b"func f() -> Int {\n\
          \tlet s = \"a\" + \"b\"\n\
          \tlet g = func [&s]() -> Int { s.byte_count }\n\
          \tg() + s.byte_count\n\
          }\n\
          print(f())\n",
        &[],
        b"4\n",
    );
    // `[consuming s]` moves the owner into the closure's slot; the
    // frame's later use is a use of a moved value.
    assert_runs(
        b"func f() -> Int {\n\
          \tlet s = \"a\" + \"b\"\n\
          \tlet g = func [consuming s]() -> Int { s.byte_count }\n\
          \tg()\n\
          }\n\
          print(f())\n",
        &[],
        b"2\n",
    );
    let output = run_source(
        b"func f() -> Int {\n\
          \tlet s = \"a\" + \"b\"\n\
          \tlet g = func [consuming s]() -> Int { s.byte_count }\n\
          \tg() + s.byte_count\n\
          }\n\
          print(f())\n",
        &[],
    );
    assert!(!output.status.success());
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(stderr.contains("moved"), "{stderr}");
}

#[test]
fn run_assigns_through_tuple_elements() {
    // `t.0 = v` and nested struct-tuple spines: runtime records are
    // tuples, so the write rebuilds the tuple along the place chain.
    assert_runs(
        b"func f() -> Int {\n\
          \tlet t = (1, 2)\n\
          \tt.0 = 41\n\
          \tt.0 + t.1\n\
          }\n\
          print(f())\n",
        &[],
        b"43\n",
    );
    assert_runs(
        b"struct P {\n\
          \tlet pair: (Int, Int)\n\
          \tinit(pair: (Int, Int)) {\n\
          \t\tself.pair = pair\n\
          \t\tself\n\
          \t}\n\
          }\n\
          func f() -> Int {\n\
          \tlet p = P(pair: (1, 2))\n\
          \tp.pair.1 = 40\n\
          \tp.pair.0 + p.pair.1\n\
          }\n\
          print(f())\n",
        &[],
        b"41\n",
    );
}

#[test]
fn run_mut_requirements_on_rvalue_receivers() {
    // A `mut func` requirement on an rvalue existential or generic
    // receiver materializes a temporary place: the call evolves the
    // temporary, which releases like any statement temp.
    assert_runs(
        b"protocol Counter {\n\
          \tmut func bump() -> Int\n\
          }\n\
          struct C {\n\
          \tlet n: Int\n\
          \tinit(n: Int) {\n\
          \t\tself.n = n\n\
          \t\tself\n\
          \t}\n\
          }\n\
          extend C: Counter {\n\
          \tmut func bump() -> Int {\n\
          \t\tself.n = self.n + 1\n\
          \t\tself.n\n\
          \t}\n\
          }\n\
          func make() -> any Counter {\n\
          \tC(n: 40)\n\
          }\n\
          print(make().bump())\n",
        &[],
        b"41\n",
    );
    assert_runs(
        b"protocol Counter {\n\
          \tmut func bump() -> Int\n\
          }\n\
          struct C {\n\
          \tlet n: Int\n\
          \tinit(n: Int) {\n\
          \t\tself.n = n\n\
          \t\tself\n\
          \t}\n\
          }\n\
          extend C: Counter {\n\
          \tmut func bump() -> Int {\n\
          \t\tself.n = self.n + 1\n\
          \t\tself.n\n\
          \t}\n\
          }\n\
          func dup<T>(consume x: T) -> T {\n\
          \tx\n\
          }\n\
          func poke<T: Counter>(consume x: T) -> Int {\n\
          \tdup(x: x).bump()\n\
          }\n\
          print(poke(x: C(n: 40)))\n",
        &[],
        b"41\n",
    );
}

#[test]
fn run_returns_donate_owned_values_from_borrowed_reads() {
    // Return position follows implicit sharing's clone-at-boundary rule:
    // a borrow-typed place read returned where the function owns donates
    // a retained reference, exactly like a call argument.
    assert_runs(
        b"enum Node {\n\
          \tcase n(Int)\n\
          }\n\
          func parse() -> Node {\n\
          \tlet roots = [Node.n(41)]\n\
          \troots[0]\n\
          }\n\
          match parse() {\n\
          \t.n(v) -> print(v)\n\
          }\n",
        &[],
        b"41\n",
    );
    assert_runs(
        b"func first(items: [String]) -> String {\n\
          \titems[0]\n\
          }\n\
          print(first(items: [\"ab\" + \"cd\"]))\n",
        &[],
        b"abcd\n",
    );
    // An explicit return statement takes the same path.
    assert_runs(
        b"func first(items: [String]) -> String {\n\
          \treturn items[0]\n\
          }\n\
          print(first(items: [\"ab\" + \"cd\"]))\n",
        &[],
        b"abcd\n",
    );
}

#[test]
fn run_borrowed_return_escape_names_the_binding() {
    // A declared `-> &T` return genuinely cannot lend frame-owned data;
    // the diagnostic names the binding and the function and suggests the
    // owned spelling.
    let output = run_source(
        b"enum Node {\n\
          \tcase n(Int)\n\
          }\n\
          func parse() -> &Node {\n\
          \tlet roots = [Node.n(41)]\n\
          \troots[0]\n\
          }\n\
          match parse() {\n\
          \t.n(v) -> print(v)\n\
          }\n",
        &[],
    );
    assert!(!output.status.success());
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(stderr.contains("cannot return a borrow"), "{stderr}");
    assert!(stderr.contains("`roots`"), "{stderr}");
    assert!(stderr.contains("`parse`"), "{stderr}");
    assert!(stderr.contains("drop the `&`"), "{stderr}");
}

#[test]
fn run_derived_equality_through_conditional_conformances() {
    // A recursive enum whose payload routes through Array's conditional
    // Equatable row: the catalog's context prover must see derived
    // conformances (`derivably_conforms`), or the row is never selected
    // and derived equality dead-ends (the talk-syntax parser.test case).
    assert_runs(
        b"enum Lit {\n\
          \tcase int(String)\n\
          \tcase list([Lit])\n\
          }\n\
          print(Lit.int(\"a\" + \"b\") == Lit.int(\"ab\"))\n\
          print(Lit.list([Lit.int(\"1\")]) == Lit.list([Lit.int(\"1\")]))\n\
          print(Lit.list([Lit.int(\"1\")]) == Lit.int(\"1\"))\n",
        &[],
        b"true\ntrue\nfalse\n",
    );
}

#[test]
fn run_packs_compound_rigid_payloads_into_existentials() {
    // Conditional conformance under a rigid element: inside `pack`'s
    // generic body, `Array<T>` coerces to `any Showable` via
    // `extend<Element: Showable> Array<Element>: Showable`. The
    // requirement closure forwards `T`'s witness block to the
    // implementation instance, and the pack's glue closures capture the
    // full evidence blocks. TALK_CHECK_ALL compiles the rigid instance
    // (the forwarding path); the entry executes the specialized one.
    let source = b"func pack<T: Showable>(consume x: T) -> any Showable {\n\
      \tlet xs = [x]\n\
      \txs\n\
      }\n\
      print(pack(x: 41))\n";
    let mut child = Command::new(env!("CARGO_BIN_EXE_talk"))
        .arg("run")
        .env("TALK_CHECK_ALL", "1")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("run `talk run`");
    child
        .stdin
        .take()
        .expect("piped stdin")
        .write_all(source)
        .expect("write Talk source");
    let output = child.wait_with_output().expect("read run output");
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(output.status.success(), "{stderr}");
    assert_eq!(output.stdout, b"[41]\n");
}

#[test]
fn run_out_of_order_record_literals() {
    // Field values evaluate in source order, then permute into the
    // row's label-sorted layout.
    assert_runs(
        b"func f() -> Int {\n\
          \tlet r = { name: \"a\" + \"b\", id: 7 }\n\
          \tmatch r {\n\
          \t\t{ name, id } -> name.byte_count + id\n\
          \t}\n\
          }\n\
          print(f())\n",
        &[],
        b"9\n",
    );
}

#[test]
fn run_constructor_references_as_values() {
    // `Enum.variant` used uncalled becomes a captureless function value.
    assert_runs(
        b"enum E {\n\
          \tcase a(Int)\n\
          \tcase b\n\
          }\n\
          func apply(f: (Int) -> E, n: Int) -> E {\n\
          \tf(n)\n\
          }\n\
          match apply(f: E.a, n: 41) {\n\
          \t.a(n) -> print(n),\n\
          \t.b -> print(0)\n\
          }\n",
        &[],
        b"41\n",
    );
}

#[test]
fn run_quoted_identifiers() {
    // @"..." spells a literal identifier, so keywords can name enum
    // cases, bindings, and patterns.
    assert_runs(
        b"enum Fizz {\n\
          \tcase #\"as\", #\"func\", #\"struct\"\n\
          }\n\
          let #\"let\" = 40\n\
          match Fizz.#\"func\" {\n\
          \t.#\"as\" -> print(0),\n\
          \t.#\"func\" -> print(#\"let\" + 2),\n\
          \t.#\"struct\" -> print(1)\n\
          }\n",
        &[],
        b"42\n",
    );
}

#[test]
fn run_or_patterns_settle_per_alternative() {
    // Alternatives leaving different owned payloads unbound re-test the
    // tag on the matched edge and release exactly the payloads the
    // matching alternative left unbound.
    assert_runs(
        b"enum E {\n\
          \tcase a(String, Int)\n\
          \tcase b(Int, String)\n\
          }\n\
          func f(e: E) -> Int {\n\
          \tmatch e {\n\
          \t\t.a(_, n) | .b(n, _) -> n\n\
          \t}\n\
          }\n\
          print(f(e: E.a(\"x\" + \"y\", 1)))\n\
          print(f(e: E.b(2, \"long\" + \"er\")))\n",
        &[],
        b"1\n2\n",
    );
    // Consumed (owned) scrutinee takes the same path.
    assert_runs(
        b"enum E {\n\
          \tcase a(String, Int)\n\
          \tcase b(Int, String)\n\
          }\n\
          func f() -> Int {\n\
          \tlet e = E.a(\"x\" + \"y\", 1)\n\
          \tmatch e {\n\
          \t\t.a(_, n) | .b(n, _) -> n\n\
          \t}\n\
          }\n\
          print(f())\n",
        &[],
        b"1\n",
    );
}

#[test]
fn run_record_patterns_bind_field_and_interior() {
    // `label: pattern` binds both names: the label binder owns the
    // value, interior binders take donated references.
    assert_runs(
        b"func f() -> Int {\n\
          \tlet r = { id: 7, name: \"a\" + \"b\" }\n\
          \tlet { name: n, id } = r\n\
          \tname.byte_count + n.byte_count + id\n\
          }\n\
          print(f())\n",
        &[],
        b"11\n",
    );
    assert_runs(
        b"func f() -> Int {\n\
          \tlet r = { id: 7, name: \"a\" + \"b\" }\n\
          \tmatch r {\n\
          \t\t{ name: n, id } -> name.byte_count + n.byte_count + id\n\
          \t}\n\
          }\n\
          print(f())\n",
        &[],
        b"11\n",
    );
}

#[test]
fn run_mut_args_through_places_and_rejects_rvalues() {
    // A `mut` effect argument through a tuple-element place writes back.
    assert_runs(
        b"effect 'adjust(mut value: Int) -> ()\n\
          #handle 'adjust { v in\n\
          \tv = v + 10\n\
          \t'continue ()\n\
          }\n\
          let t = (1, 2)\n\
          'adjust(value: mut t.0)\n\
          print(t.0 + t.1)\n\
          ",
        &[],
        b"13\n",
    );
    // A true rvalue `mut` argument is a frontend error: its evolution
    // would be silently discarded.
    for source in [
        &b"effect 'adjust(mut value: Int) -> ()\n#handle 'adjust { v in\n\tv = v + 10\n\t'continue ()\n}\n'adjust(value: mut (1 + 2))\nprint(9)\n"[..],
        &b"func inc(mut n: Int) -> Void {\n\tn = n + 1\n}\ninc(n: mut (1 + 2))\nprint(0)\n"[..],
    ] {
        let output = run_source(source, &[]);
        assert!(!output.status.success());
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(stderr.contains("must name a mutable place"), "{stderr}");
    }
}

#[test]
fn run_uninitialized_lets_use_definite_assignment() {
    // Declared-then-assigned bindings run; the born-moved state makes
    // read-before-initialization a path-sensitive diagnostic.
    assert_runs(
        b"func f() -> Int {\n\tlet x: Int\n\tx = 41\n\tx + 1\n}\nprint(f())\n",
        &[],
        b"42\n",
    );
    assert_runs(
        b"func f(c: Bool) -> Int {\n\tlet x: Int\n\tif c { x = 1 } else { x = 2 }\n\tx\n}\nprint(f(c: true))\n",
        &[],
        b"1\n",
    );
    // Owned content initializes and releases exactly once; a
    // never-initialized owned binding releases nothing.
    assert_runs(
        b"func f() -> Int {\n\tlet s: String\n\ts = \"a\" + \"b\"\n\ts.byte_count\n}\nprint(f())\n",
        &[],
        b"2\n",
    );
    assert_runs(
        b"func f() -> Int {\n\tlet s: String\n\t7\n}\nprint(f())\n",
        &[],
        b"7\n",
    );
    // Read before any assignment is rejected.
    let output = run_source(
        b"func f() -> Int {\n\tlet x: Int\n\tx + 1\n}\nprint(f())\n",
        &[],
    );
    assert!(!output.status.success());
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(stderr.contains("before it is initialized"), "{stderr}");
    // Initialization on only one path is rejected at the join.
    let output = run_source(
        b"func f(c: Bool) -> Int {\n\tlet x: Int\n\tif c { x = 1 }\n\tx\n}\nprint(f(c: true))\n",
        &[],
    );
    assert!(!output.status.success());
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(stderr.contains("before it is initialized"), "{stderr}");
}

#[test]
fn run_closure_mutates_captured_owned_value() {
    // A mutated-and-captured owning binding cells with owning content:
    // assignment releases the displaced value, the frame releases the
    // cell's final content at scope exit.
    assert_runs(
        b"func f() -> Int {\n\
          \tlet s = \"a\" + \"b\"\n\
          \tlet bump = func() -> Void { s = s + \"c\" }\n\
          \tbump()\n\
          \tbump()\n\
          \ts.byte_count\n\
          }\n\
          print(f())\n",
        &[],
        b"4\n",
    );
    // The frame's own assignments to a celled owning binding release
    // displaced content too.
    assert_runs(
        b"func f() -> Int {\n\
          \tlet s = \"a\" + \"b\"\n\
          \tlet read = func() -> Int { s.byte_count }\n\
          \ts = s + \"c\"\n\
          \tread()\n\
          }\n\
          print(f())\n",
        &[],
        b"3\n",
    );
}

#[test]
fn run_closure_captures_owned_local() {
    // A closure capturing an owned buffer retains a frame-anchored
    // snapshot; the frame releases it at scope exit (ADR 0037 §closures).
    assert_runs(
        b"func f() -> Int {\n\
          \tlet s = \"a\" + \"b\"\n\
          \tlet g = func() -> Int { s.byte_count }\n\
          \tg() + g()\n\
          }\n\
          print(f())\n",
        &[],
        b"4\n",
    );
}

#[test]
fn run_trailing_closure_captures_method_receiver() {
    // The ADR 0037 motivating case: `self` (a borrowed receiver over a
    // buffer-holding struct) captured by a trailing block.
    assert_runs(
        b"struct Lexer {\n\
          \tlet source: String\n\
          \tinit(source: String) {\n\
          \t\tself.source = source\n\
          \t\tself\n\
          \t}\n\
          \tfunc first_byte_count() -> Optional<Int> {\n\
          \t\tOptional.some(1).map { n in self.source.byte_count + n }\n\
          \t}\n\
          }\n\
          match Lexer(source: \"ab\" + \"cd\").first_byte_count() {\n\
          \t.some(n) -> print(n),\n\
          \t.none -> print(0)\n\
          }\n",
        &[],
        b"5\n",
    );
}

#[test]
fn run_matches_float_literal_patterns() {
    assert_runs(
        b"func classify(x: Float) -> Int {\n\
          \tmatch x {\n\
          \t\t1.5 -> 1,\n\
          \t\t2.5 -> 2,\n\
          \t\t_ -> 0\n\
          \t}\n\
          }\n\
          print(classify(x: 1.5))\n\
          print(classify(x: 2.5))\n\
          print(classify(x: 3.5))\n",
        &[],
        b"1\n2\n0\n",
    );
}

#[test]
fn run_executes_branches_recursion_and_loops() {
    assert_runs(
        b"func sum(n: Int) -> Int {\n\
          \tif n <= 0 { return 0 }\n\
          \tn + sum(n: n - 1)\n\
          }\n\
          sum(n: 10)\n\
          ",
        &[],
        b"55\n",
    );
    assert_runs(
        b"func sum_to(limit: Int) -> Int {\n\
          \tlet total = 0\n\
          \tlet i = 1\n\
          \tloop i <= limit {\n\
          \t\ttotal = total + i\n\
          \t\ti = i + 1\n\
          \t}\n\
          \ttotal\n\
          }\n\
          sum_to(limit: 10)\n\
          ",
        &[],
        b"55\n",
    );
}

#[test]
fn run_suppresses_a_unit_result() {
    assert_runs(b"// no-core\nlet a = 1\n", &[], b"");
}

#[test]
fn run_executes_an_explicit_entry_function() {
    let source = b"// no-core\n\
        pub func one() -> Int { return 1 }\n\
        pub func two() -> Int { return 2 }\n";
    assert_runs(source, &["--entry", "two"], b"2\n");
}

#[test]
fn run_falls_back_to_main_when_there_is_no_script_body() {
    assert_runs(b"pub func main() -> Int { return 41 + 1 }\n", &[], b"42\n");
}

#[test]
fn run_builds_projects_and_destructures_tuples() {
    assert_runs(
        b"func line_col() -> (Int, Int) { (3, 7) }\nlet p = line_col()\np.0 + p.1\n",
        &[],
        b"10\n",
    );
    assert_runs(b"let nested = ((1, 2), 3)\nnested.0.1\n", &[], b"2\n");
    assert_runs(
        b"func first(pair: &(Int, Int)) -> Int {\n\tpair.0\n}\nfirst(pair: (9, 10))\n",
        &[],
        b"9\n",
    );
    assert_runs(b"let (a, b) = (40, 2)\na + b\n", &[], b"42\n");
}

#[test]
fn run_renders_a_tuple_result_in_talk_syntax() {
    assert_runs(b"(1, true)\n", &[], b"(1, true)\n");
}

#[test]
fn run_matches_record_patterns() {
    // Reference pin: vm_matches_evaluator_on_record_literal_patterns.
    assert_runs(
        b"let record = { x: 123, y: 456 }\n\
          let result = match record {\n\
          \t{ x, y: 123 } -> 1,\n\
          \t{ x, y: 456 } -> 2,\n\
          \t{ x, y: _ } -> 3\n\
          }\n\
          result\n",
        &[],
        b"2\n",
    );
    // `label: pattern` binds the label as well as matching the pattern
    // (the reference lowering binds both names).
    assert_runs(
        b"let r = { x: 5, y: 7 }\n\
          match r { { x, y: n } -> x * 10 + n + y }\n",
        &[],
        b"64\n",
    );
    // Field order in the pattern is free; the row fixes the layout.
    assert_runs(
        b"let r = { x: 1, y: 2 }\n\
          match r { { y, x } -> x * 10 + y }\n",
        &[],
        b"12\n",
    );
    // Nested record patterns.
    assert_runs(
        b"let r = { p: { x: 4, y: 5 }, t: 9 }\n\
          match r { { p: { x, y }, t } -> x + y + t }\n",
        &[],
        b"18\n",
    );
    // `..` skips the remaining fields; an owned skipped field still
    // releases (drop-on-the-floor, not a leak).
    assert_runs(
        b"let r = { name: \"talk\", note: \"dropped\" }\n\
          match r { { name, .. } -> name.byte_count }\n",
        &[],
        b"4\n",
    );
    // Record patterns nested in enum payloads.
    assert_runs(
        b"enum Node {\n\
          \tcase leaf({ x: Int, y: Int })\n\
          \tcase empty\n\
          }\n\
          match Node.leaf({ x: 30, y: 12 }) {\n\
          \t.leaf({ x, y }) -> x + y,\n\
          \t.empty -> 0\n\
          }\n",
        &[],
        b"42\n",
    );
}

#[test]
fn run_destructures_structs_with_let() {
    // `Point { x, y }` binds each named stored field.
    assert_runs(
        b"struct Point {\n\tlet x: Int\n\tlet y: Int\n\tinit(x: Int, y: Int) {\n\t\tself.x = x\n\t\tself.y = y\n\t\tself\n\t}\n}\nlet Point { x, y } = Point(x: 3, y: 4)\nx + y\n",
        &[],
        b"7\n",
    );
    // `..` leaves the rest to the aggregate; owned unmentioned fields
    // still release exactly once (balance-verified).
    assert_runs(
        b"struct Pair {\n\tlet name: String\n\tlet tag: String\n\tinit(name: String, tag: String) {\n\t\tself.name = name\n\t\tself.tag = tag\n\t\tself\n\t}\n}\nlet Pair { name, .. } = Pair(name: \"ab\" + \"c\", tag: \"x\" + \"y\")\nname.byte_count\n",
        &[],
        b"3\n",
    );
    // `field: pattern` destructures the interior.
    assert_runs(
        b"struct Wrap {\n\tlet inner: (Int, Int)\n\tinit(inner: (Int, Int)) {\n\t\tself.inner = inner\n\t\tself\n\t}\n}\nlet Wrap { inner: (a, b) } = Wrap(inner: (2, 5))\na * b\n",
        &[],
        b"10\n",
    );
}

#[test]
fn run_matches_struct_patterns() {
    // Refutable field sub-patterns select arms.
    assert_runs(
        b"struct Point {\n\tlet x: Int\n\tlet y: Int\n\tinit(x: Int, y: Int) {\n\t\tself.x = x\n\t\tself.y = y\n\t\tself\n\t}\n}\nfunc classify(p: Point) -> Int {\n\tmatch p {\n\t\tPoint { x: 0, y } -> y,\n\t\tPoint { x, .. } -> x\n\t}\n}\nclassify(p: Point(x: 0, y: 9)) + classify(p: Point(x: 7, y: 1))\n",
        &[],
        b"16\n",
    );
    // A consumed scrutinee moves owned fields into the binders.
    assert_runs(
        b"struct Named {\n\tlet name: String\n\tlet id: Int\n\tinit(name: String, id: Int) {\n\t\tself.name = name\n\t\tself.id = id\n\t\tself\n\t}\n}\nfunc read(consume n: Named) -> Int {\n\tmatch n {\n\t\tNamed { name, .. } -> name.byte_count\n\t}\n}\nread(n: Named(name: \"ab\" + \"cd\", id: 1))\n",
        &[],
        b"4\n",
    );
    // Generic structs instantiate field types per scrutinee.
    assert_runs(
        b"struct Box<T> {\n\tlet value: T\n\tinit(value: T) {\n\t\tself.value = value\n\t\tself\n\t}\n}\nmatch Box(value: 41) {\n\tBox { value } -> value + 1\n}\n",
        &[],
        b"42\n",
    );
}

#[test]
fn run_destructures_heap_structs() {
    // Heap-struct fields are views of the object: binds donate a
    // reference; the object's drop releases the stored fields
    // (balance-verified: 0 live 'heap objects at exit).
    assert_runs(
        b"struct Node 'heap {\n\tlet label: String\n\tlet weight: Int\n\tinit(label: String, weight: Int) {\n\t\tself.label = label\n\t\tself.weight = weight\n\t\tself\n\t}\n}\nlet Node { label, weight } = Node(label: \"ab\" + \"c\", weight: 4)\nlabel.byte_count + weight\n",
        &[],
        b"7\n",
    );
}

#[test]
fn run_destructures_records_with_let() {
    // Reference pin: vm_matches_evaluator_on_record_destructuring_let.
    assert_runs(b"let { x, y } = { x: 3, y: 4 }\nx + y\n", &[], b"7\n");
    // Owned fields transfer into the binders.
    assert_runs(
        b"let { first, second } = { first: \"a\", second: \"bb\" }\n\
          first.byte_count + second.byte_count\n",
        &[],
        b"3\n",
    );
    // Destructured binders flow into calls like any other local.
    // (Reading them from inside another function hits the pre-existing
    // once-only global storage rejection, the same as tuples.)
    assert_runs(
        b"let { a, b } = { a: 2, b: 3 }\n\
          func double(n: Int) -> Int { n * 2 }\n\
          double(n: a) + b\n",
        &[],
        b"7\n",
    );
}

#[test]
fn run_shares_mutable_captures_through_cells() {
    // Reference pin: vm_matches_evaluator_on_closure_capturing_a_cell.
    // A mutated local captured by a closure is assignment-converted to
    // a cell (ORBIT-style — Kranz et al., 1986); mutations persist
    // across calls.
    assert_runs(
        b"func makeCounter() {\n\
          \tlet i = 0\n\
          \n\
          \treturn func() {\n\
          \t\ti = i + 1\n\
          \t\ti\n\
          \t}\n\
          }\n\
          let counter = makeCounter()\n\
          counter()\n\
          counter()\n\
          counter()\n",
        &[],
        b"3\n",
    );
    // Reference pin: vm_matches_evaluator_on_independent_counters.
    // Each activation allocates its own cell.
    assert_runs(
        b"func makeCounter() {\n\
          \tlet a = 0\n\
          \treturn func() {\n\
          \t\ta = a + 1\n\
          \t\ta\n\
          \t}\n\
          }\n\
          let a = makeCounter()\n\
          let b = makeCounter()\n\
          a()\n\
          a()\n\
          (a(), b())\n",
        &[],
        b"(3, 1)\n",
    );
    // Reference pin: vm_matches_evaluator_on_top_level_mut_closure.
    // The closure mutates the top-level binding; the change is visible
    // after the call.
    assert_runs(
        b"let a = 123\n\
          func b() {\n\
          \ta = a + 1\n\
          \ta\n\
          }\n\
          b()\n\
          a\n",
        &[],
        b"124\n",
    );
}

#[test]
fn run_executes_local_functions_that_capture() {
    // Reference pin: vm_matches_evaluator_on_recursive_closure_capturing_a_local.
    assert_runs(
        b"func outer() -> Int {\n\
          \tlet step = 2\n\
          \tfunc down(n: Int) -> Int { if n > 0 { down(n: n - step) + 1 } else { 0 } }\n\
          \tdown(n: 6)\n\
          }\n\
          outer()\n\
          ",
        &[],
        b"3\n",
    );
    // Reference pins: local self- and mutual recursion keep working.
    assert_runs(
        b"func outer() -> Int {\n\
          \tfunc fact(n: Int) -> Int { if n > 1 { n * fact(n: n - 1) } else { 1 } }\n\
          \tfact(n: 5)\n\
          }\n\
          outer()\n\
          ",
        &[],
        b"120\n",
    );
    assert_runs(
        b"func outer() -> Int {\n\
          \tfunc a(n: Int) -> Int { if n > 0 { b(n: n - 1) } else { 0 } }\n\
          \tfunc b(n: Int) -> Int { a(n: n) + 1 }\n\
          \ta(n: 4)\n\
          }\n\
          outer()\n\
          ",
        &[],
        b"4\n",
    );
    // Reference pin: vm_matches_evaluator_on_capture_of_rebound_binding.
    // A later rebinding does not retroactively change the capture.
    assert_runs(
        b"func f() -> Int {\n\
          \tlet x = 1\n\
          \tlet g = func() -> Int { x }\n\
          \tlet x = 2\n\
          \tg() + x\n\
          }\n\
          f()\n",
        &[],
        b"3\n",
    );
}

#[test]
fn run_enforces_capture_list_modes() {
    // `[copy a]` captures a copy; the original is untouched. (Capture
    // lists govern frame locals, so the reference's flow tests — and
    // these — sit inside a function body.)
    assert_runs(
        b"func run() -> Int {\n\
          \tlet a = 40\n\
          \tlet f = func [copy a]() -> Int { a }\n\
          \tf() + 2\n\
          }\n\
          run()\n",
        &[],
        b"42\n",
    );
    // Reference rule: `[consuming s]` moves the owner; later use fails.
    let output = run_source(
        b"func run() -> Int {\n\
          \tlet s = (1, 2)\n\
          \tlet f = func [consuming s]() -> Int { s.0 }\n\
          \tf() + s.1\n\
          }\n\
          run()\n",
        &[],
    );
    assert!(!output.status.success());
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(stderr.contains("moved"), "{stderr}");
    // Reference rule: with an explicit list, every free variable must
    // be listed.
    let output = run_source(
        b"func run() -> Int {\n\
          \tlet a = 1\n\
          \tlet b = 2\n\
          \tlet f = func [copy a]() -> Int { a + b }\n\
          \tf()\n\
          }\n\
          run()\n",
        &[],
    );
    assert!(!output.status.success());
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(stderr.contains("capture"), "{stderr}");
}

#[test]
fn run_specializes_recursive_inferred_generics() {
    // An unannotated function generalizes to a scheme; its recursive
    // call is monomorphic (typing records no instantiation for it), so
    // the callee's parameters specialize through the enclosing
    // instance's own bindings (the static-dictionary rule of Griesemer
    // et al., OOPSLA 2022).
    assert_runs(
        b"func fact(n) {\n\
          \tif n <= 1 { return 1 }\n\
          \treturn n * fact(n - 1)\n\
          }\n\
          print(fact(5))\n\
          ",
        &[],
        b"120\n",
    );
    // Two instantiations of a non-recursive inferred generic keep
    // working alongside the recursive case.
    assert_runs(
        b"func double(x) { x + x }\n\
          print(double(20) + double(1))\n\
          ",
        &[],
        b"42\n",
    );
}

#[test]
fn run_executes_compound_if_conditions_left_to_right() {
    assert_runs(
        b"enum MaybeInt {\n\
          \tcase some(Int)\n\
          \tcase none\n\
          }\n\
          func source(consume value: MaybeInt) -> MaybeInt {\n\
          \tprint(1)\n\
          \tvalue\n\
          }\n\
          func allowed(value: Int) -> Bool {\n\
          \tprint(2)\n\
          \ttrue\n\
          }\n\
          func inspect(consume value: MaybeInt) {\n\
          \tif let .some(x) = source(value: value), allowed(value: x) {\n\
          \t\tprint(x)\n\
          \t} else {\n\
          \t\tprint(0)\n\
          \t}\n\
          }\n\
          inspect(value: MaybeInt.some(7))\n\
          inspect(value: MaybeInt.none)\n\
          ",
        &[],
        b"1\n2\n7\n1\n0\n",
    );
}

#[test]
fn run_matches_enum_variants_with_payloads() {
    let source = b"enum Op {\n\
        \tcase add(Int, Int)\n\
        \tcase neg(Int)\n\
        }\n\
        func eval(op: Op) -> Int {\n\
        \tmatch op {\n\
        \t\t.add(a, b) -> a + b,\n\
        \t\t.neg(a) -> 0 - a\n\
        \t}\n\
        }\n\
        eval(op: Op.add(30, 12)) + eval(op: Op.neg(5))\n";
    assert_runs(source, &[], b"37\n");
}

#[test]
fn run_matches_or_and_literal_patterns() {
    let source = b"func kind(x: Int) -> Int {\n\
        \tmatch x {\n\
        \t\t1 | 2 -> 10,\n\
        \t\t3 -> 20,\n\
        \t\t_ -> 0\n\
        \t}\n\
        }\n\
        kind(x: 1) + kind(x: 2) + kind(x: 3) + kind(x: 9)\n";
    assert_runs(source, &[], b"40\n");
}

#[test]
fn run_renders_an_enum_result_in_talk_syntax() {
    assert_runs(
        b"enum Color {\n\tcase red\n\tcase green\n}\nColor.green\n",
        &[],
        b"Color.green\n",
    );
}

#[test]
fn run_constructs_and_projects_structs() {
    let source = b"struct Point {\n\
        \tlet x: Int\n\
        \tlet y: Int\n\
        \tinit(x: Int, y: Int) {\n\
        \t\tself.x = x\n\
        \t\tself.y = y\n\
        \t\tself\n\
        \t}\n\
        }\n\
        let p = Point(x: 1, y: 2)\n\
        p.x + p.y\n";
    assert_runs(source, &[], b"3\n");
}

#[test]
fn run_reads_string_byte_count() {
    assert_runs(b"let s = \"hey\"\ns.byte_count\n", &[], b"3\n");
}

#[test]
fn run_concatenates_strings_without_leaking() {
    assert_runs(b"let s = \"x\" + \"y\"\ns.byte_count\n", &[], b"2\n");
}

#[test]
fn run_clones_copy_and_cheap_clone_values() {
    let source = b"struct BoxedText {\n\
        \tlet value: String\n\
        }\n\
        extend BoxedText: CheapClone {}\n\
        let original = BoxedText(value: \"hello\")\n\
        let duplicate = original.clone()\n\
        let source = \"world\"\n\
        let cloned = source.clone()\n\
        let number = 42\n\
        let copied = number.clone()\n\
        duplicate.value.byte_count + cloned.byte_count + number + copied\n";
    assert_runs(source, &[], b"94\n");
}

#[test]
fn run_prints_scalars_and_strings() {
    assert_runs(b"print(42)\nprint(\"hey\")\n", &[], b"42\nhey\n");
}

/// The one corpus runner (gates G2, G5, G6): run `<programs>/<name>.tlk`
/// through the real CLI and compare against `<expected>/<name>.stdout`.
/// Success, frozen stdout (tolerating only a trailing-newline
/// difference in the pin file), and empty stderr — which is also the
/// allocation-balance check, since leaks report there.
fn assert_corpus_program(programs: &str, expected_dir: &str, name: &str) {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"));
    let expected = std::fs::read_to_string(root.join(format!("{expected_dir}/{name}.stdout")))
        .expect("read frozen expected stdout");
    let output = Command::new(env!("CARGO_BIN_EXE_talk"))
        .arg("run")
        .arg(root.join(format!("{programs}/{name}.tlk")))
        .output()
        .expect("run corpus program");
    assert!(
        output.status.success(),
        "{name} failed:\n{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert_eq!(
        stdout.trim_end_matches('\n'),
        expected.trim_end_matches('\n'),
        "{name} diverged from frozen stdout\nstderr:\n{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(output.stderr.is_empty(), "{name} stderr not empty");
}

fn assert_parity_program(name: &str) {
    assert_corpus_program("tests/programs", "tests/parity/programs", name);
}

/// The benchmark corpus (bench/): one program per workload archetype
/// from the profiling passes, each with a pinned deterministic output.
/// These exist to be measured and to have their IR and bytecode read —
/// keeping them green keeps the analysis surface stable.
#[test]
fn bench_corpus_runs() {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("bench");
    let mut entries: Vec<_> = std::fs::read_dir(&root)
        .expect("bench directory")
        .filter_map(Result::ok)
        .map(|entry| entry.path())
        .filter(|path| path.extension().is_some_and(|ext| ext == "tlk"))
        .collect();
    entries.sort();
    assert!(
        entries.len() >= 8,
        "bench corpus shrank: {} programs",
        entries.len()
    );
    for_each_corpus_case(&entries, |program| {
        let name = program
            .file_stem()
            .and_then(|stem| stem.to_str())
            .expect("program name")
            .to_string();
        let expected = std::fs::read_to_string(root.join(format!("expected/{name}.stdout")))
            .expect("pinned stdout");
        let output = Command::new(env!("CARGO_BIN_EXE_talk"))
            .arg("run")
            .arg(program)
            .output()
            .expect("run benchmark");
        assert!(
            output.status.success(),
            "{name} failed:\n{}",
            String::from_utf8_lossy(&output.stderr)
        );
        assert_eq!(
            String::from_utf8_lossy(&output.stdout).trim_end_matches('\n'),
            expected.trim_end_matches('\n'),
            "{name} diverged from its pinned output"
        );
        assert!(
            output.stderr.is_empty(),
            "{name} stderr not empty (leak?):\n{}",
            String::from_utf8_lossy(&output.stderr)
        );
    });
}

/// Bytecode-shape assertions over the benchmark corpus: assignments
/// fuse into their producing instruction (no move-back per loop
/// iteration), parameters donate their registers to dying copies, a
/// match reads its scrutinee's tag once, and no jump targets the next
/// pc.
#[test]
fn bench_bytecode_is_tight() {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("bench");
    let render = |name: &str| -> String {
        let output = Command::new(env!("CARGO_BIN_EXE_talk"))
            .arg("bytecode")
            .arg(root.join(format!("{name}.tlk")))
            .output()
            .expect("render bytecode");
        assert!(
            output.status.success(),
            "{name}: {}",
            String::from_utf8_lossy(&output.stderr)
        );
        String::from_utf8_lossy(&output.stdout).into_owned()
    };
    let chunk = |rendered: &str, fn_name: &str| -> String {
        rendered
            .split("chunk ")
            .find(|section| {
                section
                    .lines()
                    .next()
                    .is_some_and(|head| head.contains(&format!(": {fn_name} ")))
            })
            .unwrap_or_else(|| panic!("chunk {fn_name} in render"))
            .to_string()
    };

    // Finding 2: loop-carried assignments fuse into their producers.
    let arith = render("arith");
    let bench = chunk(&arith, "bench");
    assert!(
        !bench.contains(" move "),
        "arith loop still copies assignments back:\n{bench}"
    );

    // Finding 3: a dying parameter donates its register, so fib's base
    // case returns the parameter's register directly.
    let calls = render("calls");
    let fib = chunk(&calls, "fib");
    assert!(
        !fib.contains(" move "),
        "fib still moves its parameter into the join register:\n{fib}"
    );

    // Finding 1: one tag read per match, however many arms.
    let dispatch = render("dispatch");
    let area = chunk(&dispatch, "area");
    let tag_reads = area.matches("get_tag").count();
    assert_eq!(
        tag_reads, 1,
        "match re-reads the scrutinee tag per arm:\n{area}"
    );

    // Finding 5: no jump ever targets the immediately following pc,
    // in any chunk of any benchmark.
    for name in [
        "arith", "arrays", "calls", "dispatch", "drops", "effects", "fields", "strings",
    ] {
        let rendered = render(name);
        for line in rendered.lines() {
            let trimmed = line.trim_start();
            let Some((pc, rest)) = trimmed.split_once(": ") else {
                continue;
            };
            let Ok(pc) = pc.parse::<usize>() else {
                continue;
            };
            if let Some(target) = rest.strip_prefix("jump ")
                && let Ok(target) = target.trim().parse::<usize>()
            {
                assert_ne!(
                    target,
                    pc + 1,
                    "{name}: jump to the next pc survives lowering: {line}"
                );
            }
        }
    }
}

/// A memberwise construction builds its record directly from the
/// arguments: no blank record, no call into the synthesized init, no
/// per-field SetField (whose copy-on-write always missed, since the
/// blank was aliased across the caller and init frames).
#[test]
fn memberwise_constructions_build_directly() {
    let unique = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .expect("system clock after epoch")
        .as_nanos();
    let dir = std::env::temp_dir().join(format!("talk-cons-{}-{unique}", std::process::id()));
    std::fs::create_dir_all(&dir).expect("create fixture dir");
    let source = "struct Point {\n\
                  \tlet x: Int\n\
                  \tlet y: Int\n\
                  }\n\
                  func make(n: Int) -> Int {\n\
                  \tlet p = Point(x: n, y: n + 1)\n\
                  \tp.x + p.y\n\
                  }\n\
                  print(make(n: 20))\n\
                  ";
    let file = dir.join("cons.tlk");
    std::fs::write(&file, source).expect("write fixture");

    let mir = Command::new(env!("CARGO_BIN_EXE_talk"))
        .arg("mir")
        .arg(&file)
        .output()
        .expect("render mir");
    assert!(
        mir.status.success(),
        "{}",
        String::from_utf8_lossy(&mir.stderr)
    );
    let rendered = String::from_utf8_lossy(&mir.stdout);
    let make = rendered
        .split("\nfn")
        .find(|section| section.contains(" make "))
        .expect("make in render");
    assert!(
        !make.contains("Const(Unit)"),
        "construction still builds a blank record:\n{make}"
    );
    assert!(
        make.contains("Aggregate {"),
        "construction should build the record directly:\n{make}"
    );

    let run = Command::new(env!("CARGO_BIN_EXE_talk"))
        .arg("run")
        .arg(&file)
        .output()
        .expect("run fixture");
    assert!(
        run.status.success(),
        "{}",
        String::from_utf8_lossy(&run.stderr)
    );
    assert_eq!(String::from_utf8_lossy(&run.stdout), "41\n");
    assert!(
        run.stderr.is_empty(),
        "leak or diagnostic:\n{}",
        String::from_utf8_lossy(&run.stderr)
    );
    std::fs::remove_dir_all(dir).expect("remove fixture dir");
}

/// Register-or-constant operands (Lua 5's RK design — Ierusalimschy,
/// de Figueiredo & Celes, J.UCS 2005): arithmetic and argument
/// operands address the constant pool directly, so a constant used
/// as an operand costs no materializing instruction.
#[test]
fn constant_operands_read_the_pool_directly() {
    let unique = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .expect("system clock after epoch")
        .as_nanos();
    let dir = std::env::temp_dir().join(format!("talk-rk-{}-{unique}", std::process::id()));
    std::fs::create_dir_all(&dir).expect("create fixture dir");
    let source =
        "func bump(n: Int) -> Int {\n\tn + 1\n}\nlet increment = bump\nprint(increment(41))\n";
    let file = dir.join("rk.tlk");
    std::fs::write(&file, source).expect("write fixture");

    let bytecode = Command::new(env!("CARGO_BIN_EXE_talk"))
        .arg("bytecode")
        .arg(&file)
        .output()
        .expect("render bytecode");
    assert!(
        bytecode.status.success(),
        "{}",
        String::from_utf8_lossy(&bytecode.stderr)
    );
    let rendered = String::from_utf8_lossy(&bytecode.stdout);
    let bump = rendered
        .split("chunk ")
        .find(|section| {
            section
                .lines()
                .next()
                .is_some_and(|line| line.contains(": bump ("))
        })
        .expect("bump chunk in render");
    assert!(
        !bump.contains("const r"),
        "constant operand still materializes:\n{bump}"
    );
    assert!(
        bump.lines()
            .any(|line| line.contains("add") && line.contains("k[")),
        "add should read the constant pool directly:\n{bump}"
    );

    let run = Command::new(env!("CARGO_BIN_EXE_talk"))
        .arg("run")
        .arg(&file)
        .output()
        .expect("run fixture");
    assert!(
        run.status.success(),
        "{}",
        String::from_utf8_lossy(&run.stderr)
    );
    assert_eq!(String::from_utf8_lossy(&run.stdout), "42\n");
    std::fs::remove_dir_all(dir).expect("remove fixture dir");
}

/// Wave 11a: binding a name to an owned rvalue temporary aliases the
/// temporary — a `let` is a name for a value, not a copy of one (the
/// straight-line half of SSA construction — Braun et al., CC 2013).
#[test]
fn owned_bindings_alias_their_rvalue_temporaries() {
    let unique = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .expect("system clock after epoch")
        .as_nanos();
    let dir = std::env::temp_dir().join(format!("talk-alias-{}-{unique}", std::process::id()));
    std::fs::create_dir_all(&dir).expect("create fixture dir");
    let source = "func chain() -> String {\n\
                  \tlet s = \"x\" + \"y\"\n\
                  \tlet t = s + \"z\"\n\
                  \tt\n\
                  }\n\
                  print(chain())\n";
    let file = dir.join("alias.tlk");
    std::fs::write(&file, source).expect("write fixture");

    let mir = Command::new(env!("CARGO_BIN_EXE_talk"))
        .arg("mir")
        .arg(&file)
        .output()
        .expect("render mir");
    assert!(
        mir.status.success(),
        "{}",
        String::from_utf8_lossy(&mir.stderr)
    );
    let rendered = String::from_utf8_lossy(&mir.stdout);
    let chain = rendered
        .split("\nfn")
        .find(|section| section.contains(" chain "))
        .expect("chain in render");
    let copies = chain.matches("Copy").count();
    assert_eq!(
        copies, 0,
        "expected no copies in a let chain, found {copies}:\n{chain}"
    );

    let run = Command::new(env!("CARGO_BIN_EXE_talk"))
        .arg("run")
        .arg(&file)
        .output()
        .expect("run fixture");
    assert!(
        run.status.success(),
        "{}",
        String::from_utf8_lossy(&run.stderr)
    );
    assert_eq!(String::from_utf8_lossy(&run.stdout), "xyz\n");
    assert!(
        run.stderr.is_empty(),
        "leak or diagnostic:\n{}",
        String::from_utf8_lossy(&run.stderr)
    );
    std::fs::remove_dir_all(dir).expect("remove fixture dir");
}

/// Wave 9c: a function's unwind cleanup is one chain of blocks —
/// each dropping one live value, jumping outward, ending in a single
/// `UnwindRet` — however many call sites need cleanup. Per-call-site
/// synthesis emitted one full cleanup block per call.
#[test]
fn unwind_cleanup_is_one_chain_per_function() {
    let unique = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .expect("system clock after epoch")
        .as_nanos();
    let dir = std::env::temp_dir().join(format!("talk-chain-{}-{unique}", std::process::id()));
    std::fs::create_dir_all(&dir).expect("create fixture dir");
    // Two owned strings stay live across three calls: every call needs
    // an unwind target, but the live set never changes, so one chain
    // serves all three.
    let source = "func chatty() -> Int {\n\
                  \tlet s = \"a\" + \"b\"\n\
                  \tlet x = \"c\" + \"d\"\n\
                  \tlet n1 = s.byte_count\n\
                  \tlet n2 = x.byte_count\n\
                  \tlet n3 = s.byte_count\n\
                  \tn1 + n2 + n3\n\
                  }\n\
                  print(chatty())\n";
    let file = dir.join("chain.tlk");
    std::fs::write(&file, source).expect("write fixture");

    let mir = Command::new(env!("CARGO_BIN_EXE_talk"))
        .arg("mir")
        .arg(&file)
        .output()
        .expect("render mir");
    assert!(
        mir.status.success(),
        "{}",
        String::from_utf8_lossy(&mir.stderr)
    );
    let rendered = String::from_utf8_lossy(&mir.stdout);
    let chatty = rendered
        .split("\nfn")
        .find(|section| section.contains(" chatty "))
        .expect("chatty in render");
    let unwind_rets = chatty.matches("UnwindRet").count();
    assert_eq!(
        unwind_rets, 1,
        "expected one cleanup chain, found {unwind_rets} UnwindRet blocks:\n{chatty}"
    );

    let run = Command::new(env!("CARGO_BIN_EXE_talk"))
        .arg("run")
        .arg(&file)
        .output()
        .expect("run fixture");
    assert!(
        run.status.success(),
        "{}",
        String::from_utf8_lossy(&run.stderr)
    );
    assert_eq!(String::from_utf8_lossy(&run.stdout), "6\n");
    assert!(
        run.stderr.is_empty(),
        "leak or diagnostic:\n{}",
        String::from_utf8_lossy(&run.stderr)
    );
    std::fs::remove_dir_all(dir).expect("remove fixture dir");
}

/// Wave 9b: a type's structural teardown is emitted once as a shared
/// drop function and called at each drop site, not macro-expanded per
/// site (the per-type `dec` shape — Ullrich & de Moura, IFL 2019).
#[test]
fn structural_drops_share_one_teardown_body() {
    let unique = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .expect("system clock after epoch")
        .as_nanos();
    let dir = std::env::temp_dir().join(format!("talk-drop-glue-{}-{unique}", std::process::id()));
    std::fs::create_dir_all(&dir).expect("create fixture dir");
    // A struct with two owned fields, dropped at scope exit in two
    // different functions; and an enum likewise.
    let source = "struct Pair {\n\
                  \tlet a: String\n\
                  \tlet b: String\n\
                  }\n\
                  enum Wrap {\n\
                  \tcase one(String)\n\
                  \tcase two(String)\n\
                  }\n\
                  func first() -> Int {\n\
                  \tlet p = Pair(a: \"x\" + \"y\", b: \"z\" + \"w\")\n\
                  \tlet w = Wrap.one(\"q\" + \"r\")\n\
                  \t1\n\
                  }\n\
                  func second() -> Int {\n\
                  \tlet p = Pair(a: \"c\" + \"d\", b: \"e\" + \"f\")\n\
                  \tlet w = Wrap.two(\"g\" + \"h\")\n\
                  \t2\n\
                  }\n\
                  print(first() + second())\n";
    let file = dir.join("shared_drop.tlk");
    std::fs::write(&file, source).expect("write fixture");

    let mir = Command::new(env!("CARGO_BIN_EXE_talk"))
        .arg("mir")
        .arg(&file)
        .output()
        .expect("render mir");
    assert!(
        mir.status.success(),
        "{}",
        String::from_utf8_lossy(&mir.stderr)
    );
    let rendered = String::from_utf8_lossy(&mir.stdout);
    let shared_bodies = rendered
        .lines()
        .filter(|line| line.contains(" shared_drop "))
        .count();
    // One body for Pair, one for Wrap - and exactly one each, however
    // many sites drop them. Unreferenced core glue does not survive
    // whole-program function DCE.
    assert_eq!(
        shared_bodies, 2,
        "expected one shared drop body per type, found {shared_bodies}:\n{rendered}"
    );

    let run = Command::new(env!("CARGO_BIN_EXE_talk"))
        .arg("run")
        .arg(&file)
        .output()
        .expect("run fixture");
    assert!(
        run.status.success(),
        "{}",
        String::from_utf8_lossy(&run.stderr)
    );
    assert_eq!(String::from_utf8_lossy(&run.stdout), "3\n");
    assert!(
        run.stderr.is_empty(),
        "leak or diagnostic:\n{}",
        String::from_utf8_lossy(&run.stderr)
    );
    std::fs::remove_dir_all(dir).expect("remove fixture dir");
}

/// Check every pinned program in a corpus directory (each
/// `expected/*.stdout` names a sibling `.tlk`), skipping the
/// known-failing burn-down list. `minimum` guards against the corpus
/// silently shrinking.
fn assert_corpus_dir(programs: &str, known_failing: &[&str], minimum: usize) {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join(programs);
    let expected_dir = format!("{programs}/expected");
    let mut names: Vec<_> = std::fs::read_dir(root.join("expected"))
        .expect("list expected outputs")
        .map(|entry| {
            entry
                .expect("read entry")
                .path()
                .file_stem()
                .and_then(|stem| stem.to_str())
                .expect("expected-output name")
                .to_string()
        })
        .filter(|name| !known_failing.contains(&name.as_str()))
        .collect();
    names.sort();
    assert!(
        names.len() >= minimum,
        "corpus shrank: only {} checked",
        names.len()
    );
    for_each_corpus_case(&names, |name| {
        assert_corpus_program(programs, &expected_dir, name);
    });
}

/// The reference's user-effects behavior pins (G6 effects cluster),
/// ported from its VM test suite as corpus programs: deep handlers,
/// conditional resume/abort, tail/statement/expression performs,
/// handler locals, effectful closures, lexical capability capture.
#[test]
fn reference_effects_cluster_matches_frozen_stdout() {
    assert_corpus_dir("tests/reference/effects", &[], 18);
}

/// G6 strings/UTF-8 cluster: string building, views, slices, find,
/// UTF-8 decode boundary cases (U+FFFD maximal subparts), grapheme
/// category lookups.
#[test]
fn reference_strings_cluster_matches_frozen_stdout() {
    assert_corpus_dir("tests/reference/strings", &[], 11);
}

/// G6 collections/iterators cluster: arrays, adapters, and the
/// borrow/consume/mut iteration modes (F6 verification).
#[test]
fn reference_collections_cluster_matches_frozen_stdout() {
    assert_corpus_dir("tests/reference/collections", &[], 35);
}

/// G6 drop-once/leak-balance cluster: the reference's ownership
/// regression matrix (every program also runs under this CLI's strict
/// allocation-balance check).
#[test]
fn reference_drops_cluster_matches_frozen_stdout() {
    assert_corpus_dir("tests/reference/drops", &[], 15);
}

/// Check a flow-rule corpus directory: `expected/<name>.stdout` names a
/// program that must run clean (and match, when the pin is non-empty);
/// `expected/<name>.error` names a program that must FAIL with a
/// diagnostic containing the pinned fragment (case-insensitive).
fn assert_flow_corpus(
    programs: &str,
    stricter: &[&str],
    pending_rejection: &[&str],
    minimum: usize,
) {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join(programs);
    let mut expected_paths: Vec<_> = std::fs::read_dir(root.join("expected"))
        .expect("list expected outputs")
        .map(|entry| entry.expect("read entry").path())
        .collect();
    expected_paths.sort();
    assert!(
        expected_paths.len() >= minimum,
        "flow corpus shrank: only {} checked",
        expected_paths.len()
    );
    for_each_corpus_case(&expected_paths, |expected_path| {
        let name = expected_path
            .file_stem()
            .and_then(|stem| stem.to_str())
            .expect("expected-output name")
            .to_string();
        let is_error = expected_path.extension().is_some_and(|ext| ext == "error");
        let output = Command::new(env!("CARGO_BIN_EXE_talk"))
            .arg("run")
            .arg(root.join(format!("{name}.tlk")))
            // The reference's flow pass checked every declaration;
            // check mode compiles uncalled bodies too.
            .env("TALK_CHECK_ALL", "1")
            .output()
            .expect("run flow program");
        let stderr = String::from_utf8_lossy(&output.stderr);
        if is_error {
            if pending_rejection.contains(&name.as_str()) {
                // Adjudicated must-reject whose enforcement has not
                // landed yet (docs/ownership.md). The
                // assert keeps the list current: when the enforcing
                // wave lands, this fires and the case must be promoted
                // to an enforced rejection.
                assert!(
                    output.status.success(),
                    "{name}: now rejects — remove it from PENDING_REJECTION so the pin is enforced"
                );
                return;
            }
            let fragment = std::fs::read_to_string(&expected_path)
                .expect("read expected error")
                .trim()
                .to_lowercase();
            assert!(
                !output.status.success(),
                "{name}: expected a rejection containing `{fragment}`, but the program ran"
            );
            assert!(
                stderr.to_lowercase().contains(&fragment),
                "{name}: rejection did not mention `{fragment}`:\n{stderr}"
            );
        } else {
            if stricter.contains(&name.as_str()) {
                // The reference ran this program; we still reject or
                // trap on it (fail-closed, safe). The assert keeps the
                // list current: when the enabling wave lands, this
                // fires and the case's output pin must be enforced.
                assert!(
                    !output.status.success(),
                    "{name}: now runs — remove it from KNOWN_STRICTER so its output pin is enforced"
                );
                return;
            }
            let expected = std::fs::read_to_string(&expected_path).expect("read expected stdout");
            let empty_pin = expected.trim_end_matches('\n').is_empty();
            // A declaration-only accept has no entry to run; compiling
            // clean is the check (demand-driven compilation checks what
            // runs — an argued divergence from the reference's
            // whole-program flow pass).
            if empty_pin && stderr.contains("nothing to run") {
                return;
            }
            assert!(output.status.success(), "{name} failed:\n{stderr}");
            if !empty_pin {
                let stdout = String::from_utf8_lossy(&output.stdout);
                assert_eq!(
                    stdout.trim_end_matches('\n'),
                    expected.trim_end_matches('\n'),
                    "{name} diverged\nstderr:\n{stderr}"
                );
            }
            assert!(output.stderr.is_empty(), "{name} stderr not empty");
        }
    });
}

/// The flow/ownership rule corpus, adjudicated under the implicit-
/// sharing decision (docs/ownership.md): reject pins are
/// the four surviving error categories and can never be skipped —
/// every one must exit nonzero with its fragment. Accept pins must
/// compile and run clean. Two self-cleaning lists park divergences:
/// KNOWN_STRICTER holds accept cases we still reject or trap on
/// (fail-closed; each entry asserts nonzero exit), PENDING_REJECTION
/// holds adjudicated rejects whose enforcing wave has not landed
/// (each entry asserts it does not reject yet). Both lists may only
/// shrink as waves B–F land.
#[test]
fn reference_flow_corpus_holds() {
    const KNOWN_STRICTER: &[&str] = &[
        "borrowed_generic_payload_requires_copy_or_cheap_clone_bound",
        "generic_heap_extraction_rejects_non_cheap_owned_instantiation",
    ];
    const PENDING_REJECTION: &[&str] = &[];
    assert_flow_corpus(
        "tests/reference/flow",
        KNOWN_STRICTER,
        PENDING_REJECTION,
        100,
    );
}

#[test]
fn parity_tuple_access() {
    assert_parity_program("tuple_access");
}

#[test]
fn parity_propagate_in_let() {
    assert_parity_program("propagate_in_let");
}

#[test]
fn parity_cross_enum_leading_dot() {
    assert_parity_program("cross_enum_leading_dot");
}

#[test]
fn parity_array_literal_borrow_donation() {
    assert_parity_program("array_literal_borrow_donation");
}

#[test]
fn parity_conditional_moves() {
    assert_parity_program("conditional_moves");
}

#[test]
fn parity_clone_method() {
    assert_parity_program("clone_method");
}

#[test]
fn parity_string_building() {
    assert_parity_program("string_building");
}

#[test]
fn parity_string_patterns() {
    assert_parity_program("string_patterns");
}

#[test]
fn parity_graphemes() {
    assert_parity_program("graphemes");
}

#[test]
fn parity_iterate_and_match() {
    assert_parity_program("iterate_and_match");
}

#[test]
fn test_command_resolves_the_package_root_from_a_path_argument() {
    // `talk test <path>` run from outside the package must still anchor
    // `package::` imports at that package's source root, exactly as
    // running `talk test` from inside it would.
    let unique = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .expect("system clock after epoch")
        .as_nanos();
    let dir = std::env::temp_dir().join(format!("talk-pkg-path-{}-{unique}", std::process::id()));
    let root = dir.join("root");
    std::fs::create_dir_all(root.join("src")).expect("root src");
    std::fs::create_dir_all(root.join("tests")).expect("root tests");
    std::fs::write(
        root.join("package.tlk"),
        "Package(name: \"path-arg\", version: \"0.1.0\", builds: [.lib(from: \"src/lib.tlk\")], dependencies: [])",
    )
    .expect("root manifest");
    std::fs::write(
        root.join("src/lib.tlk"),
        "pub func answer() -> Int {\n\t42\n}\n",
    )
    .expect("library source");
    std::fs::write(
        root.join("src/lib.test.tlk"),
        "use package::lib::{ answer }\n\ntest(\"package import\") {\n\tassert(answer() == 42)\n}\n",
    )
    .expect("test source");
    // A second suite under tests/ makes the suites span two directories:
    // `package::` must anchor at src/, not at any inferred common
    // ancestor of the test files.
    std::fs::write(
        root.join("tests/extra.test.tlk"),
        "use package::lib::{ answer }\n\ntest(\"package import from tests\") {\n\tassert(answer() == 42)\n}\n",
    )
    .expect("tests suite source");

    let install = Command::new(env!("CARGO_BIN_EXE_talk"))
        .args(["install", "--offline"])
        .current_dir(&root)
        .output()
        .expect("install");
    assert!(
        install.status.success(),
        "{}",
        String::from_utf8_lossy(&install.stderr)
    );

    let test = Command::new(env!("CARGO_BIN_EXE_talk"))
        .arg("test")
        .arg(&root)
        .current_dir(&dir)
        .output()
        .expect("package test by path");
    assert!(
        test.status.success(),
        "{}",
        String::from_utf8_lossy(&test.stderr)
    );
    assert!(String::from_utf8_lossy(&test.stdout).contains("2 tests passed"));

    let by_file = Command::new(env!("CARGO_BIN_EXE_talk"))
        .arg("test")
        .arg(root.join("src/lib.test.tlk"))
        .current_dir(&dir)
        .output()
        .expect("package test by file path");
    assert!(
        by_file.status.success(),
        "{}",
        String::from_utf8_lossy(&by_file.stderr)
    );
    assert!(String::from_utf8_lossy(&by_file.stdout).contains("1 tests passed"));

    std::fs::remove_dir_all(dir).expect("remove package fixture");
}

#[test]
fn package_run_and_test_use_the_locked_graph() {
    let unique = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .expect("system clock after epoch")
        .as_nanos();
    let dir = std::env::temp_dir().join(format!("talk-pkg-{}-{unique}", std::process::id()));
    let dependency = dir.join("dependency");
    let root = dir.join("root");
    std::fs::create_dir_all(dependency.join("src")).expect("dependency src");
    std::fs::create_dir_all(root.join("src")).expect("root src");
    std::fs::create_dir_all(root.join("tests")).expect("root tests");
    std::fs::write(
        dependency.join("package.tlk"),
        "Package(name: \"cli-dependency\", version: \"0.1.0\", builds: [.lib(from: \"src/lib.tlk\")], dependencies: [])",
    )
    .expect("dependency manifest");
    std::fs::write(
        dependency.join("src/lib.tlk"),
        "pub func answer_for(n: Int) -> Int {\n\tn + 2\n}\n",
    )
    .expect("dependency source");
    std::fs::write(
        root.join("package.tlk"),
        "Package(name: \"cli-root\", version: \"0.1.0\", builds: [.bin(named: \"app\", from: \"src/main.tlk\")], dependencies: [.path(package: \"cli-dependency\", path: \"../dependency\")])",
    )
    .expect("root manifest");
    std::fs::write(
        root.join("src/main.tlk"),
        "use cli_dependency::{ answer_for }\nprint(answer_for(n: 40))\n",
    )
    .expect("root source");
    std::fs::write(
        root.join("tests/dep.test.tlk"),
        "use cli_dependency::{ answer_for }\n\ntest(\"dependency math\") {\n\tassert(answer_for(n: 40) == 42)\n}\n",
    )
    .expect("test source");

    let install = Command::new(env!("CARGO_BIN_EXE_talk"))
        .args(["install", "--offline"])
        .current_dir(&root)
        .output()
        .expect("install");
    assert!(
        install.status.success(),
        "{}",
        String::from_utf8_lossy(&install.stderr)
    );

    let run = Command::new(env!("CARGO_BIN_EXE_talk"))
        .args(["run", "--offline", "--bin", "app"])
        .current_dir(&root)
        .output()
        .expect("package run");
    assert!(
        run.status.success(),
        "{}",
        String::from_utf8_lossy(&run.stderr)
    );
    assert_eq!(run.stdout, b"42\n");

    let test = Command::new(env!("CARGO_BIN_EXE_talk"))
        .arg("test")
        .current_dir(&root)
        .output()
        .expect("package test");
    assert!(
        test.status.success(),
        "{}",
        String::from_utf8_lossy(&test.stderr)
    );
    assert!(String::from_utf8_lossy(&test.stdout).contains("1 tests passed"));

    std::fs::remove_dir_all(dir).expect("remove package fixture");
}

#[test]
fn check_command_checks_the_package_workspace() {
    // Bare `talk check` inside a package checks the manifest-scoped
    // sources compiled against the locked dependency graph, walking up
    // from any subdirectory; `talk check -` keeps reading stdin.
    let unique = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .expect("system clock after epoch")
        .as_nanos();
    let dir = std::env::temp_dir().join(format!("talk-pkg-check-{}-{unique}", std::process::id()));
    let dependency = dir.join("dependency");
    let root = dir.join("root");
    std::fs::create_dir_all(dependency.join("src")).expect("dependency src");
    std::fs::create_dir_all(root.join("src")).expect("root src");
    std::fs::write(
        dependency.join("package.tlk"),
        "Package(name: \"check-dependency\", version: \"0.1.0\", builds: [.lib(from: \"src/lib.tlk\")], dependencies: [])",
    )
    .expect("dependency manifest");
    std::fs::write(
        dependency.join("src/lib.tlk"),
        "pub func answer_for(n: Int) -> Int {\n\tn + 2\n}\n",
    )
    .expect("dependency source");
    std::fs::write(
        root.join("package.tlk"),
        "Package(name: \"check-root\", version: \"0.1.0\", builds: [.bin(named: \"app\", from: \"src/main.tlk\")], dependencies: [.path(package: \"check-dependency\", path: \"../dependency\")])",
    )
    .expect("root manifest");
    std::fs::write(
        root.join("src/main.tlk"),
        "use check_dependency::{ answer_for }\nuse package::util::{ double }\n\nprint(answer_for(n: double(n: 20)))\n",
    )
    .expect("root source");
    std::fs::write(
        root.join("src/util.tlk"),
        "pub func double(n: Int) -> Int {\n\tn * 2\n}\n",
    )
    .expect("util source");
    // Test suites join the workspace too: the harness must compile in.
    std::fs::write(
        root.join("src/util.test.tlk"),
        "use package::util::{ double }\n\ntest(\"double\") {\n\tassert(double(n: 21) == 42)\n}\n",
    )
    .expect("test source");

    let talk = || {
        let mut command = Command::new(env!("CARGO_BIN_EXE_talk"));
        command.arg("check");
        command
    };

    // The lockfile gates package mode, exactly like `talk run`.
    let missing_lock = talk().current_dir(&root).output().expect("check");
    assert!(!missing_lock.status.success());
    assert!(
        String::from_utf8_lossy(&missing_lock.stderr).contains("run talk install first"),
        "{}",
        String::from_utf8_lossy(&missing_lock.stderr)
    );

    let install = Command::new(env!("CARGO_BIN_EXE_talk"))
        .args(["install", "--offline"])
        .current_dir(&root)
        .output()
        .expect("install");
    assert!(
        install.status.success(),
        "{}",
        String::from_utf8_lossy(&install.stderr)
    );

    let check = talk().current_dir(&root).output().expect("package check");
    assert!(
        check.status.success(),
        "{}\n{}",
        String::from_utf8_lossy(&check.stdout),
        String::from_utf8_lossy(&check.stderr)
    );

    // The trigger walks up: src/ is inside the package.
    let from_src = talk()
        .current_dir(root.join("src"))
        .output()
        .expect("package check from src");
    assert!(
        from_src.status.success(),
        "{}\n{}",
        String::from_utf8_lossy(&from_src.stdout),
        String::from_utf8_lossy(&from_src.stderr)
    );

    // A type error in a file the binary never imports still fails the
    // check, reported against that file.
    std::fs::write(
        root.join("src/orphan.tlk"),
        "func broken() -> Int {\n\t\"missing int\"\n}\n",
    )
    .expect("orphan source");
    let broken = talk().current_dir(&root).output().expect("package check");
    assert!(!broken.status.success());
    assert!(
        String::from_utf8_lossy(&broken.stdout).contains("orphan.tlk"),
        "{}",
        String::from_utf8_lossy(&broken.stdout)
    );
    std::fs::remove_file(root.join("src/orphan.tlk")).expect("remove orphan");

    // `-` still reads stdin from inside the package.
    use std::io::Write as _;
    let mut child = Command::new(env!("CARGO_BIN_EXE_talk"))
        .args(["check", "-"])
        .current_dir(&root)
        .stdin(std::process::Stdio::piped())
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::piped())
        .spawn()
        .expect("spawn talk check -");
    child
        .stdin
        .take()
        .expect("stdin")
        .write_all(b"print(1 + \"x\")\n")
        .expect("write source");
    let stdin_check = child.wait_with_output().expect("talk check -");
    assert!(!stdin_check.status.success());
    assert!(
        String::from_utf8_lossy(&stdin_check.stdout).contains("<stdin>"),
        "{}",
        String::from_utf8_lossy(&stdin_check.stdout)
    );

    std::fs::remove_dir_all(dir).expect("remove package fixture");
}

#[test]
fn run_performs_ambient_io_operations() {
    // `'io(request)` performs route through core's source-level host
    // fallback to the runtime's host operations (sleep, open/write/
    // read/close round trip).
    let unique = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .expect("system clock after epoch")
        .as_nanos();
    let path = std::env::temp_dir().join(format!("talk-io-{}-{unique}.txt", std::process::id()));
    let source = format!(
        "#unsafe {{\n\
         let ok = sleep(ms: 0)\n\
         let fd = open_path(path: \"{}\", flags: O_WRONLY + O_CREAT + O_TRUNC, mode: S_IRUSR + S_IWUSR)\n\
         write_string(fd: fd, s: \"hello\")\n\
         _io_close(fd: fd)\n\
         let rfd = open_path(path: \"{}\", flags: O_RDONLY, mode: 0)\n\
         let buf = _alloc<Byte>(count: 8)\n\
         let count = _io_read(fd: rfd, buf: buf, count: 8)\n\
         _io_close(fd: rfd)\n\
         _free(ptr: buf)\n\
         print(count)\n\
         }}\n\
         ",
        path.display(),
        path.display()
    );
    let output = run_source(source.as_bytes(), &[]);
    assert!(
        output.status.success(),
        "stderr:\n{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert_eq!(output.stdout, b"5\n");
    let _ = std::fs::remove_file(path);
}

#[test]
fn mir_and_bytecode_inspection_render() {
    for command in ["mir", "bytecode"] {
        let mut child = Command::new(env!("CARGO_BIN_EXE_talk"))
            .arg(command)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .expect("run inspection");
        child
            .stdin
            .take()
            .expect("piped stdin")
            .write_all(b"40 + 2\n")
            .expect("write source");
        let output = child.wait_with_output().expect("read inspection output");
        assert!(
            output.status.success(),
            "{command}: {}",
            String::from_utf8_lossy(&output.stderr)
        );
        assert!(!output.stdout.is_empty(), "{command} rendered nothing");
    }
}

#[test]
fn bootstrap_writes_artifact_and_manifest_and_check_detects_staleness() {
    let unique = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .expect("system clock after epoch")
        .as_nanos();
    let dir = std::env::temp_dir().join(format!("talk-boot-{}-{unique}", std::process::id()));
    let src_dir = dir.join("frontend");
    std::fs::create_dir_all(&src_dir).expect("source dir");
    let source = src_dir.join("Svc.tlk");
    std::fs::write(&source, "pub func double(n: Int) -> Int { n * 2 }\n").expect("write source");
    let artifact = dir.join("frontend.tbc");

    let bootstrap = |extra: &[&str]| {
        let mut command = Command::new(env!("CARGO_BIN_EXE_talk"));
        command
            .arg("bootstrap")
            .arg(&src_dir)
            .args(["--export", "double"])
            .arg("-o")
            .arg(&artifact)
            .args(extra);
        command.output().expect("run bootstrap")
    };

    let generate = bootstrap(&[]);
    assert!(
        generate.status.success(),
        "{}",
        String::from_utf8_lossy(&generate.stderr)
    );
    assert!(artifact.exists(), "artifact written");
    let manifest = dir.join("frontend.manifest");
    let manifest_text = std::fs::read_to_string(&manifest).expect("manifest written");
    assert!(
        manifest_text.contains("artifact_digest:"),
        "{manifest_text}"
    );

    let check = bootstrap(&["--check"]);
    assert!(
        check.status.success(),
        "fresh artifact must pass --check: {}",
        String::from_utf8_lossy(&check.stderr)
    );

    // Editing a source without regenerating must fail the check.
    std::fs::write(&source, "pub func double(n: Int) -> Int { n + n }\n").expect("edit source");
    let stale = bootstrap(&["--check"]);
    assert!(!stale.status.success(), "stale artifact must fail --check");
    assert!(
        String::from_utf8_lossy(&stale.stderr).contains("stale"),
        "{}",
        String::from_utf8_lossy(&stale.stderr)
    );

    std::fs::remove_dir_all(dir).expect("remove bootstrap dir");
}

#[test]
fn bytecode_builds_are_deterministic_across_processes() {
    // ADR 0043's bootstrap fixed point: compiling the same source must
    // produce byte-identical images, across separate compiler processes
    // (per-process hash seeding and allocation addresses must not leak
    // into the artifact). The fixture exercises the demand-driven paths
    // most likely to depend on map iteration order: generic
    // monomorphization, conformance dictionaries, closures, enums.
    let unique = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .expect("system clock after epoch")
        .as_nanos();
    let dir = std::env::temp_dir().join(format!("talk-det-{}-{unique}", std::process::id()));
    std::fs::create_dir_all(&dir).expect("fixture dir");
    let source = dir.join("prog.tlk");
    std::fs::write(
        &source,
        r#"protocol Greet {
	func greet() -> String
}

struct Cat {
	let name: String
}

struct Dog {
	let name: String
}

extend Cat: Greet {
	func greet() -> String { "meow " + self.name }
}

extend Dog: Greet {
	func greet() -> String { "woof " + self.name }
}

func chorus<T: Greet>(voices: [T]) -> String {
	let out = ""
	for voice in voices {
		out = out + voice.greet()
	}
	out
}

enum Tree 'heap {
	case leaf(Int)
	case node(Tree, Tree)
}

func total(tree: &Tree) -> Int {
	match tree {
		.leaf(n) -> n,
		.node(l, r) -> total(tree: l) + total(tree: r)
	}
}

let cats = [Cat(name: "a"), Cat(name: "b")]
let dogs = [Dog(name: "c")]
print(chorus(voices: cats))
print(chorus(voices: dogs))
print(total(tree: Tree.node(Tree.leaf(1), Tree.node(Tree.leaf(2), Tree.leaf(3)))).show())
"#,
    )
    .expect("write source");

    // The dedicated fixture plus a spread of repo examples: effects and
    // handlers, iterator/closure glue, and the Unicode tables.
    let mut subjects = vec![source];
    for example in [
        "tests/examples/Effects.tlk",
        "tests/examples/ForLoop.tlk",
        "tests/examples/Graphemes.tlk",
    ] {
        subjects.push(std::path::PathBuf::from(example));
    }

    for (ix, subject) in subjects.iter().enumerate() {
        let mut images = Vec::new();
        for run in 0..2 {
            let image = dir.join(format!("prog-{ix}-{run}.tbc"));
            let build = Command::new(env!("CARGO_BIN_EXE_talk"))
                .args(["build", "-o"])
                .arg(&image)
                .arg(subject)
                .output()
                .expect("build image");
            assert!(
                build.status.success(),
                "{}: {}",
                subject.display(),
                String::from_utf8_lossy(&build.stderr)
            );
            images.push(std::fs::read(&image).expect("read image"));
        }
        assert_eq!(
            images[0],
            images[1],
            "{} compiled to different images across processes",
            subject.display()
        );
    }

    std::fs::remove_dir_all(dir).expect("remove fixture dir");
}

#[test]
fn build_and_run_image_round_trip() {
    let unique = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .expect("system clock after epoch")
        .as_nanos();
    let dir = std::env::temp_dir().join(format!("talk-image-{}-{unique}", std::process::id()));
    std::fs::create_dir_all(&dir).expect("image dir");
    let source = dir.join("prog.tlk");
    let image = dir.join("prog.tbc");
    std::fs::write(&source, "print(\"built\")\n40 + 2\n").expect("write source");

    let build = Command::new(env!("CARGO_BIN_EXE_talk"))
        .args(["build", "-o"])
        .arg(&image)
        .arg(&source)
        .output()
        .expect("build image");
    assert!(
        build.status.success(),
        "{}",
        String::from_utf8_lossy(&build.stderr)
    );

    let run = Command::new(env!("CARGO_BIN_EXE_talk"))
        .arg("run-image")
        .arg(&image)
        .output()
        .expect("run image");
    assert!(
        run.status.success(),
        "{}",
        String::from_utf8_lossy(&run.stderr)
    );
    assert_eq!(run.stdout, b"built\n42\n");

    std::fs::remove_dir_all(dir).expect("remove image dir");
}

#[test]
fn test_command_reports_passes_and_failures() {
    let unique = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .expect("system clock after epoch")
        .as_nanos();
    let dir = std::env::temp_dir().join(format!("talk-testcmd-{}-{unique}", std::process::id()));
    std::fs::create_dir_all(&dir).expect("test dir");
    std::fs::write(
        dir.join("math.test.tlk"),
        "test(\"good\") {\n\tassert(1 + 1 == 2)\n}\ntest(\"bad\") {\n\tassert_message(false, \"nope\")\n}\n",
    )
    .expect("test file");

    let output = Command::new(env!("CARGO_BIN_EXE_talk"))
        .arg("test")
        .arg(&dir)
        .output()
        .expect("run talk test");
    assert!(!output.status.success());
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(stdout.contains("bad"), "{stdout}");
    assert!(stdout.contains("nope"), "{stdout}");

    std::fs::remove_dir_all(dir).expect("remove test dir");
}

#[test]
fn parity_heap_graph() {
    assert_parity_program("heap_graph");
}

#[test]
fn parity_handlers() {
    // TOOL-06's reviewed Talk-style rendering replaces the baseline CLI's
    // `I64(0)` debug format (ledger, "Deliberate ADR 0032 changes").
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"));
    let expected = std::fs::read(root.join("tests/parity/reviewed-programs/handlers.stdout"))
        .expect("read reviewed expected stdout");
    let output = Command::new(env!("CARGO_BIN_EXE_talk"))
        .arg("run")
        .arg(root.join("tests/programs/handlers.tlk"))
        .output()
        .expect("run handlers");
    assert!(
        output.status.success(),
        "handlers failed:\n{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert_eq!(output.stdout, expected);
    assert!(output.stderr.is_empty());
}

#[test]
fn parity_caller_locals_handler() {
    assert_parity_program("caller_locals_handler");
}

#[test]
fn parity_nested_handlers() {
    assert_parity_program("nested_handlers");
}

#[test]
fn parity_resume_across_frames() {
    assert_parity_program("resume_across_frames");
}

#[test]
fn parity_multi_effect_handlers() {
    assert_parity_program("multi_effect_handlers");
}

#[test]
fn parity_generic_state() {
    assert_parity_program("generic_state");
}

#[test]
fn parity_generic_two_instantiations() {
    assert_parity_program("generic_two_instantiations");
}

#[test]
fn parity_effectful_closures() {
    assert_parity_program("effectful_closures");
}

#[test]
fn abort_through_an_init_unwinds_the_assigned_fields_only() {
    // ADR 0045: an effect abort through an initializer drops exactly
    // the assigned-so-far fields (reverse order), never the blank
    // placeholders — the C++/Swift/Rust partial-initialization rule.
    // Before any assignment: nothing to release.
    assert_runs(
        b"effect 'bail(error) -> Never\n\
          struct Holder {\n\
          \tlet data: [Int]\n\
          \tinit(n: Int) {\n\
          \t\t'bail(\"stop\")\n\
          \t\tself.data = [n]\n\
          \t}\n\
          }\n\
          func build() 'bail -> Int {\n\
          \tlet h = Holder(n: 1)\n\
          \th.data.count\n\
          }\n\
          #handle 'bail { err in\n\
          \tprint(\"bailed\")\n\
          }\n\
          print(build())\n",
        &[],
        b"bailed\n",
    );
    // After a partial assignment: the assigned buffer-owning field
    // releases on the unwind (the leak fence at exit pins it), the
    // still-blank field does not.
    assert_runs(
        b"effect 'bail(error) -> Never\n\
          struct Pair2 {\n\
          \tlet left: [Int]\n\
          \tlet right: [Int]\n\
          \tinit(n: Int) {\n\
          \t\tself.left = [n, n]\n\
          \t\t'bail(\"stop\")\n\
          \t\tself.right = [n]\n\
          \t}\n\
          }\n\
          func build() 'bail -> Int {\n\
          \tlet p = Pair2(n: 2)\n\
          \tp.left.count + p.right.count\n\
          }\n\
          #handle 'bail { err in\n\
          \tprint(\"bailed\")\n\
          }\n\
          print(build())\n",
        &[],
        b"bailed\n",
    );
    // Reassignment inside the init: the displaced first value is real
    // and drops at the write; the second leaves with the receiver.
    assert_runs(
        b"struct Holder {\n\
          \tlet data: [Int]\n\
          \tinit(n: Int) {\n\
          \t\tself.data = [n]\n\
          \t\tself.data = [n, n]\n\
          \t}\n\
          }\n\
          print(Holder(n: 3).data.count)\n",
        &[],
        b"2\n",
    );
}

#[test]
fn divergent_init_assignment_rejects() {
    // A field assigned on one branch but not the other has no static
    // abort cleanup at the join; the initializer must assign it in all
    // branches or before branching (path-uniform initialization, the
    // C++ discipline — a diagnostic, not a runtime drop flag).
    let source = b"struct Holder {\n\
        \tlet data: [Int]\n\
        \tinit(n: Int) {\n\
        \t\tif n > 0 {\n\
        \t\t\tself.data = [n]\n\
        \t\t}\n\
        \t\tif n <= 0 {\n\
        \t\t\tself.data = []\n\
        \t\t}\n\
        \t}\n\
        }\n\
        print(Holder(n: 1).data.count)\n";
    let output = run_source(source, &[]);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        !output.status.success(),
        "divergent assignment must reject, got: {}",
        String::from_utf8_lossy(&output.stdout)
    );
    assert!(
        stderr.contains("assigned on every branch") || stderr.contains("initialized"),
        "{stderr}"
    );
}

#[test]
fn run_executes_mut_arguments() {
    // `mut` parameters (exclusive borrows, ADR 0018) return their evolved
    // values to the caller for writeback — locals and script globals.
    assert_runs(
        b"func bump(mut x: Int) -> Void {\n\tx = x + 1\n}\nlet n = 1\nbump(x: mut n)\nbump(x: mut n)\nprint(n)\nlet g = 10\nbump(x: mut g)\nprint(g)\n",
        &[],
        b"3\n11\n",
    );
    // Function values follow the same type-derived writeback convention
    // (CLO-02 indirect calling convention).
    assert_runs(
        b"func g() -> Int {\n\tlet f = func(mut x: Int) -> Void {\n\t\tx = x + 1\n\t}\n\tlet y = 1\n\tf(mut y)\n\tf(mut y)\n\ty\n}\nprint(g())\n",
        &[],
        b"3\n",
    );
}

#[test]
fn run_executes_or_pattern_bindings() {
    // Or-pattern alternatives bind the same names into one shared local.
    assert_runs(
        b"enum E {\n\tcase a(Int)\n\tcase b(Int)\n}\nlet e = E.b(7)\nmatch e {\n\t.a(x) | .b(x) -> print(x)\n}\n",
        &[],
        b"7\n",
    );
}

#[test]
fn run_executes_character_literals() {
    // A character literal is a borrowed grapheme view over static bytes.
    assert_runs(b"let c = 'a'\nprint(c.utf8_count())\n", &[], b"1\n");
}

#[test]
fn run_executes_recursive_local_functions() {
    // Nested capture-free `func` declarations index like top-level ones,
    // so self-recursive calls resolve.
    assert_runs(
        b"func f() -> Int {\n\tfunc inner(n: Int) -> Int {\n\t\tif n <= 0 { return 0 }\n\t\tn + inner(n: n - 1)\n\t}\n\tinner(n: 3)\n}\nprint(f())\n",
        &[],
        b"6\n",
    );
}

#[test]
fn run_routes_clause_performs_to_outer_handlers() {
    // CHG-01: a perform inside a handler clause searches from below the
    // clause's own delimiter, so it reaches the next handler out.
    assert_runs(
        b"effect 'ask() -> Int\n#handle 'ask {\n\t'continue 1\n}\nfunc f() 'ask -> Int {\n\t#handle 'ask {\n\t\t'continue 'ask() + 10\n\t}\n\t'ask()\n}\nprint(f())\n",
        &[],
        b"11\n",
    );
}

#[test]
fn run_keeps_arm_bindings_across_inner_statements() {
    // A match arm's bound payload is arm-owned: statements inside the
    // arm body flush their own temporaries, not the binding (this
    // miscompiled as drop-then-retain — the talk-syntax method_decl
    // double-free family).
    assert_runs(
        b"struct Thing {\n\
          \tlet a: String\n\
          \tinit(a: String) {\n\
          \t\tself.a = a\n\
          \t\tself\n\
          \t}\n\
          }\n\
          enum Out {\n\
          \tcase out(Thing)\n\
          \tcase nope\n\
          }\n\
          func go() -> Out {\n\
          \tmatch Optional.some(Thing(a: \"aa\" + \"a\")) {\n\
          \t\t.some(t) -> {\n\
          \t\t\tlet n = t.a.byte_count\n\
          \t\t\tOut.out(t)\n\
          \t\t},\n\
          \t\t.none -> Out.nope\n\
          \t}\n\
          }\n\
          match go() {\n\
          \t.out(t) -> print(t.a.byte_count),\n\
          \t.nope -> print(0 - 1)\n\
          }\n",
        &[],
        b"3\n",
    );
    // The returning-arm variant of the same shape.
    assert_runs(
        b"struct Thing {\n\
          \tlet a: String\n\
          \tinit(a: String) {\n\
          \t\tself.a = a\n\
          \t\tself\n\
          \t}\n\
          }\n\
          enum Out {\n\
          \tcase out(Thing)\n\
          \tcase nope\n\
          }\n\
          func go() -> (Out, Int) {\n\
          \tmatch Optional.some(Thing(a: \"aa\" + \"a\")) {\n\
          \t\t.some(t) -> {\n\
          \t\t\tlet n = t.a.byte_count\n\
          \t\t\treturn (Out.out(t), n)\n\
          \t\t},\n\
          \t\t.none -> ()\n\
          \t}\n\
          \t(Out.nope, 0)\n\
          }\n\
          match go() {\n\
          \t(o, n) -> match o {\n\
          \t\t.out(t) -> print(t.a.byte_count + n),\n\
          \t\t.nope -> print(0 - 1)\n\
          \t}\n\
          }\n",
        &[],
        b"6\n",
    );
}

#[test]
fn run_retains_field_reads_consumed_by_constructions() {
    // A construction argument read from another value's field donates a
    // reference like a call argument would; the source value still owns
    // its copy (this double-freed as the talk-syntax for_stmt family).
    assert_runs(
        b"struct Inner {\n\
          \tlet s: String\n\
          \tinit(s: String) {\n\
          \t\tself.s = s\n\
          \t\tself\n\
          \t}\n\
          }\n\
          struct Box2 {\n\
          \tlet s: String\n\
          \tinit(s: String) {\n\
          \t\tself.s = s\n\
          \t\tself\n\
          \t}\n\
          }\n\
          func make() -> Inner {\n\
          \tInner(s: \"aa\" + \"a\")\n\
          }\n\
          func go() -> Int {\n\
          \tlet b = Box2(s: make().s)\n\
          \tb.s.byte_count\n\
          }\n\
          print(go())\n",
        &[],
        b"3\n",
    );
}

#[test]
fn run_balances_temps_when_a_sibling_arm_returns() {
    // A returning arm drops the statement's live temporaries for its
    // own path only; the surviving arm still owns them (the drop must
    // not consume the builder's shared ownership state).
    assert_runs(
        b"enum Kind {\n\
          \tcase a\n\
          \tcase b\n\
          }\n\
          func pick(kinds: [Kind]) -> Result<Int, String> {\n\
          \tResult.ok(kinds.count)\n\
          }\n\
          func go() -> Int {\n\
          \tlet n = match pick(kinds: [Kind.a, Kind.b, Kind.a]) {\n\
          \t\t.ok(n) -> n,\n\
          \t\t.error(e) -> return 0 - 1\n\
          \t}\n\
          \tn\n\
          }\n\
          print(go())\n\
          ",
        &[],
        b"3\n",
    );
}

#[test]
fn run_captures_capabilities_lexically() {
    // Reference pin: a function value keeps the handlers of its
    // creation site, not its call site (Effekt-style capabilities —
    // Brachthäuser, Schuster & Ostermann, OOPSLA 2020; ADR 0011
    // departure (d)). `f` routes to the first handler (100) even
    // though a second (200) covers the call.
    assert_runs(
        b"effect 'boost() -> Int\n\
          func run() -> Int {\n\
          \t#handle 'boost { 'continue 100 }\n\
          \tlet f = func() -> Int { 'boost() }\n\
          \t#handle 'boost { 'continue 200 }\n\
          \tf() + 'boost()\n\
          }\n\
          run()\n",
        &[],
        b"300\n",
    );
}

#[test]
fn run_releases_intermediates_of_a_return_chain() {
    // `return a + b + c` builds intermediate strings; the return path
    // must drop them like a tail expression would (this leak made the
    // Identity and Show examples fail their balance checks).
    assert_runs(
        b"func f() -> String {\n\tlet s = \"b\"\n\treturn \"a\" + \".\" + s\n}\nprint(f())\n",
        &[],
        b"a.b\n",
    );
    assert_runs(b"print(1.23)\n", &[], b"1.229999999999999\n");
}

#[test]
fn run_drops_a_payload_binding_on_the_break_path_after_a_sibling_arm_consumed_it() {
    // The then-arm's `return Result.error(err)` consumes the arm-owned
    // payload temporary; the break path must still drop its own copy.
    // The owned-type table is shared across sibling arms — consumption
    // deleting from it made the break path's flush skip the drop, a
    // real leak (found by the wave-B balance verifier).
    assert_runs(
        b"func mk() -> Result<Int, String> {\n\tResult.error(\"boom\" + \"!\")\n}\nfunc f(flag: Bool) -> Result<Int, String> {\n\tlet total = 0\n\tloop {\n\t\tlet x = match mk() {\n\t\t\t.ok(v) -> v,\n\t\t\t.error(err) -> {\n\t\t\t\tif flag { return Result.error(err) }\n\t\t\t\tbreak\n\t\t\t}\n\t\t}\n\t\ttotal = total + x\n\t}\n\tResult.ok(total)\n}\nprint(f(flag: false))\n",
        &[],
        b"Result.ok(0)\n",
    );
}

#[test]
fn run_retains_borrowed_sources_stored_into_owning_containers() {
    // A borrowed parameter packed into a tuple (an owning container)
    // donates a reference (rule 2 of docs/ownership.md).
    // Consuming with the source's borrow type skipped the retain, so
    // the match decomposition freed the caller's payload — twice by
    // the second call.
    assert_runs(
        b"enum MaybeText {\n\tcase some(String)\n\tcase none\n}\nfunc inspect(lhs: MaybeText) -> Int {\n\tmatch (lhs, MaybeText.some(\"owned\" + \" payload\")) {\n\t\t(MaybeText.some(value), MaybeText.some(_)) -> value.byte_count,\n\t\t_ -> 0\n\t}\n}\nfunc check() -> Int {\n\tlet lhs = MaybeText.some(\"borrowed\" + \" payload\")\n\tinspect(lhs: lhs) + inspect(lhs: lhs)\n}\ncheck()\n",
        &[],
        b"32\n",
    );
}

#[test]
fn run_retains_a_consumed_value_that_has_later_uses() {
    // Rule 1 (docs/ownership.md): a consume that is not
    // the value's last use donates a reference instead of moving, so
    // use-after-move stops being an error for shareable types.
    assert_runs(
        b"func take(consume s: String) -> Int {\n\ts.byte_count\n}\nlet s = \"hello\" + \" world\"\nlet n = take(s: s)\ns.byte_count + n\n",
        &[],
        b"22\n",
    );
    // Consuming an outer binding inside a loop retains on every
    // iteration; the loop may repeat.
    assert_runs(
        b"func take(consume s: String) -> Int {\n\ts.byte_count\n}\nlet s = \"a\" + \"b\"\nlet i = 0\nlet n = 0\nloop i < 3 {\n\tn = n + take(s: s)\n\ti = i + 1\n}\nn\n",
        &[],
        b"6\n",
    );
}

#[test]
fn run_snapshots_a_live_view_across_owner_move_and_reassignment() {
    // Snapshot semantics (docs/ownership.md): consuming
    // an owner with a live view retains it, and reassigning one
    // displaces the old value to scope exit, so the view stays valid.
    assert_runs(
        b"func f() -> Int {\n\tlet s = \"hello\" + \" world\"\n\tlet sub = s.utf8().slice(start: 0, byte_count: 1)\n\tlet moved = s\n\tsub.byte_count + moved.byte_count\n}\nf()\n",
        &[],
        b"12\n",
    );
    assert_runs(
        b"func f() -> Int {\n\tlet s = \"hello\" + \" world\"\n\tlet sub = s.utf8().slice(start: 0, byte_count: 5)\n\ts = \"x\" + \"y\"\n\tsub.byte_count + s.byte_count\n}\nf()\n",
        &[],
        b"7\n",
    );
}

#[test]
fn run_entry_requires_a_public_function() {
    // `--entry` is documented as running a zero-parameter *public*
    // function; a private one must be rejected, not silently executed.
    let output = run_source(
        b"func secret() -> Int {\n\t3\n}\n0\n",
        &["--entry", "secret"],
    );
    assert!(!output.status.success(), "private entry executed");
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("must be a public function"),
        "stderr: {stderr}"
    );
}

#[test]
fn run_package_entry_flag_selects_the_named_function() {
    // Inside a package, `talk run --entry name` must execute the named
    // zero-parameter function, not silently fall back to the script.
    let nonce = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .expect("clock")
        .as_nanos();
    let dir = std::env::temp_dir().join(format!("talk-entry-{}-{nonce}", std::process::id()));
    std::fs::create_dir_all(dir.join("src")).expect("package dirs");
    std::fs::write(
        dir.join("package.tlk"),
        "Package(\n\tname: \"entrypkg\",\n\tversion: \"0.1.0\",\n\tbuilds: [.bin(named: \"main\", from: \"src/main.tlk\")],\n\tdependencies: []\n)\n",
    )
    .expect("manifest");
    std::fs::write(
        dir.join("src/main.tlk"),
        "pub func alt() -> Int {\n\tprint(\"alt ran\")\n\t7\n}\nprint(\"script ran\")\n",
    )
    .expect("main");
    let install = Command::new(env!("CARGO_BIN_EXE_talk"))
        .arg("install")
        .arg("--offline")
        .current_dir(&dir)
        .output()
        .expect("talk install");
    assert!(
        install.status.success(),
        "{}",
        String::from_utf8_lossy(&install.stderr)
    );
    let run = Command::new(env!("CARGO_BIN_EXE_talk"))
        .arg("run")
        .arg("--entry")
        .arg("alt")
        .current_dir(&dir)
        .output()
        .expect("talk run");
    assert!(
        run.status.success(),
        "{}",
        String::from_utf8_lossy(&run.stderr)
    );
    let stdout = String::from_utf8_lossy(&run.stdout);
    assert!(stdout.contains("alt ran"), "stdout: {stdout}");
    assert!(!stdout.contains("script ran"), "stdout: {stdout}");
    std::fs::remove_dir_all(&dir).ok();
}

#[test]
fn check_reads_stdin_once_for_both_passes() {
    // The ownership pass re-compiles from the text the frontend pass
    // already read: stdin can only be consumed once, so a rejected
    // program piped through `-` must still fail the check.
    use std::io::Write as _;
    let mut child = Command::new(env!("CARGO_BIN_EXE_talk"))
        .arg("check")
        .arg("-")
        .current_dir(env!("CARGO_MANIFEST_DIR"))
        .stdin(std::process::Stdio::piped())
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::piped())
        .spawn()
        .expect("spawn talk check");
    let source =
        std::fs::read("tests/reference/flow/linear_value_dropped_at_scope_exit_is_rejected.tlk")
            .expect("fixture");
    child
        .stdin
        .take()
        .expect("stdin")
        .write_all(&source)
        .expect("write fixture");
    let output = child.wait_with_output().expect("talk check");
    assert!(
        !output.status.success(),
        "check accepted a rejected program over stdin"
    );
}

#[test]
fn check_accepts_uncalled_static_generic_bodies() {
    // `talk check` compiles every callable rigidly (TALK_CHECK_ALL); a
    // static parameter read in a generic body is an abstract value
    // there (ADR 0035 §6), not an error — for plain funcs, nominal
    // methods, and protocol defaults alike, called or not.
    use std::io::Write as _;
    let source = b"func width<static N: Int>() -> Int { N }\n\
        struct Grid<static Rows: Int> {\n\
        \tfunc size() -> Int { Rows }\n\
        }\n\
        protocol Sized<static N: Int> {\n\
        \tfunc area() -> Int { N }\n\
        }\n";
    let mut child = Command::new(env!("CARGO_BIN_EXE_talk"))
        .arg("check")
        .arg("-")
        .current_dir(env!("CARGO_MANIFEST_DIR"))
        .stdin(std::process::Stdio::piped())
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::piped())
        .spawn()
        .expect("spawn talk check");
    child
        .stdin
        .take()
        .expect("stdin")
        .write_all(source)
        .expect("write source");
    let output = child.wait_with_output().expect("talk check");
    assert!(
        output.status.success(),
        "check rejected valid static-generic declarations:\n{}{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );
}

#[test]
fn check_accepts_protocol_defaults_using_associated_type_bounds() {
    // `talk check` compiles every callable rigidly (TALK_CHECK_ALL). A
    // protocol default body calling a method on a constrained
    // associated type needs that type's dictionary block bound in the
    // rigid frame — the seed must range over the protocol's associated
    // types, not just Self and its input parameters. The program runs
    // fine (the demanded instance substitutes the conformance row's
    // inferred bindings); only the rigid compile exercises this.
    use std::io::Write as _;
    let source = b"protocol Named {\n\
        \tfunc name() -> String\n\
        }\n\
        struct Snack {}\n\
        extend Snack: Named {\n\
        \tfunc name() { \"snack\" }\n\
        }\n\
        protocol Pet {\n\
        \tassociated Food: Named\n\
        \tfunc favoriteFood() -> Food\n\
        \tfunc describe() {\n\
        \t\tprint(self.favoriteFood().name())\n\
        \t}\n\
        }\n\
        struct Cat {}\n\
        extend Cat: Pet {\n\
        \tfunc favoriteFood() { Snack() }\n\
        }\n\
        Cat().describe()\n";
    let mut child = Command::new(env!("CARGO_BIN_EXE_talk"))
        .arg("check")
        .arg("-")
        .current_dir(env!("CARGO_MANIFEST_DIR"))
        .stdin(std::process::Stdio::piped())
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::piped())
        .spawn()
        .expect("spawn talk check");
    child
        .stdin
        .take()
        .expect("stdin")
        .write_all(source)
        .expect("write source");
    let output = child.wait_with_output().expect("talk check");
    assert!(
        output.status.success(),
        "check rejected a protocol default over a constrained associated type:\n{}{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );
}

#[test]
fn check_reports_ownership_errors_like_run_does() {
    // `talk check` runs the ownership analysis (wave F of
    // docs/ownership.md): a program `talk run` rejects
    // must fail `talk check` with the same diagnostic, not pass
    // silently.
    let output = Command::new(env!("CARGO_BIN_EXE_talk"))
        .arg("check")
        .arg("tests/reference/flow/rejects_read_while_mutable_borrow_is_live.tlk")
        .current_dir(env!("CARGO_MANIFEST_DIR"))
        .output()
        .expect("run talk check");
    assert!(
        !output.status.success(),
        "check accepted a program run rejects"
    );
    let printed = format!(
        "{}{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(
        printed.contains("already mutable borrowed"),
        "diagnostic missing:\n{printed}"
    );
}

#[test]
fn run_retains_consumes_with_later_uses_inside_trailing_blocks() {
    // A trailing block compiles as its own frame, but its body never
    // seeded the use counts rule 1 reads — so a consume with later
    // uses moved instead of retaining and the later use was rejected.
    assert_runs(
        b"func take(consume s: String) -> Int {\n\ts.byte_count\n}\nfunc run(f: () -> Int) -> Int {\n\tf()\n}\nfunc check() -> Int {\n\trun {\n\t\tlet s = \"hello\" + \" world\"\n\t\tlet n = take(s: s)\n\t\ts.byte_count + n\n\t}\n}\ncheck()\n",
        &[],
        b"22\n",
    );
}

#[test]
fn run_releases_statement_position_if_values() {
    // A statement-position `if` whose arms produce a droppable value
    // (here a mut call's returned Optional of a view) merged it into
    // the join parameter without registering a temporary: nobody
    // released it once views became owning. The lexer-shaped
    // composition that found it: a nested peek inside a loop with
    // breaks on both arms.
    assert_runs(
        b"struct Lex {\n\
          	let code: String\n\
          	let current: Int\n\
          	\n\
          	init(code: &String) {\n\
          	self.code = code.to_string()\n\
          	self.current = 0\n\
          	}\n\
          	}\n\
          	extend Lex {\n\
          	func char_at(pos: Int) -> Character? {\n\
          	if self.code.byte_count <= pos { return Optional.none }\n\
          	let iter = self.code.utf8().slice(start: pos, byte_count: self.code.byte_count - pos).iter()\n\
          	iter.next()\n\
          	}\n\
          	func peek() -> Character? {\n\
          	self.char_at(pos: self.current)\n\
          	}\n\
          	func peek_next() -> Character? {\n\
          	match self.peek() {\n\
          	.some(ch) -> self.char_at(pos: self.current + ch.utf8_count()),\n\
          	.none -> Optional.none\n\
          	}\n\
          	}\n\
          	mut func advance() -> Character? {\n\
          	match self.char_at(pos: self.current) {\n\
          	.some(ch) -> {\n\
          	self.current = self.current + ch.utf8_count()\n\
          	Optional.some(ch)\n\
          	},\n\
          	.none -> Optional.none\n\
          	}\n\
          	}\n\
          	mut func scan() -> Int {\n\
          	let is_float = false\n\
          	let n = 0\n\
          	loop {\n\
          	let ch = match self.peek() {\n\
          	.some(peeked) -> peeked,\n\
          	.none -> {\n\
          	break\n\
          	}\n\
          	}\n\
          	if ch == '.' {\n\
          	if is_float {\n\
          	break\n\
          	}\n\
          	let next_digit = match self.peek_next() {\n\
          	.some(next) -> next.is_numeric(),\n\
          	.none -> false\n\
          	}\n\
          	if next_digit == false {\n\
          	break\n\
          	}\n\
          	is_float = true\n\
          	self.advance()\n\
          	} else {\n\
          	let continues = ch.is_numeric()\n\
          	if continues == false {\n\
          	break\n\
          	}\n\
          	n = n + 1\n\
          	self.advance()\n\
          	}\n\
          	}\n\
          	n\n\
          	}\n\
          	\n\
          	}\n\
          	let lex = Lex(code: \"1.2x\")\n\
          	print(lex.scan())\n\
          	",
        &[],
        b"2\n",
    );
}

#[test]
fn run_shares_captured_assignments_with_the_frame() {
    // Superseded rejection (was CHG-06): the reference pins mutable
    // captures — the closure and the frame share one cell, so the
    // mutation is visible after the call.
    assert_runs(
        b"func f() -> Int {\n\tlet count = 0\n\tlet bump = func() -> Void {\n\t\tcount = count + 1\n\t}\n\tbump()\n\tcount\n}\nf()\n",
        &[],
        b"1\n",
    );
}

#[test]
fn run_unhandled_ambient_performs_reach_the_host_fallback() {
    // With no user handler live, an 'ambient perform routes to the host
    // fallback the entry wrapper installed (ADR 0039): for 'async the
    // reference host resumes with unit.
    assert_runs(b"'async()\nprint(1)\n", &[], b"1\n");
}

#[test]
fn run_user_handlers_intercept_ambient_effects() {
    // 'async is 'ambient (ADR 0039): a live user handler intercepts its
    // performs through the ordinary handler stack.
    assert_runs(
        b"#handle 'async {\n\tprint(\"yield\")\n\t'continue\n}\n'async()\nprint(1)\n",
        &[],
        b"yield\n1\n",
    );
}

#[test]
fn run_ambient_clause_performs_delegate_to_the_fallback() {
    // A clause executes below its own search floor (CHG-01), so a
    // perform inside it reaches the next handler out — here the host
    // fallback, which resumes with unit.
    assert_runs(
        b"#handle 'async {\n\tprint(\"seen\")\n\t'async()\n\t'continue\n}\n'async()\nprint(1)\n",
        &[],
        b"seen\n1\n",
    );
}

#[test]
fn run_nested_ambient_handlers_delegate_outward_to_the_fallback() {
    // inner user handler -> outer user handler -> host fallback: the
    // ordinary routing order for an ambient effect (ADR 0039 §4).
    assert_runs(
        b"#handle 'async {\n\tprint(\"outer\")\n\t'async()\n\t'continue\n}\n#handle 'async {\n\tprint(\"inner\")\n\t'async()\n\t'continue\n}\n'async()\nprint(1)\n",
        &[],
        b"inner\nouter\n1\n",
    );
}

#[test]
fn run_ambient_handlers_may_discontinue() {
    // An ambient handler follows the same one-shot rules as any handler:
    // a clause that completes without resuming aborts the handled scope
    // (with its value, which must match the scope's — unit here).
    assert_runs(
        b"#handle 'async {\n\tprint(\"abort\")\n}\n'async()\nprint(99)\n",
        &[],
        b"abort\n",
    );
}

#[test]
fn run_function_values_reach_the_fallback_without_a_user_handler() {
    // A function value with no user handler live at creation captures
    // the fallback capability — ambient effects follow the same
    // creation-site capture semantics as handled effects (ADR 0039 §5).
    assert_runs(
        b"let f = func() {\n\t'async()\n\t7\n}\nprint(f())\n",
        &[],
        b"7\n",
    );
}

#[test]
fn run_function_values_capture_ambient_handlers_at_creation() {
    assert_runs(
        b"#handle 'async {\n\tprint(\"captured\")\n\t'continue\n}\nlet f = func() {\n\t'async()\n\t7\n}\nprint(f())\n",
        &[],
        b"captured\n7\n",
    );
}

#[test]
fn run_module_initialization_may_perform_ambient_effects() {
    // Fallbacks install before module initialization (ADR 0039 §3), so a
    // top-level binding's initializer can perform an ambient effect —
    // under a named entry too, where lets still initialize first.
    assert_runs(
        b"func f() -> Int {\n\t'async()\n\t3\n}\nlet ready = f()\npub func go() -> () {\n\tprint(ready)\n}\n",
        &["--entry", "go"],
        b"3\n",
    );
}

#[test]
fn run_constructs_rigid_params_through_init_requirements() {
    // `T(x: 1)` for `T: Makeable` resolves through the bound's init
    // requirement; the committed conformance witness (the conforming
    // type's initializer) runs at the specialized call.
    assert_runs(
        b"protocol Makeable {\n\tinit(x: Int)\n}\nstruct Box {\n\tlet x: Int\n\tinit(x: Int) {\n\t\tself.x = x\n\t\tself\n\t}\n}\nextend Box: Makeable {}\nfunc make<T: Makeable>() -> T {\n\tT(x: 1)\n}\nlet b: Box = make()\nprint(b.x)\n",
        &[],
        b"1\n",
    );
}

#[test]
fn run_user_handlers_intercept_io() {
    // A user 'io handler substitutes results without invoking the host:
    // the intercepted sleeps return immediately, and the handler's count
    // proves both performs routed to it. (print bypasses 'io — it is a
    // raw io_write intrinsic — so it still reaches stdout.)
    assert_runs(
        b"let count = 0\n#handle 'io { request in\n\tcount = count + 1\n\t'continue 0\n}\nsleep(ms: 1)\nsleep(ms: 1)\nprint(count)\n",
        &[],
        b"2\n",
    );
}

#[test]
fn run_io_handlers_delegate_to_the_host_fallback() {
    // A clause re-performing the same request reaches the io host
    // fallback below its floor; the program still behaves normally.
    assert_runs(
        b"#handle 'io { request in\n\t'continue 'io(request: request)\n}\nsleep(ms: 1)\nprint(1)\n",
        &[],
        b"1\n",
    );
}

#[test]
fn run_lying_io_handlers_cannot_break_memory_safety() {
    // The stdlib io wrappers clamp reply counts to the capacity they
    // allocated: a handler that answers cwd_len with 8 and cwd_copy with
    // 999999 yields a wrong (truncated) string, never an out-of-bounds
    // view.
    assert_runs(
        b"use os::{ OS }\nlet calls = 0\n#handle 'io { request in\n\tcalls = calls + 1\n\tif calls == 1 {\n\t\t'continue 8\n\t}\n\t'continue 999999\n}\nlet c = OS.cwd()\nprint(calls)\n",
        &[],
        b"2\n",
    );
}

#[test]
fn run_alloc_performs_are_inert() {
    // Real allocation is carried by intrinsics, not performs; a bare
    // 'alloc perform reaches the no-op fallback and resumes.
    assert_runs(b"'alloc(allocation: .allocate(8))\nprint(1)\n", &[], b"1\n");
}

#[test]
fn run_assigns_through_nested_places() {
    // Place chains: struct-in-struct leaves write back up the value
    // links (records are copy-on-write).
    assert_runs(
        b"struct In {\n\tlet v: Int\n\tinit(v: Int) {\n\t\tself.v = v\n\t\tself\n\t}\n}\nstruct Out {\n\tlet inner: In\n\tinit(inner: In) {\n\t\tself.inner = inner\n\t\tself\n\t}\n}\nlet o = Out(inner: In(v: 1))\no.inner.v = 5\nprint(o.inner.v)\n",
        &[],
        b"5\n",
    );
    // A `mut` argument may name a projected place.
    assert_runs(
        b"struct Box {\n\tlet n: Int\n\tinit(n: Int) {\n\t\tself.n = n\n\t\tself\n\t}\n}\nfunc bump(mut x: Int) -> Void {\n\tx = x + 1\n}\nlet b = Box(n: 1)\nbump(x: mut b.n)\nbump(x: mut b.n)\nprint(b.n)\n",
        &[],
        b"3\n",
    );
}

#[test]
fn run_executes_record_rows() {
    // Closed record rows lay out as label-sorted tuples: literals,
    // field reads, and field assignment (with the displaced value
    // dropped).
    assert_runs(b"let r = {x: 1, y: 2}\nprint(r.x + r.y)\n", &[], b"3\n");
    assert_runs(
        b"let r = {x: 1, y: \"a\" + \"b\"}\nr.x = 5\nprint(r.x)\nprint(r.y)\n",
        &[],
        b"5\nab\n",
    );
}

#[test]
fn run_initializes_globals_for_named_entries() {
    // A named entry gets the same LINK-02 slot discipline scripts get:
    // ordered initialization (non-literal initializers included),
    // mutation, and guarded teardown.
    let source = b"let counter = 0\nlet name = \"talk\" + \"!\"\npub func main() -> Void {\n\tcounter = counter + 1\n\tprint(counter)\n\tprint(name)\n}\n";
    assert_runs(source, &["--entry", "main"], b"1\ntalk!\n");
}

#[test]
fn run_calls_function_values_stored_in_globals() {
    assert_runs(
        b"func f() -> Int {\n\t7\n}\nlet g = f\nprint(g())\n",
        &[],
        b"7\n",
    );
}

#[test]
fn run_clones_enum_values_with_payloads() {
    // Enum retains dispatch on the tag (CheapClone adds one reference
    // per owned payload buffer).
    assert_runs(
        b"enum E {\n\tcase s(String)\n}\nextend E: CheapClone {}\nlet e = E.s(\"a\" + \"b\")\nlet f = e.clone()\nmatch f {\n\t.s(x) -> print(x)\n}\n",
        &[],
        b"ab\n",
    );
}

/// The writeback convention crossed with every call shape. Each cell
/// makes two calls and observes the evolved state, so a lost writeback
/// or a shape mismatch fails loudly; the runtime's allocation balance
/// checks the ownership half of every cell for free.
#[test]
fn writeback_matrix_covers_call_shapes_and_mutation_shapes() {
    const PROTOCOL: &str = "protocol Counter {\n\tmut func bump_by(mut amount: Int) -> Int\n}\nstruct C {\n\tlet n: Int\n\tlet tag: String\n\tinit(n: Int, tag: String) {\n\t\tself.n = n\n\t\tself.tag = tag\n\t}\n}\nextend C: Counter {\n\tmut func bump_by(mut amount: Int) -> Int {\n\t\tself.n = self.n + amount\n\t\tamount = amount * 2\n\t\tself.n\n\t}\n}\n";
    let cells: Vec<(&str, String, &str)> = vec![
        (
            "direct/mut-param",
            "func bump(mut x: Int) -> Void {\n\tx = x + 1\n}\nlet n = 0\nbump(x: mut n)\nbump(x: mut n)\nprint(n)\n".into(),
            "2\n",
        ),
        (
            "direct/two-mut-params",
            "func swap_add(mut a: Int, mut b: Int) -> Void {\n\tlet t = a\n\ta = b + 1\n\tb = t + 1\n}\nlet x = 10\nlet y = 20\nswap_add(a: mut x, b: mut y)\nprint(x)\nprint(y)\n".into(),
            "21\n11\n",
        ),
        (
            "direct/mut-param-with-owned-arg",
            "func stamp(mut x: Int, consume s: String) -> Void {\n\tx = x + s.byte_count\n}\nlet n = 0\nstamp(x: mut n, s: \"ab\" + \"c\")\nprint(n)\n".into(),
            "3\n",
        ),
        (
            "method/mut-receiver",
            format!("{PROTOCOL}let c = C(n: 0, tag: \"t\" + \"g\")\nlet step = 3\nprint(c.bump_by(amount: mut step))\nprint(c.bump_by(amount: mut step))\n"),
            "3\n9\n",
        ),
        (
            "closure/two-mut-params",
            "func run() -> Void {\n\tlet f = func(mut a: Int, mut b: Int) -> Void {\n\t\ta = a + 1\n\t\tb = b + 2\n\t}\n\tlet x = 0\n\tlet y = 0\n\tf(mut x, mut y)\n\tf(mut x, mut y)\n\tprint(x)\n\tprint(y)\n}\nrun()\n".into(),
            "2\n4\n",
        ),
        (
            "global-fn-value/mut-param",
            "func bump(mut x: Int) -> Void {\n\tx = x + 1\n}\nlet g = bump\nlet n = 0\ng(mut n)\ng(mut n)\nprint(n)\n".into(),
            "2\n",
        ),
        (
            "rigid-dictionary/receiver-and-param",
            format!("{PROTOCOL}effect 'acc<T: Counter>(value: T) -> ()\n#handle 'acc {{ v in\n\tlet step = 3\n\tprint(v.bump_by(amount: mut step))\n\tprint(step)\n\tprint(v.bump_by(amount: mut step))\n\tprint(step)\n\t'continue ()\n}}\n'acc(value: C(n: 0, tag: \"t\" + \"g\"))\n"),
            "3\n6\n9\n12\n",
        ),
        (
            "existential/receiver-and-param",
            format!("{PROTOCOL}let a: any Counter = C(n: 0, tag: \"t\" + \"g\")\nlet step = 3\nprint(a.bump_by(amount: mut step))\nprint(step)\nprint(a.bump_by(amount: mut step))\nprint(step)\n"),
            "3\n6\n9\n12\n",
        ),
        (
            "perform/mut-arg",
            "effect 'adjust(mut value: Int) -> ()\n#handle 'adjust { v in\n\tv = v + 10\n\t'continue ()\n}\nlet n = 1\n'adjust(value: mut n)\n'adjust(value: mut n)\nprint(n)\n".into(),
            "21\n",
        ),
        (
            "perform/two-mut-args-with-owned-arg",
            "effect 'both(mut a: Int, mut b: Int, label: String) -> ()\n#handle 'both { p, q, s in\n\tp = p + s.byte_count\n\tq = q + 2\n\t'continue ()\n}\nlet x = 0\nlet y = 0\n'both(a: mut x, b: mut y, label: \"ab\" + \"c\")\nprint(x)\nprint(y)\n".into(),
            "3\n2\n",
        ),
        (
            "projected-place/mut-param",
            "struct Box {\n\tlet n: Int\n\tinit(n: Int) {\n\t\tself.n = n\n\t\tself\n\t}\n}\nfunc bump(mut x: Int) -> Void {\n\tx = x + 1\n}\nlet b = Box(n: 0)\nbump(x: mut b.n)\nbump(x: mut b.n)\nprint(b.n)\n".into(),
            "2\n",
        ),
    ];
    for (name, source, expected) in cells {
        let output = run_source(source.as_bytes(), &[]);
        assert!(
            output.status.success(),
            "{name}: {}",
            String::from_utf8_lossy(&output.stderr)
        );
        assert_eq!(
            String::from_utf8_lossy(&output.stdout),
            *expected,
            "{name} stdout mismatch; stderr: {}",
            String::from_utf8_lossy(&output.stderr)
        );
    }
}

/// The repo's own core `.test.tlk` suites, run exactly as a user runs
/// them (`talk test` over real files): the acceptance check that keeps
/// "it passes the unit tests" honest against "it runs real programs".
#[test]
fn talk_test_runs_the_core_suites() {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"));
    let mut files: Vec<std::path::PathBuf> = std::fs::read_dir(root.join("core"))
        .expect("list core sources")
        .filter_map(|entry| entry.ok().map(|entry| entry.path()))
        .filter(|path| {
            path.file_name()
                .and_then(|name| name.to_str())
                .is_some_and(|name| name.ends_with(".test.tlk"))
        })
        .collect();
    files.sort();
    assert!(!files.is_empty(), "no core test suites found");
    for file in files {
        let output = Command::new(env!("CARGO_BIN_EXE_talk"))
            .arg("test")
            .arg(&file)
            .output()
            .expect("run talk test");
        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(
            output.status.success() && stdout.contains("tests passed"),
            "{}:\nstdout: {stdout}\nstderr: {stderr}",
            file.display()
        );
    }
}

/// Opt-in acceptance gate (plan G3): run `talk test` in each external
/// Talk project listed in TALK_ACCEPTANCE_DIRS (colon-separated roots).
/// Skips silently when unset so CI without local corpora stays green;
/// set it locally to hold real projects as gates:
///   TALK_ACCEPTANCE_DIRS=~/apps/talk-html cargo test
#[test]
fn talk_test_runs_acceptance_projects() {
    let Some(dirs) = std::env::var_os("TALK_ACCEPTANCE_DIRS") else {
        return;
    };
    for root in std::env::split_paths(&dirs) {
        let output = Command::new(env!("CARGO_BIN_EXE_talk"))
            .arg("test")
            .current_dir(&root)
            .output()
            .expect("run talk test");
        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(
            output.status.success() && stdout.contains("tests passed"),
            "{}:\nstdout: {stdout}\nstderr: {stderr}",
            root.display()
        );
    }
}

/// The reference examples corpus (vendored from the mature compiler's
/// `examples/`, with its frozen stdout): every pinned example must
/// match byte-for-byte. Where a script ends in a non-unit expression,
/// the pin is the reference engine stdout plus this CLI's
/// trailing-value line (the reference harness read stdout and the
/// value separately; the stdout portion matches it byte-for-byte).
/// Known failures are the plan's burn-down list; shrink it, never
/// grow it.
#[test]
fn examples_corpus_matches_frozen_stdout() {
    // The burn-down list is empty: every pinned example passes.
    assert_corpus_dir("tests/examples", &[], 16);
}

#[test]
fn protocol_init_requirement_constructs_concrete_self() {
    // Construction through a protocol's init requirement: `Self` pins
    // from the expected type, and the conformance's witness initializer
    // (here the synthesized memberwise init) builds the value.
    assert_runs(
        b"protocol FromPair<T> {\n\
          \tinit(lower: T, upper: T)\n\
          }\n\
          struct Pair<T> {\n\
          \tlet lower: T\n\
          \tlet upper: T\n\
          }\n\
          extend<T> Pair<T>: FromPair<T> {}\n\
          let p: Pair<Int> = FromPair(lower: 1, upper: 5)\n\
          p.lower + p.upper\n",
        &[],
        b"6\n",
    );
}

#[test]
fn protocol_init_requirement_runs_explicit_witness_init() {
    // An explicit initializer witnesses the requirement and its body
    // runs at protocol construction.
    assert_runs(
        b"protocol FromCount {\n\
          \tinit(count: Int)\n\
          }\n\
          struct Doubled {\n\
          \tlet value: Int\n\
          \tinit(count: Int) {\n\
          \t\tself.value = count * 2\n\
          \t}\n\
          }\n\
          extend Doubled: FromCount {}\n\
          let d: Doubled = FromCount(count: 21)\n\
          d.value\n",
        &[],
        b"42\n",
    );
}

#[test]
fn range_literals_reach_runtime() {
    // `1..5` is inclusive (ClosedRange), `1..<5` half-open (Range);
    // both desugar to direct core-type constructions.
    assert_runs(
        b"let c = 1..5\n\
          let r = 1..<5\n\
          if c.contains(element: 5) && !r.contains(element: 5) && r.contains(element: 4) { 1 } else { 0 }\n\
          ",
        &[],
        b"1\n",
    );
}

#[test]
fn run_rejects_escaping_owned_captures() {
    // A closure over an owned capture holds a frame-anchored snapshot;
    // returning it would outlive the environment, so that edge fails
    // closed until environments own their captures outright.
    let output = run_source(
        b"func make() -> () -> Int {\n\tlet s = \"a\" + \"b\"\n\tlet g = func() -> Int { s.byte_count }\n\tg\n}\nlet g = make()\nprint(g())\n",
        &[],
    );
    assert!(!output.status.success());
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(stderr.contains("cannot escape"), "{stderr}");
}

#[test]
fn run_tears_down_globals_after_a_top_level_discontinue() {
    // A handler clause's finite value aborts the delimited statements,
    // but guarded global teardown still runs (ADR 0033).
    let source = b"effect 'quit() -> Never\n\
        let box = Array<String>(capacity: 0)\n\
        box.push(\"x\" + \"y\")\n\
        #handle 'quit { 0 - 1 }\n\
        func risky() 'quit -> Int {\n\
        \t'quit()\n\
        }\n\
        risky()\n";
    assert_runs(source, &[], b"-1\n");
}

#[test]
fn check_accepts_constrained_generic_bodies() {
    // A rigid frame's dictionaries come from the function's own scheme
    // predicates, not only effect signatures.
    assert_checks(b"func f<T: Showable>(x: T) -> String { x.show() }\nprint(f(x: 42))\n");
    // Derived operations on rigid leaves dispatch the same way.
    assert_checks(
        b"func same<T: Equatable>(a: T, b: T) -> Bool { a == b }\nprint(same(a: 1, b: 1))\n",
    );
}

#[test]
fn generic_dispatch_reaches_derived_and_default_entries() {
    // A receiver concrete only under an instance substitution
    // dereferences the committed dictionary (ADR 0038): a derived
    // Showable resolves to the structural recipe...
    assert_runs(
        b"struct Point {\n\tlet x: Int\n\tlet y: Int\n}\nfunc render<T: Showable>(value: T) -> String {\n\tvalue.show()\n}\nprint(render(value: Point(x: 1, y: 2)))\n",
        &[],
        b"Point(x: 1, y: 2)\n",
    );
    // ...and a requirement without a declared witness resolves to the
    // protocol's default body.
    assert_runs(
        b"func differ<T: Equatable>(a: T, b: T) -> Bool {\n\ta.notEquals(b)\n}\nprint(differ(a: 1, b: 2))\nprint(differ(a: 3, b: 3))\n",
        &[],
        b"true\nfalse\n",
    );
}

#[test]
fn check_accepts_refined_protocol_dispatch() {
    // `T: P` where `protocol P: Q` supplies Q's dictionary too — the
    // rigid constraint set expands through protocol supers.
    assert_checks(
        b"protocol Q {\n\tfunc q() -> Int\n}\nprotocol P: Q {\n\tfunc p() -> Int\n}\nfunc f<T: P>(x: T) -> Int { x.q() }\nstruct S {\n\tinit() { self }\n}\nextend S: P {\n\tfunc q() -> Int { 1 }\n\tfunc p() -> Int { 2 }\n}\nprint(f(x: S()))\n",
    );
}

#[test]
fn check_accepts_owner_param_dictionaries() {
    // A struct's owner bound serves its method bodies, declared inline...
    assert_checks(
        b"struct Box<T: Showable> {\n\tlet value: T\n\tinit(value: T) {\n\t\tself.value = value\n\t\tself\n\t}\n\tfunc render() -> String {\n\t\tself.value.show()\n\t}\n}\nprint(Box(value: 42).render())\n",
    );
    // ...via a where clause...
    assert_checks(
        b"struct Box<T> where T: Showable {\n\tlet value: T\n\tinit(value: T) {\n\t\tself.value = value\n\t\tself\n\t}\n\tfunc render() -> String {\n\t\tself.value.show()\n\t}\n}\nprint(Box(value: 42).render())\n",
    );
    // ...and in inherent extend members.
    assert_checks(
        b"struct Box<T: Showable> {\n\tlet value: T\n\tinit(value: T) {\n\t\tself.value = value\n\t\tself\n\t}\n}\nextend Box {\n\tfunc render() -> String {\n\t\tself.value.show()\n\t}\n}\nprint(Box(value: 42).render())\n",
    );
}

#[test]
fn check_accepts_protocol_default_bodies() {
    // A default body's rigid `Self` dispatches its own protocol's
    // requirements through the frame's dictionary.
    assert_checks(
        b"protocol P {\n\tfunc p() -> Int\n}\nextend P {\n\tfunc twice() -> Int {\n\t\tself.p() + self.p()\n\t}\n}\nstruct S {\n\tinit() { self }\n}\nextend S: P {\n\tfunc p() -> Int { 3 }\n}\nprint(S().twice())\n",
    );
}

#[test]
fn check_accepts_generic_values_in_handler_clauses() {
    // Handler clauses inherit the enclosing frame's witnesses and
    // dictionaries through their environments, like ordinary closures.
    assert_checks(
        b"effect 'emit(x: Int) -> ()\nfunc run<T: Showable>(v: T) -> () {\n\t#handle 'emit { n in\n\t\tprint(v.show())\n\t\t'continue ()\n\t}\n\t'emit(x: 1)\n}\nrun(v: 42)\n",
    );
    // Ownership witnesses too: a clause that consumes a captured rigid
    // releases it through the inherited drop witness.
    assert_checks(
        b"effect 'ping() -> ()\nfunc hold<T>(consume v: T) -> () {\n\t#handle 'ping {\n\t\tlet w = v\n\t\t'continue ()\n\t}\n\t'ping()\n}\nhold(v: \"a\" + \"b\")\n",
    );
}

#[test]
fn run_resumes_from_inside_a_loop_in_a_handler_clause() {
    // `'continue` is a frame return from the clause, legal at any loop
    // depth: the loop searches for an answer and resumes with it.
    assert_runs(
        b"effect 'ask() -> Int\n#handle 'ask {\n\tlet i = 0\n\tloop i < 10 {\n\t\tif i == 7 {\n\t\t\t'continue i\n\t\t}\n\t\ti = i + 1\n\t}\n\t'continue 0\n}\nprint('ask())\n",
        &[],
        b"7\n",
    );
}

#[test]
fn run_passes_owned_payloads_through_generic_effects() {
    // EFF-03: a payload in a directly-generic position travels as an
    // existential-shaped [drop, retain] package, so one clause body
    // serves every instantiation — releasing an unconsumed payload…
    assert_runs(
        b"effect 'give<T>(value: T) -> ()\n#handle 'give { v in 'continue () }\nfunc send(consume s: String) 'give -> Void {\n\t'give(value: s)\n}\nsend(s: \"a\" + \"b\")\nprint(1)\n",
        &[],
        b"1\n",
    );
    // …resuming with it (the perform site unwraps the package)…
    assert_runs(
        b"effect 'echo<T>(value: T) -> T\n#handle 'echo { v in 'continue v }\nfunc round(consume s: String) 'echo -> String {\n\t'echo(value: s)\n}\nprint(round(s: \"hi\" + \"!\"))\n",
        &[],
        b"hi!\n",
    );
    // …and discontinuing past it (abort cleanup drops the package).
    assert_runs(
        b"effect 'toss<T>(value: T) -> Never\nfunc risky() -> Int {\n\t#handle 'toss { v in -1 }\n\tlet s = \"a\" + \"b\"\n\t'toss(value: s)\n}\nprint(risky())\n",
        &[],
        b"-1\n",
    );
    // Copy instantiations use the same packaging convention.
    assert_runs(
        b"effect 'echo<T>(value: T) -> T\n#handle 'echo { v in 'continue v }\nprint('echo(value: 41) + 1)\n",
        &[],
        b"42\n",
    );
    // Nested positions hold native values; the clause's structural glue
    // reaches rigid leaves through the perform site's witnesses.
    assert_runs(
        b"effect 'pair<T>(value: (Int, T)) -> ()\n#handle 'pair { v in 'continue () }\n'pair(value: (1, 2))\nprint(3)\n",
        &[],
        b"3\n",
    );
    assert_runs(
        b"effect 'pair<T>(value: (Int, T)) -> ()\n#handle 'pair { v in 'continue () }\nlet s = \"a\" + \"b\"\n'pair(value: (1, s))\nprint(3)\n",
        &[],
        b"3\n",
    );
    // …including through a compound type's own teardown (Array's deinit
    // instantiated at the rigid element receives the same witnesses)…
    assert_runs(
        b"effect 'batch<T>(values: Array<T>) -> ()\n#handle 'batch { vs in 'continue () }\nlet xs: Array<String> = [\"a\" + \"b\", \"c\" + \"d\"]\n'batch(values: xs)\nprint(4)\n",
        &[],
        b"4\n",
    );
    // …and through enum payload glue.
    assert_runs(
        b"enum Wrap<T> {\n\tcase full(T)\n\tcase empty\n}\neffect 'opt<T>(value: Wrap<T>) -> ()\n#handle 'opt { v in 'continue () }\n'opt(value: Wrap.full(\"a\" + \"b\"))\nprint(5)\n",
        &[],
        b"5\n",
    );
    // A nested payload continued back returns natively.
    assert_runs(
        b"effect 'swap<T>(value: (Int, T)) -> (Int, T)\n#handle 'swap { v in 'continue v }\nlet back = 'swap(value: (7, \"x\" + \"y\"))\nprint(back.0)\nprint(back.1)\n",
        &[],
        b"7\nxy\n",
    );
    // A clause handing its rigid value to a generic function threads the
    // witnesses through that instance's hidden parameters.
    assert_runs(
        b"effect 'sink<T>(value: T) -> ()\nfunc discard<X>(consume x: X) -> Void {\n}\n#handle 'sink { v in\n\tdiscard(x: v)\n\t'continue ()\n}\n'sink(value: \"a\" + \"b\")\nprint(1)\n",
        &[],
        b"1\n",
    );
    // A clause re-performing with its rigid value forwards its own
    // witnesses to the next handler out.
    assert_runs(
        b"effect 'inner<T>(value: T) -> ()\neffect 'outer<T>(value: T) -> ()\n#handle 'inner { v in 'continue () }\n#handle 'outer { v in\n\t'inner(value: v)\n\t'continue ()\n}\n'outer(value: \"a\" + \"b\")\nprint(2)\n",
        &[],
        b"2\n",
    );
    // A compound rigid payload re-performs through glue closures that
    // capture the inner witnesses.
    assert_runs(
        b"effect 'batch<T>(values: Array<T>) -> ()\neffect 'again<U>(value: U) -> ()\n#handle 'again { u in 'continue () }\n#handle 'batch { vs in\n\t'again(value: vs)\n\t'continue ()\n}\nlet xs: Array<String> = [\"a\" + \"b\"]\n'batch(values: xs)\nprint(3)\n",
        &[],
        b"3\n",
    );
}

#[test]
fn run_dispatches_overloaded_requirements_through_witness_tables() {
    // ADR 0041: same-base requirement overloads get distinct witness-table
    // slots; generic and existential dispatch select by written labels.
    assert_runs(
        b"protocol Tagger {\n\tfunc tag(short flag: Bool) -> Int\n\tfunc tag(long count: Int) -> Int\n}\nstruct S {}\nextend S: Tagger {\n\tfunc tag(short flag: Bool) -> Int {\n\t\tif flag { 1 } else { 2 }\n\t}\n\n\tfunc tag(long count: Int) -> Int {\n\t\tcount + 10\n\t}\n}\nfunc generic<T: Tagger>(x: T) -> Int {\n\tx.tag(short: true) + x.tag(long: 5)\n}\nprint(generic(x: S()))\nlet e: any Tagger = S()\nprint(e.tag(short: false) + e.tag(long: 1))\n",
        &[],
        b"16\n13\n",
    );
}

#[test]
fn run_dispatches_constrained_generic_effects() {
    // A constrained effect generic carries its conformance dictionary
    // alongside [drop, retain]: one clause body calls requirements on
    // every instantiation…
    assert_runs(
        b"effect 'show<T: Showable>(value: T) -> ()\n#handle 'show { v in\n\tprint(v.show())\n\t'continue ()\n}\n'show(value: 42)\n'show(value: \"a\" + \"b\")\n",
        &[],
        b"42\nab\n",
    );
    // …and packs the rigid value into an existential from the same
    // dictionary.
    assert_runs(
        b"effect 'show<T: Showable>(value: T) -> ()\n#handle 'show { v in\n\tlet s: any Showable = v\n\tprint(s.show())\n\t'continue ()\n}\n'show(value: 42)\n",
        &[],
        b"42\n",
    );
    // A `mut func` requirement returns (result, final self); the rigid
    // dispatch writes the evolved receiver back through the dictionary.
    assert_runs(
        b"protocol Counter {\n\tmut func bump() -> Int\n}\nstruct C {\n\tlet n: Int\n\tinit(n: Int) {\n\t\tself.n = n\n\t\tself\n\t}\n}\nextend C: Counter {\n\tmut func bump() -> Int {\n\t\tself.n = self.n + 1\n\t\tself.n\n\t}\n}\neffect 'tick<T: Counter>(value: T) -> ()\n#handle 'tick { v in\n\tprint(v.bump())\n\tprint(v.bump())\n\t'continue ()\n}\n'tick(value: C(n: 0))\n",
        &[],
        b"1\n2\n",
    );
    // An owned scrutinee is consumed by destructuring: the escaping bind
    // owns the payload and the shell drops nothing (no double free), and
    // a wildcard arm still releases the payload (no leak).
    assert_runs(
        b"enum Work {\n\tcase text(String)\n\tcase gap\n}\nextend Work: CheapClone {}\nfunc take(consume item: Work) -> String {\n\tmatch item {\n\t\t.text(piece) -> piece,\n\t\t_ -> \"\".to_string()\n\t}\n}\nprint(take(item: Work.text(\"a\" + \"b\")))\nprint(take(item: Work.gap).byte_count)\n",
        &[],
        b"ab\n0\n",
    );
    // A `mut` parameter accepts an unmarked place argument (the checker
    // coerces implicitly); the evolved value still writes back.
    assert_runs(
        b"func add_one(mut xs: [Int]) -> Void {\n\txs.push(1)\n}\nfunc run() -> Int {\n\tlet xs: [Int] = []\n\tadd_one(xs: xs)\n\tadd_one(xs: xs)\n\txs.count\n}\nprint(run())\n",
        &[],
        b"2\n",
    );
    // A `mut` receiver reached through a projection writes back through
    // the whole place chain (self.comments.push(…) evolves the field).
    assert_runs(
        b"struct Holder {\n\tlet items: [Int]\n\tinit() {\n\t\tself.items = []\n\t}\n\tmut func add(n: Int) -> Void {\n\t\tself.items.push(n)\n\t}\n}\nlet h = Holder()\nh.add(n: 1)\nh.add(n: 2)\nprint(h.items.count)\n",
        &[],
        b"2\n",
    );
    // `mut` parameters and a `mut` receiver on one requirement land in
    // callee order: (result, final self, final mut values…).
    assert_runs(
        b"protocol Counter {\n\tmut func bump_by(mut amount: Int) -> Int\n}\nstruct C {\n\tlet n: Int\n\tinit(n: Int) {\n\t\tself.n = n\n\t\tself\n\t}\n}\nextend C: Counter {\n\tmut func bump_by(mut amount: Int) -> Int {\n\t\tself.n = self.n + amount\n\t\tamount = amount * 2\n\t\tself.n\n\t}\n}\neffect 'acc<T: Counter>(value: T) -> ()\n#handle 'acc { v in\n\tlet step = 3\n\tprint(v.bump_by(amount: mut step))\n\tprint(step)\n\tprint(v.bump_by(amount: mut step))\n\tprint(step)\n\t'continue ()\n}\n'acc(value: C(n: 0))\n",
        &[],
        b"3\n6\n9\n12\n",
    );
    // A closure created inside the clause inherits the witnesses through
    // its environment.
    assert_runs(
        b"effect 'hold<T>(value: T) -> ()\nfunc discard<X>(consume x: X) -> Void {\n}\n#handle 'hold { v in\n\tlet run = func(consume x: String) -> Void {\n\t}\n\trun(\"q\" + \"r\")\n\tdiscard(x: v)\n\t'continue ()\n}\n'hold(value: \"a\" + \"b\")\nprint(1)\n",
        &[],
        b"1\n",
    );
}

#[test]
fn run_rejects_escaping_borrowed_returns() {
    // CHG-04: a borrowed return may not loan out the frame's own value.
    let output = run_source(
        b"func f() -> &String {\n\tlet s = \"x\" + \"y\"\n\ts\n}\nf().byte_count\n",
        &[],
    );
    assert!(!output.status.success());
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(stderr.contains("cannot return a borrow"), "{stderr}");
}

#[test]
fn run_enforces_strict_linear_consumption() {
    // OWN-03: every finite exit consumes a linear value exactly once.
    assert_runs(
        b"enum Token 'linear {\n\tcase active(Int)\n}\nfunc consume_token(consume t: Token) -> Int {\n\tmatch t {\n\t\t.active(n) -> n\n\t}\n}\nfunc run_it() -> Int {\n\tlet t = Token.active(42)\n\tconsume_token(t: t)\n}\nrun_it()\n",
        &[],
        b"42\n",
    );
    let output = run_source(
        b"enum Token 'linear {\n\tcase active(Int)\n}\nfunc run_it() -> Int {\n\tlet t = Token.active(1)\n\t0\n}\nrun_it()\n",
        &[],
    );
    assert!(!output.status.success());
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("linear") && stderr.contains("consumed"),
        "{stderr}"
    );
}

#[test]
fn postfix_bang_force_unwraps_optional_and_result() {
    assert_runs(
        b"let optional: Int? = .some(41)\nlet result: Result<Int, String> = .ok(42)\nprint(optional!)\nprint(result!)\n",
        &[],
        b"41\n42\n",
    );
}

#[test]
fn postfix_bang_panics_on_the_second_variant() {
    let output = run_source(b"let value: Int? = .none\nvalue!\n", &[]);
    assert!(!output.status.success());
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(stderr.contains("reached unreachable"), "{stderr}");

    assert_runs(
        b"func recover() -> Int {\n\t#handle 'panic { message in 7 }\n\tlet value: Result<Int, String> = .error(\"bad\")\n\tvalue!\n}\nprint(recover())\n",
        &[],
        b"7\n",
    );
}

#[test]
fn run_can_handle_an_unreachable_panic() {
    assert_runs(
        b"func recover() -> Int {\n\t#handle 'panic { message in 42 }\n\tunreachable\n}\nprint(recover())\n",
        &[],
        b"42\n",
    );
}

#[test]
fn run_reports_an_unhandled_unreachable_panic() {
    let output = run_source(b"unreachable\n", &[]);
    assert!(!output.status.success());
    assert!(output.stdout.is_empty());
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(stderr.contains("reached unreachable"), "{stderr}");
}

#[test]
fn run_reports_a_clean_division_by_zero_trap() {
    let output = run_source(b"let zero = 0\n1 / zero\n", &[]);
    assert!(!output.status.success());
    assert!(output.stdout.is_empty());
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(stderr.contains("division by zero"), "{stderr}");
    assert!(stderr.contains("0 live allocations"), "{stderr}");
    assert!(stderr.contains("0 live 'heap objects"), "{stderr}");
}

#[test]
fn run_reports_an_out_of_range_array_read() {
    // Without the bounds check the raw `gep` walks off the buffer and the
    // failure surfaces as the VM's memory guard ("load out of bounds"),
    // which names neither the array nor the index.
    let output = run_source(b"let items = [1, 2, 3]\nprint(items[7])\n", &[]);
    assert!(!output.status.success());
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(stderr.contains("array index out of bounds"), "{stderr}");

    let output = run_source(b"let empty: [Int] = []\nprint(empty[0])\n", &[]);
    assert!(!output.status.success());
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(stderr.contains("array index out of bounds"), "{stderr}");

    let output = run_source(b"let items = [1, 2, 3]\nprint(items[0 - 1])\n", &[]);
    assert!(!output.status.success());
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(stderr.contains("array index out of bounds"), "{stderr}");
}

#[test]
fn run_reports_an_out_of_range_array_write() {
    let output = run_source(b"let items = [1, 2, 3]\nitems[7] = 4\n", &[]);
    assert!(!output.status.success());
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(stderr.contains("array index out of bounds"), "{stderr}");
}

#[test]
fn run_reports_an_out_of_range_array_swap() {
    let output = run_source(b"let items = [1, 2, 3]\nitems.swap(i: 0, j: 9)\n", &[]);
    assert!(!output.status.success());
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(stderr.contains("array index out of bounds"), "{stderr}");
}

#[test]
fn an_array_bounds_panic_is_handleable() {
    // Panic is an ordinary effect, so a bounds failure routes through a
    // user handler before reaching the host's abort fallback.
    assert_runs(
        b"func lookup() -> Int {\n\t#handle 'panic { message in 0 }\n\tlet items = [1, 2, 3]\n\treturn items[7]\n}\nprint(lookup())\n",
        &[],
        b"0\n",
    );
}

#[test]
fn run_executes_existential_values() {
    // D1: pack, dynamic witness dispatch, and payload teardown through
    // the fixed-slot witness table.
    assert_runs(b"let s: any Showable = 42\nprint(s.show())\n", &[], b"42\n");
    assert_runs(
        b"let items: [any Showable] = [1, true]\nprint(items.get(0).show())\nprint(items.get(1).show())\n",
        &[],
        b"1\ntrue\n",
    );
    assert_runs(
        b"let s: any Showable = \"hey\" + \"!\"\nprint(s.show())\n",
        &[],
        b"hey!\n",
    );
    // `mut` parameters on existential requirements write back too.
    assert_runs(
        b"protocol Adder {\n\tfunc add_into(mut total: Int) -> Void\n}\nstruct A {\n\tlet n: Int\n\tinit(n: Int) {\n\t\tself.n = n\n\t\tself\n\t}\n}\nextend A: Adder {\n\tfunc add_into(mut total: Int) -> Void {\n\t\ttotal = total + self.n\n\t}\n}\nlet a: any Adder = A(n: 5)\nlet sum = 0\na.add_into(total: mut sum)\na.add_into(total: mut sum)\nprint(sum)\n",
        &[],
        b"10\n",
    );
    // Constructions coerce directly into existentials, and `mut func`
    // requirements evolve the payload behind the same witness table.
    assert_runs(
        b"protocol Counter {\n\tmut func bump() -> Int\n}\nstruct C {\n\tlet n: Int\n\tinit(n: Int) {\n\t\tself.n = n\n\t\tself\n\t}\n}\nextend C: Counter {\n\tmut func bump() -> Int {\n\t\tself.n = self.n + 1\n\t\tself.n\n\t}\n}\nlet a: any Counter = C(n: 0)\nprint(a.bump())\nprint(a.bump())\n",
        &[],
        b"1\n2\n",
    );
}

#[test]
fn run_rejects_linear_globals() {
    // A named language rule (the global twin of the borrowed-global
    // rule): a linear value's exactly-once consumption cannot be proven
    // across program-lifetime storage, so linear values stay in function
    // scopes. Rejected where the binding is written, not at teardown.
    let output = run_source(
        b"enum Token 'linear {\n\tcase active(Int)\n}\nlet t = Token.active(1)\nprint(0)\n",
        &[],
    );
    assert!(!output.status.success());
    assert!(output.stdout.is_empty());
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("a linear value cannot be stored in a global binding"),
        "expected the linear-global rule, got: {stderr}"
    );
    // The idiomatic form the diagnostic points to still runs.
    assert_runs(
        b"enum Token 'linear {\n\
          \tcase active(Int)\n\
          }\n\
          func f() -> Int {\n\
          \tlet t = Token.active(41)\n\
          \tmatch t {\n\
          \t\t.active(n) -> n\n\
          \t}\n\
          }\n\
          print(f())\n",
        &[],
        b"41\n",
    );
}

#[test]
fn every_parity_program_has_a_frozen_expected_stdout() {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"));
    let sources: BTreeSet<_> = std::fs::read_dir(root.join("tests/programs"))
        .expect("read parity source directory")
        .map(|entry| entry.expect("read parity source entry").path())
        .filter(|path| path.extension().is_some_and(|extension| extension == "tlk"))
        .map(|path| {
            path.file_stem()
                .expect("parity source file stem")
                .to_owned()
        })
        .collect();
    let expected: BTreeSet<_> = std::fs::read_dir(root.join("tests/parity/programs"))
        .expect("read parity expected-output directory")
        .map(|entry| entry.expect("read parity expected-output entry").path())
        .filter(|path| {
            path.extension()
                .is_some_and(|extension| extension == "stdout")
        })
        .map(|path| {
            path.file_stem()
                .expect("parity expected-output file stem")
                .to_owned()
        })
        .collect();

    assert_eq!(sources, expected);
}

#[test]
fn reviewed_handlers_output_uses_talk_result_rendering() {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"));
    let baseline = std::fs::read(root.join("tests/parity/programs/handlers.stdout"))
        .expect("read baseline handlers output");
    let replacement = std::fs::read(root.join("tests/parity/reviewed-programs/handlers.stdout"))
        .expect("read reviewed handlers output");
    assert_eq!(baseline, b"10\nhandled: boom\nI64(0)\n");
    assert_eq!(replacement, b"10\nhandled: boom\n0\n");
}

#[test]
fn baseline_test_disposition_inventory_is_complete() {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"));
    let inventory =
        std::fs::read_to_string(root.join("tests/parity/baseline-test-disposition.tsv"))
            .expect("read baseline test disposition inventory");
    let ledger = std::fs::read_to_string(root.join("docs/backend-parity-ledger.md"))
        .expect("read backend parity ledger");
    let mut lines = inventory.lines();
    assert_eq!(
        lines.next(),
        Some("suite\ttest\tclass\tledger_rows\tdisposition")
    );

    let mut tests = BTreeSet::new();
    let mut flow = 0;
    let mut lower = 0;
    let mut vm = 0;
    for line in lines {
        let columns: Vec<_> = line.split('\t').collect();
        assert_eq!(columns.len(), 5, "invalid disposition row: {line}");
        let [suite, test, classification, rows, disposition] = columns.as_slice() else {
            unreachable!("column count checked above");
        };
        assert!(
            tests.insert((*suite, *test)),
            "duplicate baseline test disposition: {suite}/{test}"
        );
        match *suite {
            "F" => flow += 1,
            "L" => lower += 1,
            "V" => vm += 1,
            _ => panic!("unknown baseline suite code: {suite}"),
        }
        match (*classification, *disposition) {
            ("R", "B") | ("I", "FS" | "LS" | "EF") => {}
            _ => panic!(
                "invalid classification/disposition for {suite}/{test}: {classification}/{disposition}"
            ),
        }
        assert!(!rows.is_empty(), "missing ledger rows for {suite}/{test}");
        for row in rows.split(',') {
            assert!(
                ledger.contains(&format!("| {row} |")),
                "unknown parity ledger row {row} for {suite}/{test}"
            );
        }
    }

    assert_eq!((flow, lower, vm), (151, 53, 293));
    assert_eq!(tests.len(), 497);
}

#[test]
fn parity_programs_still_pass_frontend_checking() {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"));
    let mut sources: Vec<_> = std::fs::read_dir(root.join("tests/programs"))
        .expect("read parity source directory")
        .map(|entry| entry.expect("read parity source entry").path())
        .filter(|path| path.extension().is_some_and(|extension| extension == "tlk"))
        .collect();
    sources.sort();

    for_each_corpus_case(&sources, |source| {
        let output = Command::new(env!("CARGO_BIN_EXE_talk"))
            .arg("check")
            .arg(source)
            .current_dir(root)
            .output()
            .expect("run `talk check` for parity program");
        assert!(
            output.status.success(),
            "{} failed frontend checking:\nstdout:\n{}\nstderr:\n{}",
            source.display(),
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr),
        );
    });
}

/// ADR 0045: a body demanding itself at an ever-larger instantiation must
/// reject rather than diverge. The mutual form rejects in the checker
/// today (the in-group reference checks against the definition's rigid
/// parameters). The DIRECT self-call form does not yet: its `T ~ Wrap<T>`
/// obligation defers through unify's bare-param arm and is lost, so the
/// call silently reuses the enclosing instance — an open checker bug
/// tracked in the ADR 0045 notes. `INSTANTIATION_DEPTH_LIMIT` in
/// `mir::demand` backstops any route that does demand growing instances.
/// ADR 0045 rule 2: a type whose layout contains itself must live
/// behind a reference, and `'heap` is how the declaration says so.
/// Recursion through an array does NOT count — elements already live
/// behind `Storage`'s pointer — which is what keeps the frontend's own
/// AST enums unannotated.
#[test]
fn recursive_types_require_heap() {
    let output = check_source(
        b"enum Tree {\n\
          \tcase leaf(Int)\n\
          \tcase node(Tree, Tree)\n\
          }\n\
          func main() {}\n",
    );
    assert!(!output.status.success());
    let printed = format!(
        "{}{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(
        printed.contains("must be declared 'heap"),
        "diagnostics:\n{printed}"
    );

    // Array-mediated recursion needs no marker...
    assert_checks(
        b"enum Node {\n\
          \tcase leaf(Int)\n\
          \tcase branch([Node])\n\
          }\n\
          func main() {}\n",
    );
    // ...and a marked recursive enum builds and runs.
    assert_runs(
        b"enum Tree 'heap {\n\
          \tcase leaf(Int)\n\
          \tcase node(Tree, Tree)\n\
          }\n\
          func weigh(t: Tree) -> Int {\n\
          \tmatch t {\n\
          \t\t.leaf(v) -> v,\n\
          \t\t.node(a, b) -> weigh(t: a) + weigh(t: b)\n\
          \t}\n\
          }\n\
          func main() {\n\
          \tprint(weigh(t: Tree.node(Tree.leaf(1), Tree.leaf(2))))\n\
          }\n",
        &[],
        b"3\n",
    );
}

/// The direct form: the self-call's `T ~ Wrap<T>` obligation defers
/// through unify's bare-param arm (a given could in principle prove it),
/// and an undischarged deferred equation must be reported, not dropped —
/// otherwise the call compiles against a type-wrong shared instance.
#[test]
fn direct_polymorphic_recursion_rejects_in_the_checker() {
    let output = run_source(
        b"struct Wrap<T> {\n\
          \tlet value: T\n\
          }\n\
          func f<T>(x: T) -> Int {\n\
          \tf(x: Wrap(value: x))\n\
          }\n\
          func main() {\n\
          \tprint(f(x: 1))\n\
          }\n",
        &[],
    );
    assert!(!output.status.success());
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("mismatch") || stderr.contains("Mismatch"),
        "expected a type mismatch rejection, got:\n{stderr}"
    );
}

#[test]
fn mutual_polymorphic_recursion_rejects_in_the_checker() {
    let output = run_source(
        b"struct Wrap<T> {\n\
          \tlet value: T\n\
          }\n\
          func f<T>(x: T) -> Int {\n\
          \tg(x: x)\n\
          }\n\
          func g<T>(x: T) -> Int {\n\
          \tf(x: Wrap(value: x))\n\
          }\n\
          func main() {\n\
          \tprint(f(x: 1))\n\
          }\n",
        &[],
    );
    assert!(!output.status.success());
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("recursive definition"),
        "expected the recursive-definition rejection, got:\n{stderr}"
    );
}

/// ADR 0045: an enum constructed with a payload parameter left unbound
/// (`Result.error(99)` never pins `Success`) still runs, with the free
/// parameter grounded so the executed instance is concrete — no executed
/// aggregate may carry an opaque layout.
#[test]
fn unbound_enum_payload_params_ground_to_a_concrete_layout() {
    let source = b"func main() {\n\
                   \tlet r = Result.error(99)\n\
                   \tprint(r.is_ok())\n\
                   }\n";
    assert_runs(source, &[], b"false\n");

    let mut child = Command::new(env!("CARGO_BIN_EXE_talk"))
        .arg("mir")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("run `talk mir`");
    child
        .stdin
        .take()
        .expect("piped stdin")
        .write_all(source)
        .expect("write Talk source");
    let output = child.wait_with_output().expect("read mir output");
    assert!(
        output.status.success(),
        "stderr:\n{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let dump = String::from_utf8_lossy(&output.stdout);
    assert!(
        !dump.contains(": opaque"),
        "an executed instruction carries an opaque layout:\n{dump}"
    );
}
