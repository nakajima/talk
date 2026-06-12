#[cfg(test)]
pub mod tests {
    use crate::compiling::driver::{Driver, DriverConfig, Source};
    use crate::lambda_g::eval::EvalValue;
    use crate::vm::interp::Value;

    /// The same program runs on the reference evaluator (a direct
    /// transcription of the paper's semantics — our trusted baseline) and
    /// on the scheduled bytecode VM; results must agree. This is the
    /// safety net for the one novel composition in the backend — λ_G →
    /// nesting-tree schedule → bytecode (plan's flagged seam #2).
    fn run_on_both_engines(code: &'static str) -> Value {
        let driver = Driver::new(vec![Source::from(code)], DriverConfig::new("VmTest"));
        let typed = driver
            .parse()
            .expect("parse")
            .resolve_names()
            .expect("resolve")
            .type_check();
        assert!(!typed.has_errors(), "type errors: {:?}", typed.diagnostics());
        let mut lowered = typed.lower();
        assert!(
            lowered.phase.diagnostics.is_empty(),
            "lowering: {:?}",
            lowered.phase.diagnostics
        );
        // Post-lowering verifier: T-Prog + WF over the whole program
        // (LLVM-verifier spirit — Lattner & Adve, CGO 2004).
        let verified = lowered.phase.program.verify();
        assert!(verified.is_ok(), "verifier: {:?}", verified.err());

        // VM first: the substitution-based evaluator mutates the program.
        let vm_value = lowered.run_vm().expect("vm");
        let evaluator_value = lowered.eval_for_tests().expect("evaluator");

        let matches = match (&evaluator_value, &vm_value) {
            (EvalValue::I64(a), Value::I64(b)) => a == b,
            (EvalValue::F64(a), Value::F64(b)) => a == b,
            (EvalValue::Bool(a), Value::Bool(b)) => a == b,
            (EvalValue::Void, Value::Void) => true,
            _ => false,
        };
        assert!(
            matches,
            "evaluator {evaluator_value:?} != vm {vm_value:?}"
        );
        vm_value
    }

    #[test]
    fn vm_matches_evaluator_on_arithmetic() {
        assert_eq!(run_on_both_engines("2 + 3 * 3"), Value::I64(11));
    }

    #[test]
    fn vm_matches_evaluator_on_branches() {
        assert_eq!(run_on_both_engines("if 2 > 3 { 1 } else { 2 }"), Value::I64(2));
    }

    #[test]
    fn vm_matches_evaluator_on_locals() {
        assert_eq!(run_on_both_engines("let a = 4\nlet b = a + 1\nb * 2"), Value::I64(10));
    }

    #[test]
    fn vm_matches_evaluator_on_calls() {
        assert_eq!(
            run_on_both_engines("func double(x: Int) -> Int { x * 2 }\ndouble(21)"),
            Value::I64(42)
        );
    }

    #[test]
    fn vm_matches_evaluator_on_monomorphization() {
        assert_eq!(
            run_on_both_engines("func identity(x) { x }\nidentity(123)\nidentity(1.5)"),
            Value::F64(1.5)
        );
    }

    #[test]
    fn vm_matches_evaluator_on_fib() {
        // Deeper than the evaluator can comfortably go is fine on the VM;
        // when both engines run we stay modest.
        assert_eq!(
            run_on_both_engines(
                "func fib(n) {\n\tif n <= 1 { return n }\n\treturn fib(n - 2) + fib(n - 1)\n}\nfib(12)"
            ),
            Value::I64(144)
        );
    }

    #[test]
    fn vm_matches_evaluator_on_loops_and_cells() {
        assert_eq!(
            run_on_both_engines(
                "func sum() -> Int {\n\tlet total = 0\n\tlet i = 0\n\tloop i < 10 {\n\t\ttotal = total + i\n\t\ti = i + 1\n\t}\n\ttotal\n}\nsum()"
            ),
            Value::I64(45)
        );
    }

    /// Both engines, including captured stdout (the M3 surface: records,
    /// strings, io_write).
    fn run_on_both_engines_io(code: &'static str) -> (Value, String) {
        let driver = Driver::new(vec![Source::from(code)], DriverConfig::new("VmTest"));
        let typed = driver
            .parse()
            .expect("parse")
            .resolve_names()
            .expect("resolve")
            .type_check();
        assert!(!typed.has_errors(), "type errors: {:?}", typed.diagnostics());
        let mut lowered = typed.lower();
        assert!(
            lowered.phase.diagnostics.is_empty(),
            "lowering: {:?}",
            lowered.phase.diagnostics
        );
        let verified = lowered.phase.program.verify();
        assert!(verified.is_ok(), "verifier: {:?}", verified.err());

        let (vm_value, vm_out) = lowered.run_vm_with_output().expect("vm");
        let (evaluator_value, evaluator_out) = lowered.eval_with_output().expect("evaluator");

        let matches = match (&evaluator_value, &vm_value) {
            (EvalValue::I64(a), Value::I64(b)) => a == b,
            (EvalValue::F64(a), Value::F64(b)) => a == b,
            (EvalValue::Bool(a), Value::Bool(b)) => a == b,
            (EvalValue::Void, Value::Void) => true,
            // Aggregates: stdout agreement is the assertion that matters.
            (EvalValue::Record(..), Value::Record(..)) => true,
            _ => false,
        };
        assert!(
            matches,
            "evaluator {evaluator_value:?} != vm {vm_value:?}"
        );
        assert_eq!(evaluator_out, vm_out, "stdout diverged");
        (vm_value, vm_out)
    }

    #[test]
    fn vm_matches_evaluator_on_memberwise_struct() {
        let (value, _) = run_on_both_engines_io(
            "struct Point {\n\tlet x: Int\n\tlet y: Int\n}\nlet p = Point(x: 3, y: 4)\np.x + p.y",
        );
        assert_eq!(value, Value::I64(7));
    }

    #[test]
    fn vm_matches_evaluator_on_explicit_init() {
        let (value, _) = run_on_both_engines_io(
            "struct Dog {\n\tlet age: Int\n\tlet count: Int\n\n\tinit(age: Int) {\n\t\tself.age = age\n\t\tself.count = 0\n\t\tself\n\t}\n}\nDog(age: 123).age",
        );
        assert_eq!(value, Value::I64(123));
    }

    #[test]
    fn vm_matches_evaluator_on_struct_methods() {
        let (value, _) = run_on_both_engines_io(
            "struct Counter {\n\tlet n: Int\n\n\tfunc get() -> Int { self.n }\n\tfunc plus(extra: Int) -> Int { self.n + extra }\n}\nlet c = Counter(n: 40)\nc.get() + c.plus(1)",
        );
        assert_eq!(value, Value::I64(81));
    }

    #[test]
    fn vm_matches_evaluator_on_mutating_method_writeback() {
        // Value semantics + inout self (Racordon et al., JOT 2022): bump's
        // self mutation writes back into the caller's binding.
        let (value, _) = run_on_both_engines_io(
            "struct Counter {\n\tlet n: Int\n\n\tfunc bump() {\n\t\tself.n = self.n + 1\n\t}\n}\nlet c = Counter(n: 1)\nc.bump()\nc.bump()\nc.n",
        );
        assert_eq!(value, Value::I64(3));
    }

    #[test]
    fn vm_matches_evaluator_on_hello_world() {
        let (_, out) = run_on_both_engines_io("print(\"hello world\")");
        assert_eq!(out, "hello world\n");
    }

    #[test]
    fn vm_matches_evaluator_on_string_concat() {
        let (_, out) = run_on_both_engines_io("print(\"hi \" + \"there\")");
        assert_eq!(out, "hi there\n");
    }

    #[test]
    fn vm_matches_evaluator_on_print_int() {
        // Pulls in Int: Showable → _digit → match on Int literals.
        let (_, out) = run_on_both_engines_io("print(417)");
        assert_eq!(out, "417\n");
    }

    #[test]
    fn vm_matches_evaluator_on_struct_example() {
        // examples/Strings.tlk in miniature: fields + concat + print.
        let (_, out) = run_on_both_engines_io(
            "struct Person {\n\tlet firstName: String\n\tlet lastName: String\n\n\tfunc greet() {\n\t\tprint(\"hi i'm \" + self.firstName + \" \" + self.lastName)\n\t}\n}\nPerson(firstName: \"Pat\", lastName: \"N\").greet()",
        );
        assert_eq!(out, "hi i'm Pat N\n");
    }

    // ----- M4: enums, decision trees, Optional ------------------------------

    #[test]
    fn vm_matches_evaluator_on_enum_match_dispatch() {
        let (value, _) = run_on_both_engines_io(
            "enum Color {\n\tcase red\n\tcase green\n\tcase blue\n}\nlet c = Color.green\nmatch c {\n\t.red -> 1,\n\t.green -> 2,\n\t.blue -> 3\n}",
        );
        assert_eq!(value, Value::I64(2));
    }

    #[test]
    fn vm_matches_evaluator_on_enum_payload_binds() {
        let (value, _) = run_on_both_engines_io(
            "enum Maybe {\n\tcase definitely(Int)\n\tcase nope\n}\nlet m = Maybe.definitely(41)\nmatch m {\n\t.definitely(x) -> x + 1,\n\t.nope -> 0\n}",
        );
        assert_eq!(value, Value::I64(42));
    }

    #[test]
    fn vm_matches_evaluator_on_nested_variant_patterns() {
        let (value, _) = run_on_both_engines_io(
            "enum Inner {\n\tcase a(Int)\n\tcase b\n}\nenum Outer {\n\tcase wrap(Inner)\n\tcase empty\n}\nlet o = Outer.wrap(Inner.a(7))\nmatch o {\n\t.wrap(.a(x)) -> x,\n\t.wrap(.b) -> 1,\n\t.empty -> 2\n}",
        );
        assert_eq!(value, Value::I64(7));
    }

    #[test]
    fn vm_matches_evaluator_on_or_patterns() {
        let (value, _) = run_on_both_engines_io(
            "match 3 {\n\t1 | 2 -> 10,\n\t3 | 4 -> 20,\n\t_ -> 0\n}",
        );
        assert_eq!(value, Value::I64(20));
    }

    #[test]
    fn vm_matches_evaluator_on_wildcard_default_over_enums() {
        let (value, _) = run_on_both_engines_io(
            "enum Color {\n\tcase red\n\tcase green\n\tcase blue\n}\nlet c = Color.blue\nmatch c {\n\t.red -> 1,\n\t_ -> 9\n}",
        );
        assert_eq!(value, Value::I64(9));
    }

    #[test]
    fn vm_matches_evaluator_on_optional_some_and_none() {
        let (value, _) = run_on_both_engines_io(
            "let x = Optional.some(5)\nlet y: Optional<Int> = Optional.none\nlet a = match x {\n\t.some(v) -> v,\n\t.none -> 0\n}\nlet b = match y {\n\t.some(v) -> v,\n\t.none -> 100\n}\na + b",
        );
        assert_eq!(value, Value::I64(105));
    }

    #[test]
    fn vm_matches_evaluator_on_variant_or_patterns_with_shared_bind() {
        let (value, _) = run_on_both_engines_io(
            "enum Either {\n\tcase left(Int)\n\tcase right(Int)\n\tcase neither\n}\nlet e = Either.right(8)\nmatch e {\n\t.left(n) | .right(n) -> n,\n\t.neither -> 0\n}",
        );
        assert_eq!(value, Value::I64(8));
    }

    #[test]
    fn vm_matches_evaluator_on_record_literal_patterns() {
        let (value, _) = run_on_both_engines_io(
            "let record = { x: 123, y: 456 }\nlet result = match record {\n\t{ x, y: 123 } -> 1,\n\t{ x, y: 456 } -> 2,\n\t{ x, y: _ } -> 3\n}\nresult",
        );
        assert_eq!(value, Value::I64(2));
    }

    #[test]
    fn vm_matches_evaluator_on_tuple_patterns_in_match() {
        let (value, _) = run_on_both_engines_io(
            "let pair = (1, 2)\nmatch pair {\n\t(1, y) -> y + 10,\n\t(x, _) -> x\n}",
        );
        assert_eq!(value, Value::I64(12));
    }

    #[test]
    fn vm_matches_evaluator_on_enum_match_in_function() {
        // The match sits inside a demanded specialization (not main), so
        // the switch's continuations are claimed by a non-entry chunk.
        let (value, _) = run_on_both_engines_io(
            "enum Shape {\n\tcase circle(Int)\n\tcase square(Int)\n}\nfunc area(s: Shape) -> Int {\n\tmatch s {\n\t\t.circle(r) -> 3 * r * r,\n\t\t.square(w) -> w * w\n\t}\n}\narea(Shape.circle(2)) + area(Shape.square(3))",
        );
        assert_eq!(value, Value::I64(21));
    }

    #[test]
    fn vm_matches_evaluator_on_tuple_destructuring_let() {
        let (value, _) = run_on_both_engines_io("let (a, b) = (1, 2)\na + b");
        assert_eq!(value, Value::I64(3));
    }

    #[test]
    fn vm_matches_evaluator_on_record_destructuring_let() {
        let (value, _) = run_on_both_engines_io(
            "let { x, y } = { x: 3, y: 4 }\nx + y",
        );
        assert_eq!(value, Value::I64(7));
    }

    // ----- M5: arrays, sized memory, conditional conformance ----------------

    #[test]
    fn vm_matches_evaluator_on_array_count() {
        let (value, _) = run_on_both_engines_io("let a = [1, 2, 3]\na.count");
        assert_eq!(value, Value::I64(3));
    }

    #[test]
    fn vm_matches_evaluator_on_array_get() {
        let (value, _) = run_on_both_engines_io("let a = [10, 20, 30]\na.get(1)");
        assert_eq!(value, Value::I64(20));
    }

    #[test]
    fn vm_matches_evaluator_on_float_array_round_trip() {
        let (value, _) = run_on_both_engines_io("let a = [1.5, 2.5]\na.get(0) + a.get(1)");
        assert_eq!(value, Value::F64(4.0));
    }

    #[test]
    fn vm_matches_evaluator_on_array_of_structs_round_trip() {
        // The flagged M5 seam: aggregates stored in raw memory are arena
        // handles; a struct must survive the store/load round trip.
        let (value, _) = run_on_both_engines_io(
            "struct Point {\n\tlet x: Int\n\tlet y: Int\n}\nlet points = [Point(x: 1, y: 2), Point(x: 3, y: 4)]\npoints.get(1).y",
        );
        assert_eq!(value, Value::I64(4));
    }

    #[test]
    fn vm_matches_evaluator_on_conditional_conformance_array_show() {
        // extend Array<Element: Showable>: Showable — the witness demands
        // at Element := Int (context discharged by monomorphization).
        let (_, out) = run_on_both_engines_io("let a = [1, 2, 3]\nprint(a)");
        assert_eq!(out, "[1, 2, 3]\n");
    }

    #[test]
    fn vm_matches_evaluator_on_generic_bounded_dispatch() {
        // Protocols.tlk in miniature: a rigid-bounded param dispatches
        // through the conformance row at the demand's θ.
        let (value, _) = run_on_both_engines_io(
            "protocol Foo {\n\tfunc foo() -> Int\n}\nstruct Thing {}\nextend Thing: Foo {\n\tfunc foo() { 123 }\n}\nfunc fizz<T: Foo>(t: T) { t.foo() }\nfizz(Thing())",
        );
        assert_eq!(value, Value::I64(123));
    }

    #[test]
    fn vm_matches_evaluator_on_array_iterator_next() {
        // ArrayIterator.next() is a mutating witness: inout self writes
        // back into the iterator's cell between calls.
        let (value, _) = run_on_both_engines_io(
            "let numbers = [7, 8]\nlet it = numbers.iter()\nlet r1: Optional<Int> = it.next()\nlet r2: Optional<Int> = it.next()\nlet r3: Optional<Int> = it.next()\nlet a = match r1 {\n\t.some(v) -> v,\n\t.none -> 0 - 1\n}\nlet b = match r2 {\n\t.some(v) -> v,\n\t.none -> 0 - 1\n}\nlet c = match r3 {\n\t.some(v) -> v,\n\t.none -> 0 - 1\n}\na * 100 + b * 10 + c",
        );
        assert_eq!(value, Value::I64(7 * 100 + 8 * 10 - 1));
    }

    #[test]
    fn vm_matches_evaluator_on_derived_show_for_enums() {
        // Showable is auto-derived for enums (no conformance row): the
        // lowerer synthesizes show. Format matches the old implementation:
        // Name.variant(payloads…).
        let (_, out) = run_on_both_engines_io(
            "let some: Optional<Int> = Optional.some(5)\nlet none: Optional<Int> = Optional.none\nprint(some)\nprint(none)",
        );
        assert_eq!(out, "Optional.some(5)\nOptional.none\n");
    }

    // ----- M6: closures, indirect calls, trailing blocks ---------------------

    #[test]
    fn vm_matches_evaluator_on_anonymous_function_application() {
        // A function literal bound and applied (the parser does not chain
        // a call directly onto a literal — AnonFunc.tlk's `}(123)` parses
        // as a separate parenthesized statement).
        let (value, _) = run_on_both_engines_io("let f = func(x) {\n\t1 + x\n}\nf(123)");
        assert_eq!(value, Value::I64(124));
    }

    #[test]
    fn vm_matches_evaluator_on_closure_capturing_a_cell() {
        // Capture.tlk in miniature: the closure captures the counter's
        // cell; mutations persist across calls.
        let (value, _) = run_on_both_engines_io(
            "func makeCounter() {\n\tlet i = 0\n\n\treturn func() {\n\t\ti = i + 1\n\t\ti\n\t}\n}\nlet counter = makeCounter()\ncounter()\ncounter()\ncounter()",
        );
        assert_eq!(value, Value::I64(3));
    }

    #[test]
    fn vm_matches_evaluator_on_closure_as_argument() {
        let (value, _) = run_on_both_engines_io(
            "func apply(f: (Int) -> Int, x: Int) -> Int { f(x) }\napply(func(n) { n * 2 }, 21)",
        );
        assert_eq!(value, Value::I64(42));
    }

    #[test]
    fn vm_matches_evaluator_on_trailing_blocks() {
        let (_, out) = run_on_both_engines_io(
            "func twice(foo: () -> ()) {\n\tfoo()\n\tfoo()\n}\ntwice { print(\"hi\") }",
        );
        assert_eq!(out, "hi\nhi\n");
    }

    #[test]
    fn vm_matches_evaluator_on_statically_routed_sleep() {
        // 'io(.sleep(ms)) routes statically to the io_sleep primop (the
        // implicit top-level handler); CaptureIO's sleep is a no-op
        // returning 0.
        let (value, _) = run_on_both_engines_io("sleep(0)");
        assert_eq!(value, Value::I64(0));
    }

    // ----- M7: abort effects (capability-passing CPS — Schuster et al.,
    // ICFP 2020/PLDI 2022; abort as unwinding, Hillerström et al., FSCD
    // 2017 §4.5) ----------------------------------------------------------

    #[test]
    fn vm_matches_evaluator_on_abort_effect() {
        // Effects.tlk in miniature: the perform runs the lexical handler,
        // the rest of the performing function never runs.
        let (_, out) = run_on_both_engines_io(
            "effect 'oops(error) -> Never\n@handle 'oops { err in print(err) }\nfunc boom() 'oops -> () {\n\t'oops(\"bang\")\n\tprint(\"after perform\")\n}\nboom()",
        );
        assert_eq!(out, "bang\n");
    }

    #[test]
    fn vm_matches_evaluator_on_abort_skipping_rest_of_scope() {
        // The abort skips not just the performer's remainder but every
        // statement between the call and the end of the handled scope.
        let (_, out) = run_on_both_engines_io(
            "effect 'oops(error) -> Never\n@handle 'oops { err in print(err) }\nfunc boom() 'oops -> () {\n\t'oops(\"bang\")\n}\nboom()\nprint(\"rest of scope\")",
        );
        assert_eq!(out, "bang\n");
    }

    #[test]
    fn vm_matches_evaluator_on_abort_two_levels_below_the_scope() {
        // The perform sits two calls below the handler's scope: the abort
        // propagates as a plain Ret chain through the intermediate frame,
        // running no code in either function's remainder.
        let (_, out) = run_on_both_engines_io(
            "effect 'oops(error) -> Never\n@handle 'oops { err in print(err) }\nfunc inner() 'oops -> () {\n\t'oops(\"deep\")\n\tprint(\"inner after\")\n}\nfunc outer() 'oops -> () {\n\tinner()\n\tprint(\"outer after\")\n}\nouter()\nprint(\"main after\")",
        );
        assert_eq!(out, "deep\n");
    }

    #[test]
    fn vm_matches_evaluator_on_effect_normal_path() {
        // No perform fires: the reified rest-of-scope (the let binding and
        // the arithmetic after the call) runs exactly once.
        let (value, out) = run_on_both_engines_io(
            "effect 'oops(error) -> Never\n@handle 'oops { err in\n\tprint(err)\n\t0\n}\nfunc check(x: Bool) 'oops -> Int {\n\tif x {\n\t\t'oops(\"nope\")\n\t}\n\t42\n}\nlet result = check(false)\nresult + 1",
        );
        assert_eq!(out, "");
        assert_eq!(value, Value::I64(43));
    }

    #[test]
    fn vm_matches_evaluator_on_abort_handler_value_as_scope_value() {
        // When the abort fires, the handler block's value becomes the
        // handled scope's value (Plotkin & Pretnar handler semantics).
        let (value, out) = run_on_both_engines_io(
            "effect 'oops(error) -> Never\n@handle 'oops { err in\n\tprint(err)\n\t0\n}\nfunc check(x: Bool) 'oops -> Int {\n\tif x {\n\t\t'oops(\"nope\")\n\t}\n\t42\n}\nlet result = check(true)\nresult + 1",
        );
        assert_eq!(out, "nope\n");
        assert_eq!(value, Value::I64(0));
    }

    #[test]
    fn vm_matches_evaluator_on_abort_handler_capturing_a_local() {
        // The handler block closes over a local of the scope's function;
        // the capability reaches the performer with that environment.
        let (_, out) = run_on_both_engines_io(
            "effect 'oops(error) -> Never\nlet tag = \"caught: \"\n@handle 'oops { err in\n\tprint(tag)\n\tprint(err)\n}\nfunc boom() 'oops -> () {\n\t'oops(\"bang\")\n}\nboom()",
        );
        assert_eq!(out, "caught: \nbang\n");
    }

    // ----- M9: resumable handlers (`continue v` resumes the perform; a
    // handler completing without continue aborts the scope — one-shot by
    // construction since continue is a tail transfer) ---------------------

    #[test]
    fn vm_matches_evaluator_on_resuming_handler() {
        // The handler resumes with 42: the performer continues as if the
        // perform returned it, and the rest of the scope runs.
        let (value, out) = run_on_both_engines_io(
            "effect 'ask(prompt) -> Int\n@handle 'ask { p in\n\tprint(p)\n\tcontinue 42\n}\nfunc question() 'ask -> Int {\n\tlet answer = 'ask(\"meaning?\")\n\tanswer + 1\n}\nlet r = question()\nr * 2",
        );
        assert_eq!(out, "meaning?\n");
        assert_eq!(value, Value::I64((42 + 1) * 2));
    }

    #[test]
    fn vm_matches_evaluator_on_resume_two_levels_below_the_scope() {
        // The perform sits two calls below the handler: resuming runs the
        // rest of the performer AND the rest of its caller, exactly once
        // each, with the value threading back up the reified chain.
        let (_, out) = run_on_both_engines_io(
            "effect 'ask(prompt) -> Int\n@handle 'ask { p in\n\tcontinue 10\n}\nfunc inner() 'ask -> Int {\n\tlet v = 'ask(\"x\")\n\tv + 1\n}\nfunc outer() 'ask -> Int {\n\tlet w = inner()\n\tw + 100\n}\nlet o = outer()\nprint(o + 1000)",
        );
        assert_eq!(out, "1111\n");
    }

    #[test]
    fn vm_matches_evaluator_on_handler_that_chooses_to_resume() {
        // A conditional handler: positive payloads resume, the rest of
        // the performer runs (v * 10).
        let (value, _) = run_on_both_engines_io(
            "effect 'check(n) -> Int\n@handle 'check { n in\n\tif n > 0 {\n\t\tcontinue n\n\t}\n\t0 - 1\n}\nfunc go(x: Int) 'check -> Int {\n\tlet v = 'check(x)\n\tv * 10\n}\ngo(5)",
        );
        assert_eq!(value, Value::I64(50));
    }

    #[test]
    fn vm_matches_evaluator_on_handler_that_chooses_to_abort() {
        // The same handler aborting: its value (-1) becomes the scope's
        // value and the performer's rest (v * 10) never runs.
        let (value, _) = run_on_both_engines_io(
            "effect 'check(n) -> Int\n@handle 'check { n in\n\tif n > 0 {\n\t\tcontinue n\n\t}\n\t0 - 1\n}\nfunc go(x: Int) 'check -> Int {\n\tlet v = 'check(x)\n\tv * 10\n}\ngo(0)",
        );
        assert_eq!(value, Value::I64(-1));
    }

    #[test]
    fn vm_matches_evaluator_on_resume_at_a_tail_perform() {
        // The perform is the performer's final expression: the resumed
        // value is the performer's result directly.
        let (value, _) = run_on_both_engines_io(
            "effect 'ask(prompt) -> Int\n@handle 'ask { p in\n\tcontinue 7\n}\nfunc query() 'ask -> Int {\n\t'ask(\"q\")\n}\nlet a = query()\na + 1",
        );
        assert_eq!(value, Value::I64(8));
    }

    #[test]
    fn vm_matches_evaluator_on_resume_at_a_statement_perform() {
        // Statement-position perform: the resumed value is discarded and
        // the statements after it run.
        let (_, out) = run_on_both_engines_io(
            "effect 'ping() -> Int\n@handle 'ping {\n\tcontinue 1\n}\nfunc go() 'ping -> () {\n\t'ping()\n\tprint(\"resumed\")\n}\ngo()",
        );
        assert_eq!(out, "resumed\n");
    }

    #[test]
    fn vm_matches_evaluator_on_repeated_performs_through_one_handler() {
        // Deep-handler semantics: the handler stays installed; every
        // perform runs it afresh (three resumes through a loop).
        let (value, _) = run_on_both_engines_io(
            "effect 'step(n) -> Int\n@handle 'step { n in\n\tcontinue n + 1\n}\nfunc go() 'step -> Int {\n\tlet a = 'step(0)\n\tlet b = 'step(a)\n\tlet c = 'step(b)\n\tc\n}\ngo()",
        );
        assert_eq!(value, Value::I64(3));
    }

    // ----- M8: the full io dialect (both engines run against the same
    // CaptureIO: simulated fds, write-then-read loopback) -----------------

    #[test]
    fn vm_matches_evaluator_on_file_write_read_roundtrip() {
        // open mints a simulated fd; writes append; reads start at the
        // beginning — so a write then read round-trips the bytes.
        let (value, out) = run_on_both_engines_io(
            "let path = _alloc<Byte>(1)\nlet fd = _io_open(path, 65, 384)\nlet hello = \"hello io\"\n_io_write(fd, hello.base, hello.length)\nlet buf = _alloc<Byte>(16)\nlet n = _io_read(fd, buf, 16)\n_io_write(STDOUT_FD, buf, n)\n_io_close(fd)",
        );
        assert_eq!(out, "hello io");
        assert_eq!(value, Value::I64(0));
    }

    #[test]
    fn vm_matches_evaluator_on_socket_loopback() {
        // CaptureIO sockets are buffers: what a test writes to a
        // connection it can read back — the scripted-client loop.
        let (_, out) = run_on_both_engines_io(
            "let sock = _io_socket(AF_INET, SOCK_STREAM, 0)\n_io_connect(sock, LOCALHOST, 9900)\nlet msg = \"ping\"\n_io_write(sock, msg.base, msg.length)\nlet buf = _alloc<Byte>(8)\nlet n = _io_read(sock, buf, 8)\n_io_write(STDOUT_FD, buf, n)",
        );
        assert_eq!(out, "ping");
    }

    #[test]
    fn vm_matches_evaluator_on_server_accept_script() {
        // The ChatServer slice: bind/listen succeed, accept mints a
        // client fd, and the greeting written to it reads back.
        let (value, out) = run_on_both_engines_io(
            "let server = _io_socket(AF_INET, SOCK_STREAM, 0)\nlet b = _io_bind(server, INADDR_ANY, 9900)\nlet l = _io_listen(server, 128)\nlet client = _io_accept(server)\nlet hi = \"hi client\"\n_io_write(client, hi.base, hi.length)\nlet buf = _alloc<Byte>(16)\nlet n = _io_read(client, buf, 16)\n_io_write(STDOUT_FD, buf, n)\nb + l",
        );
        assert_eq!(out, "hi client");
        assert_eq!(value, Value::I64(0));
    }

    #[test]
    fn vm_matches_evaluator_on_io_error_returns() {
        // POSIX conventions: a bad fd reads as -EBADF, and ctl is
        // -EINVAL under the captured io (tests never ioctl for real).
        let (value, _) = run_on_both_engines_io(
            "let buf = _alloc<Byte>(4)\nlet bad = _io_read(99, buf, 4)\nlet ctl = _io_ctl(1, 0, 0)\nbad * 100 + ctl",
        );
        assert_eq!(value, Value::I64(-9 * 100 + -22));
    }

    #[test]
    fn vm_matches_evaluator_on_empty_poll() {
        // Zero descriptors: poll reports zero ready (the marshaling
        // boundary, without hand-building pollfd records in Talk).
        let (value, _) = run_on_both_engines_io(
            "let fds = _alloc<Byte>(8)\n_io_poll(fds, 0, 0)",
        );
        assert_eq!(value, Value::I64(0));
    }

    #[test]
    fn vm_runs_deep_recursion_beyond_the_evaluator() {
        // VM-only: fib(20) — loops in the term would blow past the
        // reference evaluator's step budget, but the frame-stack VM is
        // fine.
        let driver = Driver::new(
            vec![Source::from(
                "func fib(n) {\n\tif n <= 1 { return n }\n\treturn fib(n - 2) + fib(n - 1)\n}\nfib(20)",
            )],
            DriverConfig::new("VmTest"),
        );
        let mut lowered = driver
            .parse()
            .unwrap()
            .resolve_names()
            .unwrap()
            .type_check()
            .lower();
        assert_eq!(lowered.run_vm().expect("vm"), Value::I64(6765));
    }
}
