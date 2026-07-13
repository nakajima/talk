#[cfg(test)]
pub mod tests {
    use crate::compiling::driver::{Driver, DriverConfig, Source};
    use crate::lambda_g::eval::EvalValue;
    use crate::name_resolution::symbol::Symbol;
    use crate::vm::interp::{Value, ValueNames, run, run_displayed};
    use crate::vm::io::CaptureIO;
    use crate::vm::{Chunk, Insn, MemKind, Module};

    /// The same program runs on the reference evaluator (a direct
    /// transcription of the paper's semantics — our trusted baseline) and
    /// on the scheduled bytecode VM; results must agree. This is the
    /// safety net for the one novel composition in the backend — λ_G →
    /// nesting-tree schedule → bytecode (plan's flagged seam #2).
    fn run_on_both_engines(code: &'static str) -> Value {
        let code = unsafe_marked_if_raw(code);
        let driver = Driver::new(
            vec![Source::from(code.as_str())],
            DriverConfig::new("VmTest"),
        );
        let typed = driver
            .parse()
            .expect("parse")
            .resolve_names()
            .expect("resolve")
            .type_check();
        assert!(
            !typed.has_errors(),
            "type errors: {:?}",
            typed.diagnostics()
        );
        let mut lowered = typed.lower();
        assert!(
            lowered.phase.diagnostics.is_empty(),
            "lowering: {:?}",
            lowered.phase.diagnostics
        );
        // Post-lowering verifier: T-Prog + WF over the whole program
        // (LLVM-verifier spirit — Lattner & Adve, CGO 2004). The
        // free-balance verifier (ADR 0017 stage 2) already ran inside
        // `Driver::lower` — on by default in test builds.
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
        assert!(matches, "evaluator {evaluator_value:?} != vm {vm_value:?}");
        vm_value
    }

    #[test]
    fn vm_matches_evaluator_on_arithmetic() {
        assert_eq!(run_on_both_engines("2 + 3 * 3"), Value::I64(11));
    }

    #[test]
    fn vm_matches_evaluator_on_branches() {
        assert_eq!(
            run_on_both_engines("if 2 > 3 { 1 } else { 2 }"),
            Value::I64(2)
        );
    }

    #[test]
    fn vm_matches_evaluator_on_locals() {
        assert_eq!(
            run_on_both_engines("let a = 4\nlet b = a + 1\nb * 2"),
            Value::I64(10)
        );
    }

    #[test]
    fn vm_matches_evaluator_on_character_literal() {
        assert_eq!(run_on_both_engines("'😎'.utf8_count()"), Value::I64(4));
    }

    #[test]
    fn vm_matches_evaluator_on_omitted_string_call_parens() {
        assert_eq!(
            run_on_both_engines("func len(s: String) -> Int { s.byte_count }\nlen \"abc\""),
            Value::I64(3)
        );
    }

    #[test]
    fn vm_matches_evaluator_on_positional_block_args() {
        assert_eq!(
            run_on_both_engines("func apply(f) { f(2, 3) }\napply { $0 + $1 }"),
            Value::I64(5)
        );
    }

    #[test]
    fn vm_matches_evaluator_on_sequential_rebinding() {
        // Rule 2 of docs/sequential-scoping-plan.md: a later `let` shadows
        // from its point of declaration on; its rhs sees the earlier
        // binding.
        assert_eq!(
            run_on_both_engines("func f() -> Int {\n\tlet x = 1\n\tlet x = x + 1\n\tx\n}\nf()"),
            Value::I64(2)
        );
    }

    #[test]
    fn vm_matches_evaluator_on_capture_of_rebound_binding() {
        // A closure keeps the binding visible where it was written; a
        // later rebinding doesn't retroactively change the capture.
        assert_eq!(
            run_on_both_engines(
                "func f() -> Int {\n\tlet x = 1\n\tlet g = func() -> Int { x }\n\tlet x = 2\n\tg() + x\n}\nf()"
            ),
            Value::I64(3)
        );
    }

    #[test]
    fn vm_matches_evaluator_on_local_self_recursion() {
        assert_eq!(
            run_on_both_engines(
                "func outer() -> Int {\n\tfunc fact(n: Int) -> Int { if n > 1 { n * fact(n - 1) } else { 1 } }\n\tfact(5)\n}\nouter()"
            ),
            Value::I64(120)
        );
    }

    #[test]
    fn vm_matches_evaluator_on_local_mutual_recursion() {
        // `func a` / `func b` in one block see each other regardless of
        // order (the resolver hoists func-valued let binders; lowering
        // must give them their labels up front the same way).
        assert_eq!(
            run_on_both_engines(
                "func outer() -> Int {\n\tfunc a(n: Int) -> Int { if n > 0 { b(n - 1) } else { 0 } }\n\tfunc b(n: Int) -> Int { a(n) + 1 }\n\ta(4)\n}\nouter()"
            ),
            Value::I64(4)
        );
    }

    #[test]
    fn vm_matches_evaluator_on_recursive_closure_capturing_a_local() {
        assert_eq!(
            run_on_both_engines(
                "func outer() -> Int {\n\tlet step = 2\n\tfunc down(n: Int) -> Int { if n > 0 { down(n - step) + 1 } else { 0 } }\n\tdown(6)\n}\nouter()"
            ),
            Value::I64(3)
        );
    }

    #[test]
    fn vm_matches_evaluator_on_calls() {
        assert_eq!(
            run_on_both_engines("func double(x: Int) -> Int { x * 2 }\ndouble(21)"),
            Value::I64(42)
        );
    }

    #[test]
    fn vm_runs_existential_member_dispatch() {
        assert_eq!(
            run_on_both_engines(
                "// no-core\nprotocol Number {\n\tfunc value() -> Int\n}\nextend Int: Number {\n\tfunc value() -> Int { self }\n}\nlet x: any Number = 41\nx.value()"
            ),
            Value::I64(41)
        );
    }

    #[test]
    fn vm_runs_as_expressions() {
        // `as` erases at typed-program build: the inner expression grafts under the
        // As node's annotations (ascribed type; existential pack when the
        // ascription packs).
        assert_eq!(
            run_on_both_engines("let n = (1 as Int)\nn + 2"),
            Value::I64(3)
        );
        assert_eq!(
            run_on_both_engines(
                "// no-core\nprotocol Number {\n\tfunc value() -> Int\n}\nextend Int: Number {\n\tfunc value() -> Int { self }\n}\nlet x = (41 as any Number)\nx.value()"
            ),
            Value::I64(41)
        );
    }

    #[test]
    fn vm_runs_existential_return_and_generic_bound_dispatch() {
        assert_eq!(
            run_on_both_engines(
                "// no-core\nprotocol Number {\n\tfunc value() -> Int\n}\nextend Int: Number {\n\tfunc value() -> Int { self }\n}\nfunc make() -> any Number { 9 }\nfunc render<T: Number>(x: T) -> Int { x.value() }\nrender(make())"
            ),
            Value::I64(9)
        );
    }

    #[test]
    fn vm_runs_existentials_in_records_and_enums() {
        assert_eq!(
            run_on_both_engines(
                "// no-core\nprotocol Number {\n\tfunc value() -> Int\n}\nextend Int: Number {\n\tfunc value() -> Int { self }\n}\nstruct Box {\n\tlet item: any Number\n}\nenum MaybeNumber {\n\tcase some(any Number)\n}\nlet box = Box(item: 12)\nlet maybe = MaybeNumber.some(box.item)\nmatch maybe {\n\tMaybeNumber.some(value) -> value.value()\n}"
            ),
            Value::I64(12)
        );
    }

    #[test]
    fn vm_runs_existentials_in_arrays() {
        let (_, out) = run_on_both_engines_io(
            "protocol Number {\n\tfunc value() -> Int\n}\nextend Int: Number {\n\tfunc value() -> Int { self }\n}\nlet values: Array<any Number> = [3, 4]\nprint(values.get(1).value())",
        );
        assert_eq!(out, "4\n");
    }

    /// B4 (ownership-soundness plan 3.2): an implicit pack from a borrowed
    /// CheapClone payload compiles by retaining — the packed `any` and the
    /// caller's original release independently, so the program balances
    /// (the eval harness's leak fence asserts it) instead of double-freeing.
    #[test]
    fn vm_balances_borrowed_cheap_clone_existential_pack() {
        assert_eq!(
            run_on_both_engines(
                "protocol Sized {\n\tfunc size() -> Int\n}\nextend String: Sized {\n\tfunc size() -> Int { self.byte_count }\n}\nfunc pack(s: String) -> any Sized {\n\ts\n}\nfunc use_it() -> Int {\n\tlet s = \"hello\" + \" heap string\"\n\tlet a = pack(s)\n\ta.size() + s.byte_count\n}\nuse_it()"
            ),
            Value::I64(34)
        );
    }

    #[test]
    fn vm_runs_gadt_hidden_payload_packed_as_existential() {
        assert_eq!(
            run_on_both_engines(
                "// no-core\nprotocol Showable {\n\tfunc show() -> Int\n}\nextend Int: Showable {\n\tfunc show() -> Int { self }\n}\nenum GBox<T> {\n\tcase hidden<A: Showable>(A) -> GBox<Bool>\n}\nfunc erase(box: GBox<Bool>) -> any Showable {\n\tmatch box {\n\t\t.hidden(value) -> value\n\t}\n}\nerase(GBox.hidden(5)).show()"
            ),
            Value::I64(5)
        );
    }

    #[test]
    fn vm_runs_gadt_hidden_payload_direct_bound_call() {
        assert_eq!(
            run_on_both_engines(
                "// no-core\nprotocol Showable {\n\tfunc show() -> Int\n}\nextend Int: Showable {\n\tfunc show() -> Int { self }\n}\nenum GBox<T> {\n\tcase hidden<A: Showable>(A) -> GBox<Bool>\n}\nfunc render(box: GBox<Bool>) -> Int {\n\tmatch box {\n\t\t.hidden(value) -> value.show()\n\t}\n}\nrender(GBox.hidden(6))"
            ),
            Value::I64(6)
        );
    }

    #[test]
    fn vm_runs_existential_member_dispatch_with_associated_binding() {
        assert_eq!(
            run_on_both_engines(
                "// no-core\nprotocol Iterator {\n\tassociated Element\n\tfunc next() -> Element\n}\nstruct One {\n\tlet value: Int\n}\nextend One: Iterator {\n\ttypealias Element = Int\n\tfunc next() -> Int { self.value }\n}\nlet it: any Iterator<Element = Int> = One(value: 7)\nit.next()"
            ),
            Value::I64(7)
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

    #[test]
    fn vm_matches_evaluator_on_generic_consume_param_in_loop() {
        // A generic `consume` param eaten inside a loop auto-clones per
        // iteration (liveness loop-carries parameters like pre-loop lets);
        // the String instantiation exercises the retain/release balance on
        // both engines.
        assert_eq!(
            run_on_both_engines(
                "func eat<T>(consume x: T) -> Int {\n\t0\n}\nfunc f<T>(consume x: T) -> Int {\n\tlet i = 0\n\tloop i < 2 {\n\t\ti = i + 1\n\t\tlet n = eat(x)\n\t}\n\ti\n}\nf(\"a\" + \"b\")"
            ),
            Value::I64(2)
        );
    }

    #[test]
    fn vm_matches_evaluator_on_inferred_borrow_param() {
        // Plan 3.3(b): `func peek(x)` borrows by default — a droppable
        // String flows through the inferred param, stays caller-owned, and
        // both engines balance (no leak, no double free).
        assert_eq!(
            run_on_both_engines(
                "func peek(x) -> Int {\n\tx.byte_count\n}\nlet s = \"a\" + \"b\"\nlet n = peek(s)\nlet m = s.byte_count\nn + m"
            ),
            Value::I64(4)
        );
    }

    #[test]
    fn vm_matches_evaluator_on_inferred_param_arithmetic() {
        // Copy erasure on inferred borrow params: `&?a` meets Int and
        // erases, so the body compiles to scalar arithmetic.
        assert_eq!(
            run_on_both_engines("func add(a, b) {\n\ta + b\n}\nadd(1, 2)"),
            Value::I64(3)
        );
    }

    #[test]
    fn vm_matches_evaluator_on_inferred_identity_borrow() {
        // `func id(x) { x }` returns a borrow of its argument (the
        // annotated-generic twin's semantics); the caller reads through
        // both the borrow and the original owner.
        assert_eq!(
            run_on_both_engines(
                "func id(x) {\n\tx\n}\nlet s = \"a\" + \"b\"\nlet t = id(s)\nt.byte_count + s.byte_count"
            ),
            Value::I64(4)
        );
    }

    /// Both engines, including captured stdout (the M3 surface: records,
    /// strings, io_write).
    fn run_on_both_engines_io(code: &'static str) -> (Value, String) {
        let mut lowered = lower_for_both_engines(code);
        let (vm_value, vm_out) = lowered.run_vm_with_output().expect("vm");
        let (evaluator_value, evaluator_out) = lowered.eval_with_output().expect("evaluator");
        assert_engine_values_match(&evaluator_value, &vm_value);
        assert_eq!(evaluator_out, vm_out, "stdout diverged");
        (vm_value, vm_out)
    }

    fn lower_for_both_engines(
        code: &'static str,
    ) -> crate::compiling::driver::Driver<crate::compiling::driver::Lowered> {
        let code = unsafe_marked_if_raw(code);
        let driver = Driver::new(
            vec![Source::from(code.as_str())],
            DriverConfig::new("VmTest"),
        );
        let typed = driver
            .parse()
            .expect("parse")
            .resolve_names()
            .expect("resolve")
            .type_check();
        assert!(
            !typed.has_errors(),
            "type errors: {:?}",
            typed.diagnostics()
        );
        let mut lowered = typed.lower();
        assert!(
            lowered.phase.diagnostics.is_empty(),
            "lowering: {:?}",
            lowered.phase.diagnostics
        );
        // T-Prog + WF; the free-balance verifier already ran inside
        // `Driver::lower` (on by default in test builds).
        let verified = lowered.phase.program.verify();
        assert!(verified.is_ok(), "verifier: {:?}", verified.err());
        lowered
    }

    // ------------------------------------------------------------------
    // Leak fences (ownership-soundness plan 6.2): every run asserts the
    // allocation balance at exit, with the result value's own footprint
    // accounted so container/String-valued programs are fenced too.
    // ------------------------------------------------------------------

    #[test]
    fn vm_matches_evaluator_on_discarded_droppable_call_result() {
        // A statement-position call whose droppable result is discarded:
        // flow CONSUMES the value (mir ConsumeValue), so the discard owns
        // the drop (`lower_mir_discard`). Found by the 6.2 accounting
        // sweep — the discard delivered the value into a `drop`
        // continuation that dropped nothing.
        assert_eq!(
            run_on_both_engines(
                "func mk() -> String {\n\t\"x\" + \"y\"\n}\nfunc check() -> Int {\n\tmk()\n\t0\n}\ncheck()"
            ),
            Value::I64(0)
        );
    }

    /// A leak the free-balance verifier cannot see (the pointer escapes
    /// into an array buffer, so the verifier widens instead of reporting)
    /// behind a non-scalar result: only the runtime fence catches it.
    const LEAK_BEHIND_STRING_RESULT: &str = "let xs = [_alloc<Byte>(8)]\n\"a\" + \"b\"";

    #[test]
    #[should_panic(expected = "allocations leaked")]
    fn eval_fence_catches_leak_behind_string_result() {
        let mut lowered = lower_for_both_engines(LEAK_BEHIND_STRING_RESULT);
        let _ = lowered.eval_with_output().expect("evaluator");
    }

    #[test]
    #[should_panic(expected = "allocations leaked")]
    fn vm_fence_catches_leak_behind_string_result() {
        let mut lowered = lower_for_both_engines(LEAK_BEHIND_STRING_RESULT);
        let _ = lowered.run_vm_with_output().expect("vm");
    }

    #[test]
    fn fences_account_result_footprint_for_container_results() {
        // Heap-backed results are the value's own footprint, not a leak: a
        // heap String, an array, and a struct holding a heap String.
        for code in [
            "\"a\" + \"b\"",
            "[1, 2, 3]",
            "struct Holder {\n\tlet name: String\n}\nHolder(name: \"a\" + \"b\")",
        ] {
            let mut lowered = lower_for_both_engines(code);
            let _ = lowered.run_vm_with_output().expect("vm");
            let _ = lowered.eval_with_output().expect("evaluator");
        }
    }

    fn assert_engine_values_match(evaluator_value: &EvalValue, vm_value: &Value) {
        let matches = match (evaluator_value, vm_value) {
            (EvalValue::I64(a), Value::I64(b)) => a == b,
            (EvalValue::F64(a), Value::F64(b)) => a == b,
            (EvalValue::Bool(a), Value::Bool(b)) => a == b,
            (EvalValue::Void, Value::Void) => true,
            // Aggregates: stdout agreement is the assertion that matters.
            (EvalValue::Record(..), Value::Record(..)) => true,
            (EvalValue::Tuple(..), Value::Tuple(..)) => true,
            _ => false,
        };
        assert!(matches, "evaluator {evaluator_value:?} != vm {vm_value:?}");
    }

    fn unsafe_marked_if_raw(code: &str) -> String {
        if code.contains("RawPtr")
            || code.contains("_alloc")
            || code.contains("_io_")
            || code.contains("@_ir")
        {
            format!("// unsafe\n{code}")
        } else {
            code.to_string()
        }
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
            "struct Counter {\n\tlet n: Int\n\n\tmut func bump() {\n\t\tself.n = self.n + 1\n\t}\n}\nlet c = Counter(n: 1)\nc.bump()\nc.bump()\nc.n",
        );
        assert_eq!(value, Value::I64(3));
    }

    #[test]
    fn vm_matches_evaluator_on_mutating_nested_field_receiver_writeback() {
        let (value, _) = run_on_both_engines_io(
            "struct Counter {\n\tlet n: Int\n\n\tmut func bump() {\n\t\tself.n = self.n + 1\n\t}\n}\nstruct Inner {\n\tlet counter: Counter\n\tlet offset: Int\n}\nstruct Outer {\n\tlet inner: Inner\n}\nlet outer = Outer(inner: Inner(counter: Counter(n: 1), offset: 40))\nouter.inner.counter.bump()\nouter.inner.counter.n + outer.inner.offset",
        );
        assert_eq!(value, Value::I64(42));
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
    fn consuming_method_receiver_in_branch_does_not_double_free() {
        assert_eq!(
            run_on_both_engines(
                "extend String {\n\tconsuming func consume_len() -> Int {\n\t\tself.byte_count\n\t}\n}\nfunc f(flag: Bool) -> Int {\n\tlet s = \"a\" + \"b\"\n\tif flag { s.consume_len() }\n\t1\n}\nf(true)"
            ),
            Value::I64(1)
        );
    }

    #[test]
    fn if_condition_call_evaluates_once() {
        let (_, out) = run_on_both_engines_io(
            "func truth() -> Bool {\n\tprint(\"called\")\n\ttrue\n}\nif truth() { }",
        );
        assert_eq!(out, "called\n");
    }

    #[test]
    fn loop_condition_call_evaluates_once_per_iteration() {
        let (_, out) = run_on_both_engines_io(
            "let count = 0\nfunc keep() -> Bool {\n\tcount = count + 1\n\tprint(count)\n\tcount < 3\n}\nloop keep() { print(99) }",
        );
        assert_eq!(out, "1\n99\n2\n99\n3\n");
    }

    #[test]
    fn conditional_owned_match_payload_does_not_double_free() {
        assert_eq!(
            run_on_both_engines(
                "enum Wrapped { case tagged(String) }\nfunc f(flag: Bool) -> Int {\n\tlet w = Wrapped.tagged(\"a\" + \"b\")\n\tif flag {\n\t\tmatch w { .tagged(s) -> s.byte_count }\n\t}\n\t0\n}\nf(true)"
            ),
            Value::I64(0)
        );
    }

    #[test]
    fn wildcard_owned_match_payload_does_not_leak() {
        assert_eq!(
            run_on_both_engines(
                "enum Wrapped { case tagged(String) }\nfunc f() -> Int {\n\tlet w = Wrapped.tagged(\"a\" + \"b\")\n\tmatch w { .tagged(_) -> 1 }\n}\nf()"
            ),
            Value::I64(1)
        );
    }

    #[test]
    fn clone_temp_passed_to_borrow_param_does_not_leak() {
        // Fuzzer finding F-A: a `.clone()` result temp in borrow position
        // leaked its refcount bump — the builder never minted a temp (and
        // so no `TemporaryEnd` candidate) for `ExprKind::Clone` rvalues.
        // The eval/VM leak fences assert the balance.
        assert_eq!(
            run_on_both_engines(
                "func blen(s: &String) -> Int {\n\ts.byte_count\n}\nfunc f() -> Int {\n\tlet s = \"a\" + \"b\"\n\tblen(s.clone())\n}\nf()"
            ),
            Value::I64(2)
        );
    }

    #[test]
    fn clone_receiver_under_projection_does_not_leak() {
        // F-A's receiver twin: the clone rvalue under a projection rides
        // the opaque-chain path (B9) and needs the same temp.
        assert_eq!(
            run_on_both_engines(
                "func f() -> Int {\n\tlet s = \"a\" + \"b\"\n\ts.clone().byte_count\n}\nf()"
            ),
            Value::I64(2)
        );
    }

    #[test]
    fn clone_into_consume_param_still_balances() {
        // F-A's control: consume-position clones balanced before the fix
        // and must keep balancing (the temp classifies Dead — consumed).
        assert_eq!(
            run_on_both_engines(
                "func eat(consume s: String) -> Int {\n\ts.byte_count\n}\nfunc f() -> Int {\n\tlet s = \"a\" + \"b\"\n\teat(s.clone()) + s.byte_count\n}\nf()"
            ),
            Value::I64(4)
        );
    }

    #[test]
    fn let_bound_clone_still_balances() {
        assert_eq!(
            run_on_both_engines(
                "func f() -> Int {\n\tlet s = \"a\" + \"b\"\n\tlet t = s.clone()\n\ts.byte_count + t.byte_count\n}\nf()"
            ),
            Value::I64(4)
        );
    }

    #[test]
    fn borrowed_scrutinee_payload_binder_consume_retains_and_balances() {
        // Plan S3 repro (ADR 0025): `steal` consumes the payload binder of
        // a borrowed scrutinee. The tier-2 clone must retain — without it
        // the caller's enum frees the same payload again.
        assert_eq!(
            run_on_both_engines(
                "enum E {\n\tcase a(String)\n}\nfunc steal(e: E) -> String {\n\tmatch e {\n\t\t.a(s) -> s\n\t}\n}\nfunc go() -> Int {\n\tlet e = E.a(\"heap\" + \" string payload\")\n\tlet s = steal(e: e)\n\tlet n = s.byte_count\n\tlet m = match e {\n\t\t.a(t) -> t.byte_count\n\t}\n\tn + m\n}\ngo()"
            ),
            Value::I64(38)
        );
    }

    #[test]
    fn borrowed_scrutinee_payload_binder_into_owned_field_balances() {
        // S3 shape 2: the binder flows into an owned aggregate; the clone's
        // buffer is freed by the aggregate's drop, the original by the enum.
        assert_eq!(
            run_on_both_engines(
                "struct Holder {\n\tlet s: String\n}\nenum E {\n\tcase a(String)\n}\nfunc hold(e: E) -> Holder {\n\tmatch e {\n\t\t.a(s) -> Holder(s: s)\n\t}\n}\nfunc go() -> Int {\n\tlet e = E.a(\"xy\" + \"z\")\n\tlet h = hold(e: e)\n\tlet n = h.s.byte_count\n\tlet m = match e {\n\t\t.a(t) -> t.byte_count\n\t}\n\tn + m\n}\ngo()"
            ),
            Value::I64(6)
        );
    }

    #[test]
    fn tuple_nested_borrowed_payload_binder_consume_balances() {
        // S3 shape 3 (ADR 0025's nested case): the binder's projection
        // crosses a borrow below a tuple; consuming it must still retain.
        assert_eq!(
            run_on_both_engines(
                "enum E {\n\tcase a(String)\n}\nfunc first(x: E, y: E) -> String {\n\tmatch (x, y) {\n\t\t(.a(s), _) -> s\n\t}\n}\nfunc go() -> Int {\n\tlet x = E.a(\"ab\" + \"c\")\n\tlet y = E.a(\"de\" + \"f\")\n\tlet s = first(x, y)\n\tlet n = s.byte_count\n\tlet m = match x {\n\t\t.a(t) -> t.byte_count\n\t}\n\tn + m\n}\ngo()"
            ),
            Value::I64(6)
        );
    }

    #[test]
    fn generic_payload_binder_from_borrowed_self_retains_per_instantiation() {
        // The generic body carries the tier-2 mark; the String instantiation
        // resolves it to a retain. Without the mark the arm's `t` would move
        // out of the borrowed receiver and `f`'s drop would free it again.
        assert_eq!(
            run_on_both_engines(
                "enum Fizz<T> {\n\tcase foo(T)\n\n\tfunc unwrap() -> T {\n\t\tmatch self {\n\t\t\t.foo(t) -> t\n\t\t}\n\t}\n}\nfunc go() -> Int {\n\tlet f = Fizz.foo(\"gen\" + \"eric\")\n\tlet s = f.unwrap()\n\tlet n = s.byte_count\n\tlet m = match f {\n\t\t.foo(t) -> t.byte_count\n\t}\n\tn + m\n}\ngo()"
            ),
            Value::I64(14)
        );
    }

    #[test]
    fn default_bind_arm_owns_enum_without_dropping_payload_twice() {
        assert_eq!(
            run_on_both_engines(
                "enum Wrapped { case tagged(String) case empty }\nfunc f() -> Int {\n\tlet w = Wrapped.tagged(\"a\" + \"b\")\n\tmatch w { .empty -> 0, x -> 1 }\n}\nf()"
            ),
            Value::I64(1)
        );
    }

    // ----- Deinit with droppable fields (ownership-soundness S1/R1) -------

    /// A user `Deinit` on a struct with a droppable field: the hook runs
    /// once and the GLUE tears the field down once — the deinit body's own
    /// `self` scope exit must not free the fields a second time.
    #[test]
    fn user_deinit_with_droppable_field_frees_fields_once() {
        let (_, out) = run_on_both_engines_io(
            "struct Loud {\n\tlet s: String\n}\nextend Loud: Deinit {\n\tconsuming func deinit() -> Void {\n\t\tprint(\"bye\")\n\t\t()\n\t}\n}\nfunc f() {\n\tlet x = Loud(s: \"a\" + \"b\")\n}\nf()",
        );
        assert_eq!(out, "bye\n");
    }

    /// The generic twin: the same balance holds when the droppable field's
    /// type arrives through an instantiation.
    #[test]
    fn generic_deinit_with_droppable_field_frees_fields_once() {
        let (_, out) = run_on_both_engines_io(
            "struct Loud<T> {\n\tlet s: T\n}\nextend Loud<T>: Deinit {\n\tconsuming func deinit() -> Void {\n\t\tprint(\"bye\")\n\t\t()\n\t}\n}\nfunc f() {\n\tlet x = Loud(s: \"a\" + \"b\")\n}\nf()",
        );
        assert_eq!(out, "bye\n");
    }

    /// A deinit body that reads a field still leaves teardown to the glue.
    #[test]
    fn deinit_body_reading_a_field_frees_fields_once() {
        let (_, out) = run_on_both_engines_io(
            "struct Loud {\n\tlet s: String\n}\nextend Loud: Deinit {\n\tconsuming func deinit() -> Void {\n\t\tprint(self.s)\n\t\t()\n\t}\n}\nfunc f() {\n\tlet x = Loud(s: \"a\" + \"b\")\n}\nf()",
        );
        assert_eq!(out, "ab\n");
    }

    /// R1: the suppression keys on the VALUE (the body's own `self`), not
    /// the type — a fresh sibling instance created inside its own type's
    /// deinit still runs its hook when it drops.
    #[test]
    fn deinit_constructing_a_sibling_runs_both_hooks() {
        let (_, out) = run_on_both_engines_io(
            "struct Loud {\n\tlet s: String\n\tlet n: Int\n}\nextend Loud: Deinit {\n\tconsuming func deinit() -> Void {\n\t\tprint(\"bye\")\n\t\tif self.n > 0 {\n\t\t\tlet sibling = Loud(s: \"x\" + \"y\", n: self.n - 1)\n\t\t\tprint(\"sibling made\")\n\t\t}\n\t}\n}\nfunc f() {\n\tlet x = Loud(s: \"a\" + \"b\", n: 1)\n}\nf()",
        );
        assert_eq!(out, "bye\nsibling made\nbye\n");
    }

    /// An owned local in a branch-tailed body drops at scope exit exactly
    /// once (StorageDead-paired candidates survive the branch join).
    /// Owned PARAMETERS on this same shape still leak — the diagnosed
    /// `Return`-tail candidate loss in `lower_mir_terminator_inner`, left
    /// in place until the rule-B buffer retain lands (see the comment
    /// there).
    #[test]
    fn owned_local_dropped_when_body_tail_is_a_branch() {
        let (_, out) = run_on_both_engines_io(
            "func f() {\n\tlet s = \"a\" + \"b\"\n\tif 1 < 2 {\n\t\tprint(s)\n\t}\n}\nf()",
        );
        assert_eq!(out, "ab\n");
    }

    #[test]
    fn owned_param_dropped_when_body_tail_is_a_branch() {
        // The parameter twin of the local case above (B10): a body whose
        // tail is a branch join reaches `Terminator::Return` with its
        // ScopeExit candidates unclaimed — owned parameters must drain
        // there (locals are covered by StorageDead pairing). The eval
        // leak fence asserts the balance.
        let (_, out) = run_on_both_engines_io(
            "func f(consume s: String) {\n\tif 1 < 2 {\n\t\tprint(s)\n\t}\n}\nf(\"a\" + \"b\")",
        );
        assert_eq!(out, "ab\n");
    }

    #[test]
    fn heap_constructor_place_read_args_balance_on_both_engines() {
        // S7: consume params (place reads) stored into a `'heap`
        // constructor retain their buffers — the params' scope-exit drops
        // and the region finalizer each free exactly once.
        assert_eq!(
            run_on_both_engines(
                "struct Node 'heap {\n\tlet key: String\n\tlet value: String\n}\nfunc stash(consume key: String, consume value: String) -> Void {\n\tlet n = Node(key: key, value: value)\n\t()\n}\nstash(\"a\" + \"b\", \"c\" + \"d\")"
            ),
            Value::Void
        );
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
            "struct Person {\n\tlet firstName: String\n\tlet lastName: String\n\n\tconsuming func greet() {\n\t\tprint(\"hi i'm \" + self.firstName + \" \" + self.lastName)\n\t}\n}\nPerson(firstName: \"Pat\", lastName: \"N\").greet()",
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
    fn vm_matches_evaluator_on_labeled_enum_payloads() {
        let (value, _) = run_on_both_engines_io(
            "enum Foo {\n\tcase bar(fizz: Int, buzz: String)\n\tcase ok(String)\n}\nlet foo = Foo.bar(fizz: 123, buzz: \"sup\")\nmatch foo {\n\t.bar(fizz: _, buzz: value) -> value.byte_count,\n\t.ok(value) -> value.byte_count\n}",
        );
        assert_eq!(value, Value::I64(3));
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
        let (value, _) =
            run_on_both_engines_io("match 3 {\n\t1 | 2 -> 10,\n\t3 | 4 -> 20,\n\t_ -> 0\n}");
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
        let (value, _) = run_on_both_engines_io("let { x, y } = { x: 3, y: 4 }\nx + y");
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
    fn vm_matches_evaluator_on_array_swap() {
        let (value, _) = run_on_both_engines_io(
            "func main() -> Int {\n\tlet a = [1, 2, 3]\n\ta.swap(0, 2)\n\ta.get(0) * 10 + a.get(2)\n}\nmain()",
        );
        assert_eq!(value, Value::I64(31));
    }

    #[test]
    fn vm_matches_evaluator_on_string_array_swap() {
        let (value, _) = run_on_both_engines_io(
            "func main() -> Int {\n\tlet a = [\"a\", \"bbb\"]\n\ta.swap(0, 1)\n\ta.get(0).byte_count * 10 + a.get(1).byte_count\n}\nmain()",
        );
        assert_eq!(value, Value::I64(31));
    }

    #[test]
    fn vm_matches_evaluator_on_float_array_round_trip() {
        let (_, out) =
            run_on_both_engines_io("let a = [1.5, 2.5]\nprint(a.get(0))\nprint(a.get(1))");
        assert_eq!(out, "1.5\n2.5\n");
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
    fn vm_matches_evaluator_on_subprotocol_conformance_dispatch() {
        let (value, _) = run_on_both_engines_io(
            "protocol A {\n\tfunc a() -> Int\n}\nprotocol B: A {}\nstruct S {}\nextend S: B {}\nextend S: A {\n\tfunc a() -> Int { 1 }\n}\nS().a()",
        );
        assert_eq!(value, Value::I64(1));
    }

    // ----- Iteration/access regression matrix (ADR 0021) ----------------------

    #[test]
    fn vm_for_loop_over_named_array_of_droppable_strings() {
        let (_, out) = run_on_both_engines_io(
            "func main() -> Int {\n\tlet xs = [\"a\" + \"b\", \"c\" + \"d\"]\n\tfor x in xs {\n\t\tprint(x)\n\t}\n\tprint(xs.count)\n\t0\n}",
        );
        assert_eq!(out, "ab\ncd\n2\n");
    }

    #[test]
    fn vm_for_loop_over_rvalue_array() {
        // The rvalue source must live for the whole loop and drop once.
        let (_, out) = run_on_both_engines_io(
            "func make() -> Array<String> {\n\t[\"a\" + \"b\", \"c\" + \"d\"]\n}\nfunc main() -> Int {\n\tfor x in make() {\n\t\tprint(x)\n\t}\n\t0\n}",
        );
        assert_eq!(out, "ab\ncd\n");
    }

    #[test]
    fn vm_for_loop_over_nested_droppable_elements() {
        // Element is itself a droppable container: no double drop of the
        // inner buffer, no leak of the outer one.
        let (_, out) = run_on_both_engines_io(
            "func main() -> Int {\n\tlet a = [[\"x\" + \"y\"]]\n\tfor row in a {\n\t\tprint(row.count)\n\t}\n\tprint(a.count)\n\t0\n}",
        );
        assert_eq!(out, "1\n1\n");
    }

    #[test]
    fn vm_for_loop_break_drops_per_iteration_binders() {
        let (_, out) = run_on_both_engines_io(
            "func main() -> Int {\n\tlet xs = [\"a\" + \"b\", \"c\" + \"d\", \"e\" + \"f\"]\n\tlet i = 0\n\tfor x in xs {\n\t\tif i == 1 {\n\t\t\tbreak\n\t\t}\n\t\tprint(x)\n\t\ti = i + 1\n\t}\n\tprint(xs.count)\n\t0\n}",
        );
        assert_eq!(out, "ab\n3\n");
    }

    #[test]
    fn vm_for_loop_continue_drops_per_iteration_binders() {
        let (_, out) = run_on_both_engines_io(
            "func main() -> Int {\n\tlet xs = [\"a\" + \"b\", \"c\" + \"d\"]\n\tlet i = 0\n\tfor x in xs {\n\t\ti = i + 1\n\t\tif i == 1 {\n\t\t\tcontinue\n\t\t}\n\t\tprint(x)\n\t}\n\t0\n}",
        );
        assert_eq!(out, "cd\n");
    }

    #[test]
    fn vm_two_shared_iterators_over_one_array_interleave() {
        let (_, out) = run_on_both_engines_io(
            "func main() -> Int {\n\tlet a = [7, 8]\n\tlet it1 = a.iter()\n\tlet it2 = a.iter()\n\tif let .some(v) = it1.next() { print(v) }\n\tif let .some(v) = it2.next() { print(v) }\n\tif let .some(v) = it1.next() { print(v) }\n\t0\n}",
        );
        assert_eq!(out, "7\n7\n8\n");
    }

    #[test]
    fn vm_match_on_borrowed_loop_element_leaves_source_intact() {
        // Matching through the borrowed element must not move or drop the
        // array's payload; the source stays usable after the loop.
        let (_, out) = run_on_both_engines_io(
            "enum Entry {\n\tcase doc(String)\n}\nfunc main() -> Int {\n\tlet entries = [Entry.doc(\"a\" + \"b\")]\n\tfor entry in entries {\n\t\tmatch entry {\n\t\t\t.doc(s) -> print(s)\n\t\t}\n\t}\n\tprint(entries.count)\n\t0\n}",
        );
        assert_eq!(out, "ab\n1\n");
    }

    #[test]
    fn vm_mut_receiver_method_through_owned_field() {
        // `self.inner.bump()` inside a `mut func`: exclusive access via
        // projection through the exclusive root, written back per call.
        let (_, out) = run_on_both_engines_io(
            "struct Inner {\n\tlet value: Int\n\tmut func bump() -> Int {\n\t\tself.value = self.value + 1\n\t\tself.value\n\t}\n}\nstruct Outer {\n\tlet inner: Inner\n\tmut func poke() -> Int {\n\t\tself.inner.bump()\n\t}\n}\nfunc main() -> Int {\n\tlet o = Outer(inner: Inner(value: 1))\n\tprint(o.poke())\n\tprint(o.poke())\n\t0\n}",
        );
        assert_eq!(out, "2\n3\n");
    }

    #[test]
    fn vm_manual_iterator_next_over_droppable_strings() {
        let (_, out) = run_on_both_engines_io(
            "func main() -> Int {\n\tlet xs = [\"a\" + \"b\"]\n\tlet it = xs.iter()\n\tif let .some(s) = it.next() { print(s) }\n\tmatch it.next() {\n\t\t.some(s) -> print(s),\n\t\t.none -> print(0 - 1)\n\t}\n\tprint(xs.count)\n\t0\n}",
        );
        assert_eq!(out, "ab\n-1\n1\n");
    }

    #[test]
    fn vm_for_loop_over_borrowed_receiver_method_source_feeds_borrow_callback() {
        // ADR 0017 bug B: a same-module method on a BORROWED receiver as
        // the for-source. The binder must type `&Array<String>` exactly as
        // it does with a free-function source, and the loop must run
        // balanced (no per-iteration drop of the source's elements).
        let (_, out) = run_on_both_engines_io(
            "struct D {\n\tlet name: String\n\tfunc make() -> Array<Array<String>> {\n\t\t[[\"x\" + \"y\"]]\n\t}\n}\nfunc walk(d: &D, fn: (&Array<String>) -> ()) {\n\tfor item in d.make() {\n\t\tfn(item)\n\t}\n}\nfunc main() -> Int {\n\tlet d = D(name: \"d\" + \"!\")\n\twalk(d) { row in\n\t\tprint(row.count)\n\t}\n\t0\n}",
        );
        assert_eq!(out, "1\n");
    }

    #[test]
    fn vm_for_loop_over_free_function_source_feeds_borrow_callback() {
        // Free-function twin of the borrowed-receiver-method shape above:
        // the control that pins ADR 0017 bug B to the method path.
        let (_, out) = run_on_both_engines_io(
            "func make() -> Array<Array<String>> {\n\t[[\"x\" + \"y\"]]\n}\nfunc walk(fn: (&Array<String>) -> ()) {\n\tfor item in make() {\n\t\tfn(item)\n\t}\n}\nfunc main() -> Int {\n\twalk() { row in\n\t\tprint(row.count)\n\t}\n\t0\n}",
        );
        assert_eq!(out, "1\n");
    }

    #[test]
    fn vm_for_loop_element_feeds_borrow_callback() {
        let (_, out) = run_on_both_engines_io(
            "func each(entries: Array<String>, fn: (&String) -> ()) {\n\tfor e in entries {\n\t\tfn(e)\n\t}\n}\nfunc main() -> Int {\n\tlet xs = [\"a\" + \"b\", \"c\" + \"d\"]\n\teach(xs) { e in\n\t\tprint(e)\n\t}\n\t0\n}",
        );
        assert_eq!(out, "ab\ncd\n");
    }

    #[test]
    fn vm_for_loop_over_skip_adapter_chain() {
        // An adapter chain is already an Iterator: `for` consumes it into
        // the hidden iterator via the Iterator protocol's identity iter().
        let (_, out) = run_on_both_engines_io(
            "func main() -> Int {\n\tlet a = [1, 2, 3]\n\tfor i in a.iter().skip(1) {\n\t\tprint(i)\n\t}\n\tprint(a.count)\n\t0\n}",
        );
        assert_eq!(out, "2\n3\n3\n");
    }

    #[test]
    fn vm_for_loop_over_map_adapter() {
        // `map` consumes its upstream iterator and stores it by value; the
        // Map iterator yields owned mapped values.
        let (_, out) = run_on_both_engines_io(
            "func main() -> Int {\n\tlet a = [1, 2, 3]\n\tlet doubled = a.iter().map() { i in i * 2 }\n\tfor i in doubled {\n\t\tprint(i)\n\t}\n\t0\n}",
        );
        assert_eq!(out, "2\n4\n6\n");
    }

    #[test]
    fn vm_consume_for_loop_moves_elements_out() {
        // `for x in consume xs`: xs moves into the loop-owned iterator and
        // is dead afterwards; elements are drained out of the array's
        // storage as owned values.
        let (_, out) = run_on_both_engines_io(
            "func main() -> Int {\n\tlet xs = [\"a\" + \"b\", \"c\" + \"d\"]\n\tfor x in consume xs {\n\t\tprint(x)\n\t}\n\t0\n}",
        );
        assert_eq!(out, "ab\ncd\n");
    }

    #[test]
    fn vm_consume_for_loop_moves_non_cheap_clone_elements_out() {
        let (_, out) = run_on_both_engines_io(
            "struct Item {\n\tlet name: String\n}\nfunc main() -> Int {\n\tlet xs = [Item(name: \"a\" + \"b\")]\n\tfor item in consume xs {\n\t\tprint(item.name)\n\t}\n\t0\n}",
        );
        assert_eq!(out, "ab\n");
    }

    #[test]
    fn vm_consume_for_loop_elements_feed_consuming_callback() {
        // Owned elements can move into a `consume` parameter.
        let (_, out) = run_on_both_engines_io(
            "func takes(consume s: String) {\n\tprint(s)\n}\nfunc main() -> Int {\n\tlet xs = [\"a\" + \"b\"]\n\tfor x in consume xs {\n\t\ttakes(consume x)\n\t}\n\t0\n}",
        );
        assert_eq!(out, "ab\n");
    }

    #[test]
    fn vm_generic_borrowed_payload_coerces_into_owned_slot() {
        // The per-instantiation clone coercion end-to-end: a borrowed
        // argument fills an owned generic enum payload by retaining.
        let (_, out) = run_on_both_engines_io(
            "enum Box2<T> {\n\tcase full(T)\n}\nfunc wrap<T: CheapClone>(v: &T) -> Box2<T> {\n\tBox2.full(v)\n}\nfunc main() -> Int {\n\tlet s = \"a\" + \"b\"\n\tlet b = wrap(s)\n\tmatch b {\n\t\t.full(v) -> print(v)\n\t}\n\t0\n}",
        );
        assert_eq!(out, "ab\n");
    }

    #[test]
    fn vm_mutated_array_local_drops_balanced() {
        // A mutated (celled) array local: push reallocs, the old buffer is
        // released by the storage-field replacement, the new one by the
        // final drop.
        let (_, out) = run_on_both_engines_io(
            "func main() -> Int {\n\tlet xs = [5]\n\txs.push(6)\n\tprint(xs.count)\n\t0\n}",
        );
        assert_eq!(out, "2\n");
    }

    #[test]
    fn vm_reassigned_shared_array_keeps_sharer_alive() {
        // ys shares xs's buffer; reassigning xs must not free what ys
        // still reads.
        let (_, out) = run_on_both_engines_io(
            "func main() -> Int {\n\tlet xs = [5]\n\txs.push(6)\n\tlet ys = xs\n\txs = [7]\n\tprint(xs.count)\n\tprint(ys.count)\n\t0\n}",
        );
        assert_eq!(out, "1\n2\n");
    }

    #[test]
    fn vm_mut_for_loop_writes_back_ints() {
        let (_, out) = run_on_both_engines_io(
            "func main() -> Int {\n\tlet xs = [1, 2, 3]\n\tfor x in mut xs {\n\t\tx = x * 2\n\t}\n\tfor x in xs {\n\t\tprint(x)\n\t}\n\t0\n}",
        );
        assert_eq!(out, "2\n4\n6\n");
    }

    #[test]
    fn vm_mut_for_loop_writes_back_droppable_strings() {
        let (_, out) = run_on_both_engines_io(
            "func main() -> Int {\n\tlet xs = [\"a\" + \"b\", \"c\" + \"d\"]\n\tfor s in mut xs {\n\t\ts = s + \"!\"\n\t}\n\tfor s in xs {\n\t\tprint(s)\n\t}\n\t0\n}",
        );
        assert_eq!(out, "ab!\ncd!\n");
    }

    #[test]
    fn vm_mut_for_loop_writes_back_non_cheap_clone_elements() {
        let (_, out) = run_on_both_engines_io(
            "struct Item {\n\tlet name: String\n}\nfunc main() -> Int {\n\tlet xs = [Item(name: \"a\" + \"b\")]\n\tfor item in mut xs {\n\t\titem = Item(name: item.name + \"!\")\n\t}\n\tfor item in xs {\n\t\tprint(item.name)\n\t}\n\t0\n}",
        );
        assert_eq!(out, "ab!\n");
    }

    #[test]
    fn vm_mut_for_loop_source_usable_after() {
        let (_, out) = run_on_both_engines_io(
            "func main() -> Int {\n\tlet xs = [5]\n\tfor x in mut xs {\n\t\tx = x + 1\n\t}\n\tprint(xs.count)\n\tprint(xs.get(0))\n\t0\n}",
        );
        assert_eq!(out, "1\n6\n");
    }

    #[test]
    fn vm_mut_for_loop_source_can_be_mut_borrowed_again_after() {
        let (_, out) = run_on_both_engines_io(
            "func touch(xs: &mut Array<Int>) -> Int {\n\txs.push(9)\n\txs.count\n}\nfunc main() -> Int {\n\tlet xs = [5]\n\tfor x in mut xs {\n\t\tx = x + 1\n\t}\n\tprint(touch(xs))\n\tprint(xs.get(0))\n\tprint(xs.get(1))\n\t0\n}",
        );
        assert_eq!(out, "2\n6\n9\n");
    }

    #[test]
    fn vm_consuming_protocol_default_on_borrowed_projection() {
        // Paint.daub(item.name) consumes a String projected out of the
        // borrowed loop binder; the copy-out-of-borrow retain must be
        // emitted or the array's deep-drop releases the name twice.
        let (_, out) = run_on_both_engines_io(
            "protocol Paint where Self: Showable {\n\tconsuming func daub() -> String {\n\t\t\"*\" + self.show()\n\t}\n}\nextend String: Paint {}\nstruct Item {\n\tlet name: String\n}\nfunc main() -> Int {\n\tlet items = [Item(name: \"ab\".to_string())]\n\tfor item in items {\n\t\tprint(Paint.daub(item.name))\n\t}\n\t0\n}",
        );
        assert_eq!(out, "*ab\n");
    }

    #[test]
    fn vm_matches_evaluator_on_array_iterator_next() {
        // ArrayIterator.next() is a mutating witness: inout self writes
        // back into the iterator's cell between calls.
        let (_, out) = run_on_both_engines_io(
            "func main() -> Int {\n\tlet numbers = [7, 8]\n\tlet it = numbers.iter()\n\tlet r1: Optional<Int> = it.next()\n\tmatch r1 {\n\t\t.some(v) -> print(v),\n\t\t.none -> print(0 - 1)\n\t}\n\tlet r2: Optional<Int> = it.next()\n\tmatch r2 {\n\t\t.some(v) -> print(v),\n\t\t.none -> print(0 - 1)\n\t}\n\tlet r3: Optional<Int> = it.next()\n\tmatch r3 {\n\t\t.some(v) -> print(v),\n\t\t.none -> print(0 - 1)\n\t}\n\t0\n}",
        );
        assert_eq!(out, "7\n8\n-1\n");
    }

    #[test]
    fn vm_sums_borrowed_scalar_elements() {
        // arr.get returns &Int; a Copy-grade scalar extracts from the
        // borrow for free, so it feeds owned arithmetic directly.
        let (_, out) = run_on_both_engines_io(
            "func f() -> Int {\n\tlet arr = [10, 20, 30]\n\tlet sum = 0\n\tlet j = 0\n\tloop {\n\t\tif j >= arr.count {\n\t\t\tbreak\n\t\t}\n\t\tsum = sum + arr.get(j)\n\t\tj = j + 1\n\t}\n\tsum\n}\nprint(f())",
        );
        assert_eq!(out, "60\n");
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

    #[test]
    fn vm_matches_evaluator_on_derived_equatable() {
        let (_, out) = run_on_both_engines_io(
            "struct Point {\n\tlet x: Int\n\tlet y: Int\n}\nenum Choice {\n\tcase none\n\tcase value(Int)\n\tcase pair(Int, Bool)\n}\nenum Chain {\n\tcase end\n\tcase link(Int, Chain)\n}\nprint(Point(x: 1, y: 2) == Point(x: 1, y: 2))\nprint(Point(x: 1, y: 2).equals(rhs: Point(x: 1, y: 2)))\nprint(Point(x: 1, y: 2) != Point(x: 1, y: 3))\nprint(Choice.value(4) == Choice.value(4))\nprint(Choice.value(4) == Choice.value(5))\nprint(Choice.value(4) == Choice.none)\nprint(Choice.pair(4, true) != Choice.pair(4, false))\nprint(Chain.link(1, Chain.end) == Chain.link(1, Chain.end))",
        );
        assert_eq!(out, "true\ntrue\ntrue\ntrue\nfalse\nfalse\ntrue\ntrue\n");
    }

    // ----- Drop schedules on early exits and match joins ----------------------

    #[test]
    fn vm_break_after_move_frees_once() {
        // The loop-local was moved into consume(); the break path must not
        // free it a second time.
        let (_, out) = run_on_both_engines_io(
            "func consume(x: String) -> Int {\n\tx.byte_count\n}\nfunc f() -> Int {\n\tloop {\n\t\tlet s = \"a\" + \"b\"\n\t\tlet n = consume(s)\n\t\tbreak\n\t}\n\t0\n}\nprint(f())",
        );
        assert_eq!(out, "0\n");
    }

    #[test]
    fn vm_or_pattern_binder_drops_once() {
        // `.a(s) | .b(s)` binds one `s`; its scope-exit drop must be
        // scheduled once, not once per or-alternative.
        let (_, out) = run_on_both_engines_io(
            "enum E {\n\tcase a(String)\n\tcase b(String)\n}\nfunc main() -> Int {\n\tlet e = E.a(\"x\" + \"y\")\n\tmatch e {\n\t\t.a(s) | .b(s) -> print(s),\n\t}\n\t0\n}",
        );
        assert_eq!(out, "xy\n");
    }

    #[test]
    fn vm_taken_literal_match_arm_frees_scrutinee() {
        // B8: the pattern compiler freed owned occurrences only for
        // WILDCARD cells, so the taken "ab" arm leaked the RVALUE scrutinee
        // (a place scrutinee matches through a borrow and is unaffected)
        // while the `_` arm balanced. Both arms exercised; the evaluator
        // leak fence (scalar results) asserts the balance.
        let (_, out) = run_on_both_engines_io(
            "func g(z: Bool) -> String {\n\tif z {\n\t\t\"a\" + \"b\"\n\t} else {\n\t\t\"z\" + \"zz\"\n\t}\n}\nfunc m(z: Bool) -> Int {\n\tmatch g(z) {\n\t\t\"ab\" -> 1,\n\t\t_ -> 2,\n\t}\n}\nprint(m(true))\nprint(m(false))",
        );
        assert_eq!(out, "1\n2\n");
    }

    #[test]
    fn vm_literal_arm_nested_in_enum_pattern_frees_payload() {
        // B8, nested shape: the String literal cell is a variant PAYLOAD
        // occurrence; matching it must free the payload exactly as the
        // `.some(_)` wildcard cell does.
        let (_, out) = run_on_both_engines_io(
            "func mk(flag: Bool) -> Optional<String> {\n\tif flag {\n\t\tOptional.some(\"a\" + \"b\")\n\t} else {\n\t\tOptional.some(\"z\" + \"zz\")\n\t}\n}\nfunc m(flag: Bool) -> Int {\n\tmatch mk(flag) {\n\t\t.some(\"ab\") -> 1,\n\t\t.some(_) -> 2,\n\t\t.none -> 3,\n\t}\n}\nprint(m(true))\nprint(m(false))",
        );
        assert_eq!(out, "1\n2\n");
    }

    #[test]
    fn vm_or_pattern_literal_arm_frees_scrutinee_once() {
        // B8, or-pattern shape (Talk has no match guards): each alternative
        // expands to its own row, and whichever alternative matches must
        // free the rvalue scrutinee exactly once.
        let (_, out) = run_on_both_engines_io(
            "func mk(i: Int) -> String {\n\tif i == 0 {\n\t\t\"a\" + \"b\"\n\t} else {\n\t\tif i == 1 {\n\t\t\t\"x\" + \"y\"\n\t\t} else {\n\t\t\t\"q\" + \"q\"\n\t\t}\n\t}\n}\nfunc m(i: Int) -> Int {\n\tmatch mk(i) {\n\t\t\"xy\" | \"ab\" -> 1,\n\t\t_ -> 2,\n\t}\n}\nprint(m(0))\nprint(m(1))\nprint(m(2))",
        );
        assert_eq!(out, "1\n1\n2\n");
    }

    #[test]
    fn vm_literal_match_binder_arm_does_not_double_free() {
        // B8 fence: the binder arm takes ownership of the scrutinee — the
        // matched-literal free must not also fire for binder rows.
        let (_, out) = run_on_both_engines_io(
            "func mk(z: Bool) -> String {\n\tif z {\n\t\t\"a\" + \"b\"\n\t} else {\n\t\t\"c\" + \"de\"\n\t}\n}\nfunc m(z: Bool) -> Int {\n\tmatch mk(z) {\n\t\t\"ab\" -> 1,\n\t\tx -> x.byte_count,\n\t}\n}\nprint(m(true))\nprint(m(false))",
        );
        assert_eq!(out, "1\n3\n");
    }

    #[test]
    fn vm_borrowed_scrutinee_literal_match_stays_balanced() {
        // B8 fence: a literal match through a borrow is an alias — the
        // taken arm must NOT free what the owner still holds.
        let (_, out) = run_on_both_engines_io(
            "func pick(s: &String) -> Int {\n\tmatch s {\n\t\t\"ab\" -> 1,\n\t\t_ -> 2,\n\t}\n}\nfunc main() -> Int {\n\tlet s = \"a\" + \"b\"\n\tlet a = pick(s)\n\ta + s.byte_count\n}\nprint(main())",
        );
        assert_eq!(out, "3\n");
    }

    #[test]
    fn vm_projection_of_call_result_frees_the_temp() {
        // B9: `g().byte_count` — the rvalue call under a projection must
        // evaluate at its own Call statement with a TemporaryEnd temp;
        // boundary Reads alone leaked the result. The evaluator leak
        // fence (scalar result) asserts the balance.
        let (_, out) = run_on_both_engines_io(
            "func g() -> String {\n\t\"a\" + \"b\"\n}\nfunc f() -> Int {\n\tg().byte_count\n}\nprint(f())",
        );
        assert_eq!(out, "2\n");
    }

    #[test]
    fn vm_chained_projection_of_call_result_frees_the_temp() {
        // B9, chained shape: the projection chain rides the SAME temp —
        // `mk().inner.byte_count` reads through the temp's field (borrow
        // provenance into the temp), and the temp's teardown frees the
        // struct exactly once.
        let (_, out) = run_on_both_engines_io(
            "struct Wrap {\n\tlet inner: String\n}\nfunc mk() -> Wrap {\n\tWrap(inner: \"a\" + \"b\")\n}\nfunc f() -> Int {\n\tmk().inner.byte_count\n}\nprint(f())",
        );
        assert_eq!(out, "2\n");
    }

    #[test]
    fn vm_projection_of_call_in_loop_frees_per_iteration() {
        // B9, loop shape: one temp per iteration, each freed on its own
        // iteration — three iterations leak exactly zero.
        let (_, out) = run_on_both_engines_io(
            "func g() -> String {\n\t\"a\" + \"b\"\n}\nfunc f() -> Int {\n\tlet i = 0\n\tlet total = 0\n\tloop i < 3 {\n\t\ti = i + 1\n\t\ttotal = total + g().byte_count\n\t}\n\ttotal\n}\nprint(f())",
        );
        assert_eq!(out, "6\n");
    }

    #[test]
    fn vm_consuming_field_projection_of_call_retains_not_double_frees() {
        // B9 consume shape: `let s = mk().inner` binds a CheapClone field
        // out of the call temp. The extraction retains (tier 2), so the
        // temp's teardown and `s`'s scope exit each free exactly once.
        let (_, out) = run_on_both_engines_io(
            "struct Wrap {\n\tlet inner: String\n}\nfunc mk() -> Wrap {\n\tWrap(inner: \"a\" + \"b\")\n}\nfunc f() -> Int {\n\tlet s = mk().inner\n\ts.byte_count\n}\nprint(f())",
        );
        assert_eq!(out, "2\n");
    }

    #[test]
    fn vm_consuming_noncheap_projection_of_call_takes_the_temp() {
        // B9 consume shape, non-retainable field: the extraction takes the
        // whole temp (its candidate classifies Dead), and the extracted
        // value's own teardown frees the buffers once — the pre-B9 shape,
        // with no double free.
        let (_, out) = run_on_both_engines_io(
            "struct Inner {\n\tlet s: String\n}\nstruct Outer {\n\tlet i: Inner\n}\nfunc mk() -> Outer {\n\tOuter(i: Inner(s: \"a\" + \"b\"))\n}\nfunc f() -> Int {\n\tlet x = mk().i\n\tx.s.byte_count\n}\nprint(f())",
        );
        assert_eq!(out, "2\n");
    }

    #[test]
    fn vm_projection_of_call_as_match_scrutinee_frees_the_temp() {
        // B9, scrutinee position: the projection's temp drains at the
        // match's own statement boundary on both arm paths.
        let (_, out) = run_on_both_engines_io(
            "func g(z: Bool) -> String {\n\tif z {\n\t\t\"a\" + \"b\"\n\t} else {\n\t\t\"z\" + \"zz\"\n\t}\n}\nfunc f(z: Bool) -> Int {\n\tmatch g(z).byte_count {\n\t\t2 -> 1,\n\t\t_ -> 2,\n\t}\n}\nprint(f(true))\nprint(f(false))",
        );
        assert_eq!(out, "1\n2\n");
    }

    #[test]
    fn vm_statements_after_match_with_diverging_arm_run() {
        // A match with one diverging arm still delivers value-arm results
        // to the join: the binding and everything after the match run.
        let (_, out) = run_on_both_engines_io(
            "func pick(m: Optional<Int>) -> Int {\n\tlet x = match m {\n\t\t.some(v) -> v,\n\t\t.none -> return 0,\n\t}\n\tprint(\"after match\")\n\tx + 1\n}\nprint(pick(Optional.some(10)))",
        );
        assert_eq!(out, "after match\n11\n");
    }

    #[test]
    fn vm_break_inside_expression_position_if_arm() {
        // The break is a CFG edge out of the arm block: the binding never
        // happens on that path, and the loop exits with the accumulator.
        let (_, out) = run_on_both_engines_io(
            "func f(n: Int) -> Int {\n\tlet total = 0\n\tlet i = 0\n\tloop i < 5 {\n\t\ti = i + 1\n\t\tlet x = if (i == n) { break } else { i }\n\t\ttotal = total + x\n\t}\n\ttotal\n}\nprint(f(3))\nprint(f(99))",
        );
        assert_eq!(out, "3\n15\n");
    }

    #[test]
    fn vm_continue_inside_expression_position_if_arm() {
        let (_, out) = run_on_both_engines_io(
            "func f() -> Int {\n\tlet total = 0\n\tlet i = 0\n\tloop i < 5 {\n\t\ti = i + 1\n\t\tlet x = if (i == 3) {\n\t\t\tcontinue\n\t\t} else {\n\t\t\ti\n\t\t}\n\t\ttotal = total + x\n\t}\n\ttotal\n}\nprint(f())",
        );
        assert_eq!(out, "12\n");
    }

    #[test]
    fn vm_move_inside_expression_position_if_arm() {
        // The moved-on-one-path local needs a drop flag that both arms of
        // the expression-position if maintain correctly.
        let (_, out) = run_on_both_engines_io(
            "func consume(x: String) -> Int {\n\tx.byte_count\n}\nfunc f(n: Int) -> Int {\n\tlet s = \"a\" + \"b\"\n\tlet x = if n > 0 { consume(s) } else { 0 }\n\tx\n}\nprint(f(1))\nprint(f(0))",
        );
        assert_eq!(out, "2\n0\n");
    }

    #[test]
    fn vm_match_with_break_arm_inside_loop() {
        let (_, out) = run_on_both_engines_io(
            "func f() -> Int {\n\tlet i = 0\n\tlet total = 0\n\tloop {\n\t\tlet step = match i < 3 {\n\t\t\ttrue -> 1,\n\t\t\tfalse -> break,\n\t\t}\n\t\ttotal = total + step\n\t\ti = i + 1\n\t}\n\ttotal\n}\nprint(f())",
        );
        assert_eq!(out, "3\n");
    }

    #[test]
    fn vm_return_from_match_arm_drains_pending_statement_temp() {
        // g()'s call temp (borrowed by len, so unconsumed) normally drains
        // at the match join; a `return` arm bypasses the join, so the exit
        // edge must drain it.
        let (_, out) = run_on_both_engines_io(
            "func len(s: String) -> Int {\n\ts.byte_count\n}\nfunc g() -> String {\n\t\"a\" + \"b\"\n}\nfunc f() -> Int {\n\tlet a = match len(g()) {\n\t\t2 -> return 1,\n\t\t_ -> 2,\n\t}\n\ta\n}\nprint(f())",
        );
        assert_eq!(out, "1\n");
    }

    #[test]
    fn vm_return_from_match_arm_untaken_path_still_balanced() {
        // Taken exit drains on the exit edge, untaken drains at the join —
        // per-path exact: the same temp must not free twice on either run.
        let (_, out) = run_on_both_engines_io(
            "func len(s: String) -> Int {\n\ts.byte_count\n}\nfunc mk(s: String) -> String {\n\ts + \"!\"\n}\nfunc f(s: String) -> Int {\n\tlet a = match len(mk(s)) {\n\t\t3 -> return 1,\n\t\t_ -> 2,\n\t}\n\ta\n}\nprint(f(\"ab\"))\nprint(f(\"zzzz\"))",
        );
        assert_eq!(out, "1\n2\n");
    }

    #[test]
    fn vm_break_from_match_arm_drains_pending_statement_temp() {
        let (_, out) = run_on_both_engines_io(
            "func len(s: String) -> Int {\n\ts.byte_count\n}\nfunc g() -> String {\n\t\"a\" + \"b\"\n}\nfunc f() -> Int {\n\tlet total = 0\n\tloop {\n\t\tlet a = match len(g()) {\n\t\t\t2 -> break,\n\t\t\t_ -> 1,\n\t\t}\n\t\ttotal = total + a\n\t}\n\ttotal\n}\nprint(f())",
        );
        assert_eq!(out, "0\n");
    }

    #[test]
    fn vm_break_from_match_arm_after_untaken_iterations_balanced() {
        // Two join-drained iterations, then a break-drained one: no leak
        // and no double free across the mix.
        let (_, out) = run_on_both_engines_io(
            "func pick(s: String, i: Int) -> Int {\n\ts.byte_count + i\n}\nfunc g() -> String {\n\t\"a\" + \"b\"\n}\nfunc f() -> Int {\n\tlet i = 0\n\tlet total = 0\n\tloop {\n\t\ti = i + 1\n\t\tlet a = match pick(g(), i) {\n\t\t\t5 -> break,\n\t\t\t_ -> 1,\n\t\t}\n\t\ttotal = total + a\n\t}\n\ttotal\n}\nprint(f())",
        );
        assert_eq!(out, "2\n");
    }

    #[test]
    fn vm_continue_from_match_arm_drains_temp_every_iteration() {
        // `continue` bypasses the join once per iteration: three taken
        // continues must leak exactly zero temps, not three.
        let (_, out) = run_on_both_engines_io(
            "func len(s: String) -> Int {\n\ts.byte_count\n}\nfunc g() -> String {\n\t\"a\" + \"b\"\n}\nfunc f() -> Int {\n\tlet i = 0\n\tlet total = 0\n\tloop i < 3 {\n\t\ti = i + 1\n\t\tlet a = match len(g()) {\n\t\t\t2 -> {\n\t\t\t\tcontinue\n\t\t\t},\n\t\t\t_ -> 2,\n\t\t}\n\t\ttotal = total + a\n\t}\n\ttotal\n}\nprint(f())",
        );
        assert_eq!(out, "0\n");
    }

    #[test]
    fn vm_return_from_expression_if_drains_condition_temp() {
        // Expression-position `if` desugars to a match on its condition;
        // the condition's call temp rides the enclosing statement.
        let (_, out) = run_on_both_engines_io(
            "func len(s: String) -> Int {\n\ts.byte_count\n}\nfunc g() -> String {\n\t\"a\" + \"b\"\n}\nfunc f(n: Int) -> Int {\n\tlet a = if (len(g()) == n) {\n\t\treturn 1\n\t} else {\n\t\t2\n\t}\n\ta\n}\nprint(f(2))\nprint(f(9))",
        );
        assert_eq!(out, "1\n2\n");
    }

    #[test]
    fn vm_return_through_short_circuit_drains_left_temp() {
        // `&&` desugars to a nested match; the droppable temp on its left
        // is pending across both joins when the return arm is taken.
        let (_, out) = run_on_both_engines_io(
            "func len(s: String) -> Int {\n\ts.byte_count\n}\nfunc g() -> String {\n\t\"a\" + \"b\"\n}\nfunc f(n: Int) -> Int {\n\tlet a = if (len(g()) == 2 && n > 0) {\n\t\treturn 1\n\t} else {\n\t\t2\n\t}\n\ta\n}\nprint(f(1))\nprint(f(0))",
        );
        assert_eq!(out, "1\n2\n");
    }

    #[test]
    fn vm_return_from_nested_match_arm_drains_both_levels() {
        // A return from the inner match's arm bypasses both joins: temps
        // at both nesting levels drain on the one exit edge.
        let (_, out) = run_on_both_engines_io(
            "func len(s: String) -> Int {\n\ts.byte_count\n}\nfunc g() -> String {\n\t\"a\" + \"b\"\n}\nfunc h() -> String {\n\t\"c\" + \"de\"\n}\nfunc f() -> Int {\n\tlet a = match len(g()) {\n\t\t2 -> match len(h()) {\n\t\t\t3 -> return 1,\n\t\t\t_ -> 2,\n\t\t},\n\t\t_ -> 3,\n\t}\n\ta\n}\nprint(f())",
        );
        assert_eq!(out, "1\n");
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
    fn trailing_block_call_arg_temp_drops_after_callee_returns() {
        let (_, out) = run_on_both_engines_io(
            "func twice(path: &Path, fn: () -> ()) {\n\tfn()\n\tfn()\n}\ntwice(Path([\".\"])) { print(\"tick\") }",
        );
        assert_eq!(out, "tick\ntick\n");
    }

    #[test]
    fn trailing_block_isolates_the_whole_statement_scope_bundle() {
        // ADR 0017 stage 4 characterization: a trailing block containing a
        // loop with break/continue, a droppable local, and an early return
        // — inside a call with its own pending arg temp (`Path`), itself
        // inside an enclosing loop. Every statement-scoped builder field
        // (loop targets, pending-temp frames, early-exit scopes) must stay
        // isolated from the enclosing statement's values.
        let (_, out) = run_on_both_engines_io(
            "func run(path: &Path, fn: () -> ()) {\n\tfn()\n\tfn()\n}\nfunc main() -> Int {\n\tlet outer = 0\n\tloop outer < 2 {\n\t\touter = outer + 1\n\t\trun(Path([\".\"])) {\n\t\t\tlet held = \"a\" + \"b\"\n\t\t\tlet j = 0\n\t\t\tloop j < 3 {\n\t\t\t\tj = j + 1\n\t\t\t\tif j == 1 {\n\t\t\t\t\tcontinue\n\t\t\t\t}\n\t\t\t\tbreak\n\t\t\t}\n\t\t\tif j == 2 {\n\t\t\t\tprint(held)\n\t\t\t\treturn\n\t\t\t}\n\t\t\tprint(\"unreachable\")\n\t\t}\n\t}\n\tprint(outer)\n\t0\n}",
        );
        assert_eq!(out, "ab\nab\nab\nab\n2\n");
    }

    #[test]
    fn trailing_block_tail_inside_value_block_returns_to_its_own_caller() {
        // Found landing ADR 0017 stage 4: `block_value_temps` leaked into
        // embedded bodies, so a trailing block's tail delivered to the
        // ENCLOSING block expression's temp instead of the closure's own
        // return — λ_G construction panicked (T-App: argument () does not
        // match domain int). The wholesale statement-scope swap isolates
        // it by construction.
        let (_, out) = run_on_both_engines_io(
            "func call(fn: () -> Int) -> Int {\n\tfn()\n}\nfunc main() -> Int {\n\tlet x = {\n\t\tlet y = call {\n\t\t\t5\n\t\t}\n\t\ty + 1\n\t}\n\tprint(x)\n\t0\n}",
        );
        assert_eq!(out, "6\n");
    }

    #[test]
    fn early_return_from_value_block_arg_drops_pending_call_temps() {
        // A value-position block is a value construct like a match: a
        // `return` inside it bypasses the statement's join, so the temps
        // already materialized for the statement (g()'s result) must
        // drain on the exit edge (`enclosing_temps`), exactly as they
        // would from a match arm. The run fences catch the leak.
        let (_, out) = run_on_both_engines_io(
            "func g() -> String {\n\t\"a\" + \"b\"\n}\nfunc h(a: String, b: Int, c: Int) -> Int {\n\ta.byte_count * 100 + b * 10 + c\n}\nfunc f(flag: Bool) -> Int {\n\th(g(), {\n\t\tif flag {\n\t\t\treturn 5\n\t\t}\n\t\t2\n\t}, 1)\n}\nprint(f(true))\nprint(f(false))",
        );
        assert_eq!(out, "5\n221\n");
    }

    #[test]
    fn trailing_block_tail_inside_match_arm_returns_to_its_own_caller() {
        // The `continuation_temps` twin of the shape above: a trailing
        // block's value tail inside an expression-position match arm is
        // the closure's return, never a continuation into the enclosing
        // match's join.
        let (_, out) = run_on_both_engines_io(
            "func call(fn: () -> Int) -> Int {\n\tfn()\n}\nfunc main() -> Int {\n\tlet v = match 1 {\n\t\t1 -> call {\n\t\t\t5\n\t\t},\n\t\t_ -> 0,\n\t}\n\tprint(v)\n\t0\n}",
        );
        assert_eq!(out, "5\n");
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

    // ----- ADR 0027: aborts unwind through lowerer-emitted cleanup --------
    // The nine acceptance tests: aborting handlers run the suspended
    // frames' drops instead of discarding them. The run helpers' leak
    // fences (evaluator balance + VM run_counted) assert the balance.

    #[test]
    fn abort_unwind_frees_performer_frame_locals() {
        // ADR 0027 test 1 (shape 1): the performing frame's owned local
        // drops during the unwind; balance asserted by the run fences.
        let (_, out) = run_on_both_engines_io(
            "effect 'oops(error) -> Never\n@handle 'oops { err in print(err) }\nfunc boom() 'oops -> () {\n\tlet owned = [1, 2, 3]\n\t'oops(\"bang\")\n}\nboom()",
        );
        assert_eq!(out, "bang\n");
    }

    #[test]
    fn abort_unwind_frees_intervening_frame_locals() {
        // ADR 0027 test 2 (shape 2): a frame between performer and
        // installer is suspended at an ordinary effectful call; its owned
        // local drops on the unwind.
        let (_, out) = run_on_both_engines_io(
            "effect 'oops(error) -> Never\n@handle 'oops { err in print(err) }\nfunc boom() 'oops -> () {\n\t'oops(\"deep\")\n}\nfunc middle() 'oops -> () {\n\tlet held = [4, 5]\n\tboom()\n\tprint(held.count)\n}\nmiddle()",
        );
        assert_eq!(out, "deep\n");
    }

    #[test]
    fn abort_unwind_frees_installing_frame_pre_handle_locals() {
        // ADR 0027 test 3 (shape 3): the installing frame's own locals,
        // declared BEFORE the @handle, drop when an abort exits through
        // the delimiter (raw_ret_k sits below the drop wrappers).
        let (value, out) = run_on_both_engines_io(
            "effect 'oops(error) -> Never\nfunc boom() 'oops -> () {\n\t'oops(\"bang\")\n}\nfunc run() -> Int {\n\tlet before = [7, 8]\n\t@handle 'oops { err in\n\t\tprint(err)\n\t\t0\n\t}\n\tboom()\n\tbefore.count\n}\nprint(run())",
        );
        assert_eq!(out, "bang\n0\n");
        assert_eq!(value, Value::Void);
    }

    #[test]
    fn abort_unwind_releases_heap_region_across_abort() {
        // ADR 0027 test 4: a `'heap` object live across the perform; the
        // abort releases its region (ledger rule F on the Unwind
        // candidates) and its teardown runs; the fences assert
        // live_objects == 0.
        let (_, out) = run_on_both_engines_io(
            "struct Box 'heap {\n\tlet label: Int\n}\neffect 'oops(error) -> Never\n@handle 'oops { err in print(err) }\nfunc boom() 'oops -> () {\n\tlet b = Box(label: 9)\n\t'oops(\"bang\")\n}\nboom()",
        );
        assert_eq!(out, "bang\n");
    }

    #[test]
    fn abort_unwind_runs_deinit_hooks_innermost_frame_first_reverse_decl() {
        // ADR 0027 drop order: innermost frame first (performer →
        // installer), reverse declaration order within a frame — the
        // order the drops would have run had each function returned
        // normally. The handler body runs BEFORE the unwind (its tail is
        // the abort).
        let (_, out) = run_on_both_engines_io(
            "struct Loud {\n\tlet tag: Int\n}\nextend Loud: Deinit {\n\tconsuming func deinit() -> Void {\n\t\tprint(self.tag)\n\t}\n}\neffect 'oops(e) -> Never\n@handle 'oops { e in print(e) }\nfunc boom() 'oops -> () {\n\tlet a = Loud(tag: 1)\n\tlet b = Loud(tag: 2)\n\t'oops(\"bang\")\n}\nfunc middle() 'oops -> () {\n\tlet c = Loud(tag: 3)\n\tboom()\n}\nmiddle()",
        );
        assert_eq!(out, "bang\n2\n1\n3\n");
    }

    #[test]
    fn abort_unwind_during_finalizer_completes_teardown() {
        // ADR 0027 test 5: a finalizer body performs and its handler
        // aborts. Under the Deinit-row check (open question 2) the only
        // legal shape is a handler installed INSIDE the deinit body — so
        // the abort's delimiter is the deinit witness's frame, the frames
        // above it (the performer, holding an owned array) unwind through
        // their entries while the finalizer-frame counter holds the
        // teardown pump, and the thunk's remaining field frees run when
        // the witness returns; teardown completes; balanced.
        let (_, out) = run_on_both_engines_io(
            "effect 'mid(m) -> Never\nfunc helper() -> Int {\n\tlet held = [1, 2]\n\t'mid(\"boom\")\n\theld.count\n}\nstruct Res 'heap {\n\tlet name: String\n}\nextend Res: Deinit {\n\tconsuming func deinit() -> Void {\n\t\t@handle 'mid { m in print(m) }\n\t\tlet n = helper()\n\t\tprint(n)\n\t}\n}\nfunc spawn() {\n\tlet r = Res(name: \"a\" + \"b\")\n}\nspawn()\nprint(\"done\")",
        );
        assert_eq!(out, "boom\ndone\n");
    }

    #[test]
    fn abort_unwind_resumed_then_aborted_drops_current_live_set() {
        // ADR 0027 test 8: the handler resumes once, the extent performs
        // again, the handler aborts; the live set at the SECOND suspension
        // (owned array allocated after the first resume) is what drops.
        let (value, out) = run_on_both_engines_io(
            "effect 'check(n) -> Int\n@handle 'check { n in\n\tif n > 0 {\n\t\tcontinue n\n\t}\n\tprint(\"abort\")\n\t0 - 1\n}\nfunc go() 'check -> Int {\n\tlet first = 'check(5)\n\tlet owned = [first, 2]\n\tlet second = 'check(0 - first)\n\towned.count + second\n}\ngo()",
        );
        assert_eq!(out, "abort\n");
        assert_eq!(value, Value::I64(-1));
    }

    #[test]
    fn abort_unwind_nested_handler_depths_drop_inner_extent_once() {
        // ADR 0027 test 7: inner and outer handlers over the same extent,
        // each aborted in turn; the inner extent's locals drop exactly
        // once per abort (fences catch both a leak and a double free).
        // The outer abort unwinds THROUGH the inner installing frame as
        // an ordinary intervening frame.
        let (_, out) = run_on_both_engines_io(
            "effect 'outer_stop(m) -> Never\neffect 'inner_stop(m) -> Never\nfunc work(which: Int) -> Int {\n\tlet inner_owned = [1, 2, 3]\n\tif which > 0 {\n\t\t'inner_stop(\"inner\")\n\t}\n\t'outer_stop(\"outer\")\n\tinner_owned.count\n}\nfunc scope(which: Int) -> Int {\n\t@handle 'inner_stop { m in\n\t\tprint(m)\n\t\t1\n\t}\n\twork(which)\n}\n@handle 'outer_stop { m in print(m) }\nprint(scope(1))\nprint(scope(0))",
        );
        assert_eq!(out, "inner\n1\nouter\n");
    }

    #[test]
    fn abort_unwind_out_of_recursive_performer() {
        // ADR 0027 test 9: an abort out of a recursive performer — each
        // activation holds its own owned array; every suspended
        // activation's local drops exactly once. Pins the evaluator's
        // label-identity/LIFO extent-stack discipline.
        let (value, out) = run_on_both_engines_io(
            "effect 'oops(error) -> Never\n@handle 'oops { err in\n\tprint(err)\n\t0 - 1\n}\nfunc descend(n: Int) 'oops -> Int {\n\tlet held = [n, n]\n\tif n == 0 {\n\t\t'oops(\"bottom\")\n\t}\n\tdescend(n - 1) + held.count\n}\ndescend(3)",
        );
        assert_eq!(out, "bottom\n");
        assert_eq!(value, Value::I64(-1));
    }

    #[test]
    fn abort_unwind_through_handler_body_drops_installing_locals_once() {
        // A may-suspend call INSIDE a handler body is the CAPABILITY's
        // suspension site: its unwind entry covers the body's own scopes
        // only (`scope_floor`). The installing frame's local unwinds from
        // its own suspension site (the perform that entered the handler) —
        // listing it at both sites drops it twice when the abort unwinds
        // through both frames (the run fences catch the double free).
        let (_, out) = run_on_both_engines_io(
            "effect 'stop(m) -> Never\neffect 'ask(q) -> Int\n@handle 'stop { m in\n\tprint(m)\n\t0\n}\nfunc boom() 'stop -> Int {\n\t'stop(\"bang\")\n}\nfunc scope() 'stop -> Int {\n\tlet held = [4, 5]\n\t@handle 'ask { q in\n\t\tcontinue boom()\n\t}\n\t'ask(\"q\") + held.count\n}\nscope()",
        );
        assert_eq!(out, "bang\n");
    }

    // ----- Pattern-binding statements: if-let and let-else ----------------

    #[test]
    fn vm_matches_evaluator_on_if_let() {
        let (_, out) = run_on_both_engines_io(
            "let x: Optional<Int> = Optional.some(41)\nif let .some(v) = x {\n\tprint(v + 1)\n}\nlet y: Optional<Int> = Optional.none\nif let .some(v) = y {\n\tprint(v)\n}",
        );
        assert_eq!(out, "42\n");
    }

    #[test]
    fn vm_matches_evaluator_on_let_else() {
        // The success path binds x; the failure path diverges through the
        // else (returning the default).
        let (_, out) = run_on_both_engines_io(
            "func unwrap_or_zero(val: Optional<Int>) -> Int {\n\tlet .some(x) = val else { return 0 }\n\tx\n}\nprint(unwrap_or_zero(Optional.some(41)))\nprint(unwrap_or_zero(Optional.none))",
        );
        assert_eq!(out, "41\n0\n");
    }

    #[test]
    fn vm_matches_evaluator_on_or_pattern_in_a_let() {
        // The parser desugars an or-pattern let to a single-arm match;
        // both alternatives bind the same name.
        let (_, out) = run_on_both_engines_io(
            "enum E {\n\tcase a(Int)\n\tcase b(Int)\n}\nfunc pick(e: E) -> Int {\n\tlet .a(v) | .b(v) = e\n\tv\n}\nprint(pick(E.a(1)))\nprint(pick(E.b(2)))",
        );
        assert_eq!(out, "1\n2\n");
    }

    // ----- Entrypoints: an explicit `func main` runs as the program;
    // otherwise the top-level statements are the program ------------------

    #[test]
    fn vm_matches_evaluator_on_explicit_main_entrypoint() {
        let (_, out) = run_on_both_engines_io("func main() {\n\tprint(\"hi from main\")\n}");
        assert_eq!(out, "hi from main\n");
    }

    #[test]
    fn vm_matches_evaluator_on_main_with_top_level_bindings() {
        // Top-level lets initialize before main runs; main's value is the
        // program's value.
        let (value, _) =
            run_on_both_engines_io("let base = 40\nfunc main() -> Int {\n\tbase + 2\n}");
        assert_eq!(value, Value::I64(42));
    }

    #[test]
    fn vm_matches_evaluator_on_main_after_top_level_statements() {
        // Top-level statements still run, in source order, before main.
        let (value, out) = run_on_both_engines_io(
            "print(\"setup\")\nfunc main() -> Int {\n\tprint(\"main\")\n\t7\n}",
        );
        assert_eq!(out, "setup\nmain\n");
        assert_eq!(value, Value::I64(7));
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
    fn vm_matches_evaluator_on_effectful_closure_stored_in_a_struct_field() {
        // Effect params on structs, end to end: the stored closure's row
        // rides the instance's type (typing side) while its capability
        // rides the closure environment (runtime side) — calling the
        // field under the handler performs and resumes.
        let (value, out) = run_on_both_engines_io(
            "effect 'ask(prompt) -> Int\nstruct Wrapper {\n\tlet f: () -> Int\n}\n@handle 'ask { p in\n\tprint(p)\n\tcontinue 42\n}\nfunc go() 'ask -> Int {\n\tlet w = Wrapper(f: func() {\n\t\t'ask(\"meaning?\") + 1\n\t})\n\tw.f()\n}\ngo()",
        );
        assert_eq!(out, "meaning?\n");
        assert_eq!(value, Value::I64(43));
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
    fn handler_body_isolates_the_whole_statement_scope_bundle() {
        // ADR 0017 stage 4 characterization, the handler-body twin: a
        // handler body containing a loop with break/continue, a droppable
        // local, and an early exit (the `continue v` resume). (`@handle`
        // only lowers at a function body's root today, so no enclosing
        // loop/pending-temp statement can surround this site.) The body's
        // loop targets, pending-temp frames, and early-exit scopes must
        // stay isolated from the enclosing function's values.
        let (_, out) = run_on_both_engines_io(
            "effect 'check(n) -> Int\nfunc go() 'check -> Int {\n\tlet first = 'check(1)\n\tlet second = 'check(2)\n\tfirst + second\n}\nfunc main() -> Int {\n\t@handle 'check { n in\n\t\tlet held = \"h\" + \"!\"\n\t\tlet j = 0\n\t\tloop j < 3 {\n\t\t\tj = j + 1\n\t\t\tif j == 1 {\n\t\t\t\tcontinue\n\t\t\t}\n\t\t\tbreak\n\t\t}\n\t\tprint(held)\n\t\tcontinue n + j\n\t}\n\tprint(go())\n\t0\n}",
        );
        assert_eq!(out, "h!\nh!\n7\n");
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
    fn vm_matches_evaluator_on_resumable_perform_in_expression_position() {
        // The performs sit inside a larger expression and an if condition
        // — positions the old statement-spine splitter could not reach.
        // In CPS every expression has a continuation, so the resumption
        // is just the perform's own.
        let (value, out) = run_on_both_engines_io(
            "effect 'ask(prompt) -> Int\n@handle 'ask { p in\n\tcontinue 21\n}\nfunc go() 'ask -> Int {\n\tif 'ask(\"q\") > 10 {\n\t\t'ask(\"a\") + 'ask(\"b\")\n\t} else {\n\t\t0\n\t}\n}\nlet r = go()\nprint(r)\nr",
        );
        assert_eq!(out, "42\n");
        assert_eq!(value, Value::I64(42));
    }

    #[test]
    fn vm_matches_evaluator_on_closure_capability_capture_is_lexical() {
        // A function value captures the capabilities of its CREATION
        // site, not its call site (Effekt-style lexical capture — ADR
        // 0011's documented departure (d)): `f` keeps routing to the
        // first handler even though a second one covers the call.
        let (value, _) = run_on_both_engines_io(
            "effect 'boost() -> Int\nfunc run() -> Int {\n\t@handle 'boost { continue 100 }\n\tlet f = func() -> Int { 'boost() }\n\t@handle 'boost { continue 200 }\n\tf() + 'boost()\n}\nrun()",
        );
        assert_eq!(value, Value::I64(300));
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
    fn vm_resuming_handler_preserves_enclosing_locals() {
        // The handler's `continue` must drop only handler-scope bindings:
        // `s` belongs to `f`, stays live across the resume, and is dropped
        // exactly once at f's exit.
        let (_, out) = run_on_both_engines_io(
            "effect 'ask(prompt) -> Int\nfunc f() -> Int {\n\tlet s = \"hello\" + \" world\"\n\t@handle 'ask { p in\n\t\tcontinue 41\n\t}\n\tlet answer = 'ask(\"q\")\n\tanswer + s.byte_count\n}\nprint(f())",
        );
        assert_eq!(out, "52\n");
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
            "let path = _alloc<Byte>(1)\nlet fd = _io_open(path, 65, 384)\n_free(path)\nlet hello = \"hello io\"\n_io_write(fd, hello.storage.base, hello.byte_count)\nlet buf = _alloc<Byte>(16)\nlet n = _io_read(fd, buf, 16)\n_io_write(STDOUT_FD, buf, n)\nlet r = _io_close(fd)\n_free(buf)\nr",
        );
        assert_eq!(out, "hello io");
        assert_eq!(value, Value::I64(0));
    }

    #[test]
    fn vm_matches_evaluator_on_open_path() {
        // open_path takes a Talk String (copied with a NUL terminator
        // into fresh memory); the simulated fd then round-trips bytes.
        let (value, out) = run_on_both_engines_io(
            "let fd = open_path(\"scratch.txt\", 65, 384)\nlet data = \"file data\"\n_io_write(fd, data.storage.base, data.byte_count)\nlet buf = _alloc<Byte>(16)\nlet n = _io_read(fd, buf, 16)\n_io_write(STDOUT_FD, buf, n)\nlet r = _io_close(fd)\n_free(buf)\nr",
        );
        assert_eq!(out, "file data");
        assert_eq!(value, Value::I64(0));
    }

    #[test]
    fn vm_matches_evaluator_on_socket_loopback() {
        // CaptureIO sockets are buffers: what a test writes to a
        // connection it can read back — the scripted-client loop.
        let (_, out) = run_on_both_engines_io(
            "let sock = _io_socket(AF_INET, SOCK_STREAM, 0)\n_io_connect(sock, LOCALHOST, 9900)\nlet msg = \"ping\"\n_io_write(sock, msg.storage.base, msg.byte_count)\nlet buf = _alloc<Byte>(8)\nlet n = _io_read(sock, buf, 8)\nlet w = _io_write(STDOUT_FD, buf, n)\n_free(buf)\nw",
        );
        assert_eq!(out, "ping");
    }

    #[test]
    fn vm_matches_evaluator_on_server_accept_script() {
        // The ChatServer slice: bind/listen succeed, accept mints a
        // client fd, and the greeting written to it reads back.
        let (value, out) = run_on_both_engines_io(
            "let server = _io_socket(AF_INET, SOCK_STREAM, 0)\nlet b = _io_bind(server, INADDR_ANY, 9900)\nlet l = _io_listen(server, 128)\nlet client = _io_accept(server)\nlet hi = \"hi client\"\n_io_write(client, hi.storage.base, hi.byte_count)\nlet buf = _alloc<Byte>(16)\nlet n = _io_read(client, buf, 16)\n_io_write(STDOUT_FD, buf, n)\n_free(buf)\nb + l",
        );
        assert_eq!(out, "hi client");
        assert_eq!(value, Value::I64(0));
    }

    #[test]
    fn vm_matches_evaluator_on_io_error_returns() {
        // POSIX conventions: a bad fd reads as -EBADF, and ctl is
        // -EINVAL under the captured io (tests never ioctl for real).
        let (value, _) = run_on_both_engines_io(
            "let buf = _alloc<Byte>(4)\nlet bad = _io_read(99, buf, 4)\nlet ctl = _io_ctl(1, 0, 0)\n_free(buf)\nbad * 100 + ctl",
        );
        assert_eq!(value, Value::I64(-9 * 100 + -22));
    }

    #[test]
    fn vm_matches_evaluator_on_empty_poll() {
        // Zero descriptors: poll reports zero ready (the marshaling
        // boundary, without hand-building pollfd records in Talk).
        let (value, _) = run_on_both_engines_io(
            "let fds = _alloc<Byte>(8)\nlet r = _io_poll(fds, 0, 0)\n_free(fds)\nr",
        );
        assert_eq!(value, Value::I64(0));
    }

    // ----- Ports from the previous backend's interpreter suite (each old
    // test's behavior pinned here or noted in docs/parity-test-audit.md) --

    #[test]
    fn vm_matches_evaluator_on_empty_program() {
        let (value, out) = run_on_both_engines_io("");
        assert_eq!(value, Value::Void);
        assert_eq!(out, "");
    }

    #[test]
    fn vm_matches_evaluator_on_comparisons_and_logic() {
        let (value, _) = run_on_both_engines_io(
            "let a = 1 < 2\nlet b = 2 <= 2\nlet c = 2 > 1\nlet d = 1 >= 2\nlet e = !false\nlet f = true && false\nlet g = false || true\na && b && c && e && g && !d && !f",
        );
        assert_eq!(value, Value::Bool(true));
    }

    #[test]
    fn vm_matches_evaluator_on_record_literal_members() {
        let (value, _) = run_on_both_engines_io("let r = { fizz: 123, buzz: 1.23 }\nr.fizz");
        assert_eq!(value, Value::I64(123));
        let (value, _) = run_on_both_engines_io("let r = { fizz: 123, buzz: 1.23 }\nr.buzz");
        assert_eq!(value, Value::F64(1.23));
    }

    #[test]
    fn record_literal_fields_evaluate_in_source_order() {
        // Labels are given out of row (label-sorted) order: the effectful
        // field values must still run in source order.
        let (value, out) = run_on_both_engines_io(
            "func first() -> Int {\n\tprint(\"first\")\n\t1\n}\nfunc second() -> Int {\n\tprint(\"second\")\n\t2\n}\nlet r = { b: first(), a: second() }\nprint(r.b)\nr.a",
        );
        assert_eq!(out, "first\nsecond\n1\n");
        assert_eq!(value, Value::I64(2));
    }

    #[test]
    fn vm_matches_evaluator_on_record_field_assignment() {
        let (value, _) = run_on_both_engines_io("let a = { b: 1 }\na.b = 2\na.b");
        assert_eq!(value, Value::I64(2));
    }

    #[test]
    fn vm_matches_evaluator_on_nested_record_field_assignment() {
        // a.b.c = 2 rebuilds b with c replaced, then a with b replaced
        // (value semantics, one store).
        let (value, _) = run_on_both_engines_io("let a = { b: { c: 1 } }\na.b.c = 2\na.b.c");
        assert_eq!(value, Value::I64(2));
    }

    #[test]
    fn vm_matches_evaluator_on_generic_struct_field() {
        let (value, _) =
            run_on_both_engines_io("struct Fizz<T> {\n\tlet buzz: T\n}\nFizz(buzz: 123).buzz");
        assert_eq!(value, Value::I64(123));
        let (value, _) =
            run_on_both_engines_io("struct Fizz<T> {\n\tlet buzz: T\n}\nFizz(buzz: 1.23).buzz");
        assert_eq!(value, Value::F64(1.23));
    }

    #[test]
    fn vm_matches_evaluator_on_literal_match() {
        let (value, _) = run_on_both_engines_io(
            "match 789 {\n\t123 -> 1,\n\t456 -> 2,\n\t789 -> 3,\n\t_ -> 0\n}",
        );
        assert_eq!(value, Value::I64(3));
    }

    #[test]
    fn vm_matches_evaluator_on_nested_closure_returned_as_value() {
        let (value, _) = run_on_both_engines_io(
            "let a = 123\nfunc b() {\n\tfunc c() {\n\t\ta\n\t}\n\tc\n}\nlet inner = b()\ninner()",
        );
        assert_eq!(value, Value::I64(123));
    }

    #[test]
    fn vm_matches_evaluator_on_independent_counters() {
        // Two counters from one factory keep separate cells.
        let (value, _) = run_on_both_engines_io(
            "func makeCounter() {\n\tlet a = 0\n\treturn func() {\n\t\ta = a + 1\n\t\ta\n\t}\n}\nlet a = makeCounter()\nlet b = makeCounter()\na()\na()\n(a(), b())",
        );
        assert_eq!(
            value,
            Value::Tuple(std::rc::Rc::new(vec![Value::I64(3), Value::I64(1)]))
        );
    }

    #[test]
    fn vm_matches_evaluator_on_top_level_mut_closure() {
        // The closure mutates the top-level binding; the change is
        // visible after the call.
        let (value, _) =
            run_on_both_engines_io("let a = 123\nfunc b() {\n\ta = a + 1\n\ta\n}\nb()\na");
        assert_eq!(value, Value::I64(124));
    }

    #[test]
    fn vm_matches_evaluator_on_early_return_skipping_side_effects() {
        let (value, out) = run_on_both_engines_io(
            "func foo() -> Int {\n\treturn 1\n\tprint(\"after\")\n\t2\n}\nfoo()",
        );
        assert_eq!(value, Value::I64(1));
        assert_eq!(out, "");
    }

    #[test]
    fn vm_matches_evaluator_on_core_function_as_value() {
        let (_, out) = run_on_both_engines_io("let f = print_raw\nf(\"hi\")");
        assert_eq!(out, "hi");
    }

    #[test]
    fn vm_matches_evaluator_on_unqualified_variant_argument() {
        let (value, _) = run_on_both_engines_io(
            "enum AB {\n\tcase a(Int)\n\tcase b(Int)\n}\nfunc callMe(param: AB) -> Int {\n\tmatch param {\n\t\t.a(x) -> x,\n\t\t.b(x) -> x\n\t}\n}\ncallMe(.a(123))",
        );
        assert_eq!(value, Value::I64(123));
    }

    #[test]
    fn vm_matches_evaluator_on_or_pattern_falling_through_arms() {
        let (value, _) = run_on_both_engines_io(
            "enum ABC {\n\tcase a\n\tcase b\n\tcase c\n}\nfunc toInt(x: ABC) -> Int {\n\tmatch x {\n\t\t.a | .b -> 1,\n\t\t.c -> 2\n\t}\n}\ntoInt(.c)",
        );
        assert_eq!(value, Value::I64(2));
    }

    #[test]
    fn vm_matches_evaluator_on_protocol_defaults_with_associated_types() {
        // A protocol default body dispatching through an associated
        // type's own protocol bound (the old pet-food example).
        let (_, out) = run_on_both_engines_io(
            "struct CatFood {}\nstruct DogFood {}\nprotocol Named {\n\tfunc name() -> String\n}\nextend CatFood: Named {\n\tfunc name() { \"tasty cat food\" }\n}\nextend DogFood: Named {\n\tfunc name() { \"tasty dog food\" }\n}\nprotocol Pet {\n\tassociated Food: Named\n\tfunc favoriteFood() -> Food\n\tfunc handleDSTChange() {\n\t\tprint(\"what the heck where is my \" + self.favoriteFood().name())\n\t}\n}\nstruct Cat {}\nextend Cat: Pet {\n\tfunc favoriteFood() {\n\t\tCatFood()\n\t}\n}\nstruct Dog {}\nextend Dog: Pet {\n\tfunc favoriteFood() {\n\t\tDogFood()\n\t}\n}\nCat().handleDSTChange()\nDog().handleDSTChange()",
        );
        assert_eq!(
            out,
            "what the heck where is my tasty cat food\nwhat the heck where is my tasty dog food\n"
        );
    }

    #[test]
    fn vm_matches_evaluator_on_protocol_extension_defaults() {
        // `extend Greeter` methods are defaulted requirements: Cat takes
        // the extension body, Dog's own witness overrides it.
        let (_, out) = run_on_both_engines_io(
            "protocol Greeter {\n\tfunc volume() -> Int\n}\nextend Greeter {\n\tfunc greet() -> Int {\n\t\tself.volume()\n\t}\n}\nstruct Cat {}\nextend Cat: Greeter {\n\tfunc volume() -> Int { 3 }\n}\nstruct Dog {}\nextend Dog: Greeter {\n\tfunc volume() -> Int { 7 }\n\tfunc greet() -> Int { 11 }\n}\nprint(Cat().greet())\nprint(Dog().greet())",
        );
        assert_eq!(out, "3\n11\n");
    }

    #[test]
    fn vm_matches_evaluator_on_return_only_loop_tail() {
        // An unconditional loop that only exits via `return`: the loop's
        // MIR exit block is unreachable, so the function tail after it
        // must not deliver () to the return continuation.
        let (_, out) = run_on_both_engines_io(
            "func firstOver(limit: Int) -> Int {\n\tlet i = 0\n\tloop {\n\t\tif i > limit { return i }\n\t\ti = i + 1\n\t}\n}\nprint(firstOver(3))",
        );
        assert_eq!(out, "4\n");
    }

    #[test]
    fn vm_matches_evaluator_on_iterator_index_with_borrowed_elements() {
        // Array iterators yield &Element; `index` compares them against a
        // by-value needle through borrow-transparent conformance plus the
        // Copy / copy-out-of-borrow coercions. The chained receiver is an
        // rvalue (its iterator state dies with the call).
        let (_, out) = run_on_both_engines_io(
            "let xs = [10, 20, 30]\nmatch xs.iter().index(20) {\n\t.some(i) -> print(i),\n\t.none -> print(\"not found\")\n}\nmatch xs.iter().index(99) {\n\t.some(i) -> print(i),\n\t.none -> print(\"not found\")\n}",
        );
        assert_eq!(out, "1\nnot found\n");
    }

    #[test]
    fn vm_matches_evaluator_on_generic_inherent_extend_member_with_closures() {
        // An inherent extend member with a method-level generic and a
        // closure param, used at two different instantiations: dispatch
        // must freshen the generic and the closure's row per use (the
        // same class as `map`, latent in extend_members).
        let (_, out) = run_on_both_engines_io(
            "struct Box2 {\n\tlet v: Int\n}\nextend Box2 {\n\tfunc apply<U>(fn: (Int) -> U) -> U {\n\t\tfn(self.v)\n\t}\n}\nlet b = Box2(v: 3)\nlet x = b.apply() { n in n + 1 }\nlet s = b.apply() { n in \"got \" + n.show() }\nprint(x)\nprint(s)",
        );
        assert_eq!(out, "4\ngot 3\n");
    }

    #[test]
    fn vm_matches_evaluator_on_generic_requirement_with_trailing_closure() {
        // `map<U>` is a generic requirement: its U instantiation must
        // reach the lowerer's θ so the trailing closure's param type is
        // concrete, not erased.
        let (_, out) = run_on_both_engines_io(
            "let xs = [10, 20, 30]\nlet m = xs.iter().map() { x in x }\nprint(\"ok\")",
        );
        assert_eq!(out, "ok\n");
    }

    #[test]
    fn vm_matches_evaluator_on_index_with_borrowed_struct_witness() {
        // ADR 0014: a plain struct's borrow-shaped equals witness compares
        // borrowed elements without copy-out coercions.
        let (_, out) = run_on_both_engines_io(
            "struct Pt {\n\tlet x: Int\n}\nextend Pt: Equatable<Pt> {\n\tfunc equals(rhs: &Pt) -> Bool {\n\t\tself.x == rhs.x\n\t}\n}\nlet xs = [Pt(x: 1), Pt(x: 2), Pt(x: 3)]\nmatch xs.iter().index(Pt(x: 2)) {\n\t.some(i) -> print(i),\n\t.none -> print(\"not found\")\n}",
        );
        assert_eq!(out, "1\n");
    }

    #[test]
    fn vm_matches_evaluator_on_mut_method_on_rvalue_receiver() {
        // A mutating call on an rvalue receiver: the updated Self has no
        // home and dies with the call; the result still comes through.
        let (_, out) = run_on_both_engines_io(
            "struct Counter {\n\tlet n: Int\n\n\tmut func bump() -> Int {\n\t\tself.n = self.n + 1\n\t\tself.n\n\t}\n}\nfunc make() -> Counter { Counter(n: 41) }\nprint(make().bump())",
        );
        assert_eq!(out, "42\n");
    }

    #[test]
    fn vm_matches_evaluator_on_tail_block_alias_drops_once() {
        // A tail-position block is REAL MIR (its moves are CFG facts):
        // aliasing a droppable into it must not double-free — the outer
        // binding is dead after the move, the inner drops once.
        let (_, out) = run_on_both_engines_io(
            "func f() -> Int {\n\tlet a = [1, 2, 3]\n\t{\n\t\tlet b = a\n\t\tb.count\n\t}\n}\nprint(f())",
        );
        assert_eq!(out, "3\n");
    }

    #[test]
    fn vm_matches_evaluator_on_array_element_teardown() {
        // Containers deep-drop their elements: the LAST buffer reference
        // tears them down (CoW-gated via _is_unique in Array's deinit).
        // Runtime-built strings in a dropped array must not leak — this
        // runs under the strict leak assertion.
        let (_, out) = run_on_both_engines_io(
            "let xs = [\"hello \" + \"world\", \"foo \" + \"bar\"]\nprint(xs.count)",
        );
        assert_eq!(out, "2\n");
    }

    #[test]
    fn vm_matches_evaluator_on_nested_array_element_teardown() {
        // Nested containers compose: the inner array's deinit runs for
        // element drops too (the recursion guard is θ-aware, not
        // symbol-level).
        let (_, out) =
            run_on_both_engines_io("let xs = [[\"a\" + \"b\"], [\"c\" + \"d\"]]\nprint(xs.count)");
        assert_eq!(out, "2\n");
    }

    #[test]
    fn vm_cloned_array_push_retains_shared_elements() {
        // CoW: push after clone() copies the shared buffer. The copy must
        // retain each element — otherwise two "unique" buffers hold the
        // same element pointers and both deep-drop them (double free).
        let (_, out) = run_on_both_engines_io(
            "func main() -> Int {\n\tlet xs = [\"a\" + \"b\"]\n\tlet snap = xs.clone()\n\txs.push(\"c\" + \"d\")\n\tprint(snap.get(0))\n\tprint(xs.get(0))\n\tprint(xs.get(1))\n\t0\n}",
        );
        assert_eq!(out, "ab\nab\ncd\n");
    }

    #[test]
    fn vm_cloned_array_set_retains_shared_elements() {
        // Same CoW copy, reached through set's uniqued_storage: the sharer
        // keeps its element, the writer drops its (retained) copy.
        let (_, out) = run_on_both_engines_io(
            "func main() -> Int {\n\tlet xs = [\"a\" + \"b\"]\n\tlet snap = xs.clone()\n\txs.set(0, \"z\" + \"w\")\n\tprint(snap.get(0))\n\tprint(xs.get(0))\n\t0\n}",
        );
        assert_eq!(out, "ab\nzw\n");
    }

    #[test]
    fn vm_array_grow_moves_droppable_elements() {
        // Growing past capacity from a unique buffer is a MOVE: elements
        // are donated to the fresh buffer (no retains) and the old shell
        // is freed without deep-dropping them — no leak, no double free.
        let (_, out) = run_on_both_engines_io(
            "func main() -> Int {\n\tlet xs = [\"a\" + \"b\"]\n\txs.push(\"c\" + \"d\")\n\txs.push(\"e\" + \"f\")\n\txs.push(\"g\" + \"h\")\n\tprint(xs.get(0))\n\tprint(xs.get(3))\n\tprint(xs.count)\n\t0\n}",
        );
        assert_eq!(out, "ab\ngh\n4\n");
    }

    #[test]
    fn vm_cloned_nested_array_push_retains_shared_elements() {
        // Nested containers: retaining an Array element is an rc bump on
        // its buffer; the deinit uniqueness gate then tears elements down
        // exactly once across the sharers.
        let (_, out) = run_on_both_engines_io(
            "func main() -> Int {\n\tlet xs = [[\"a\" + \"b\"]]\n\tlet snap = xs.clone()\n\txs.push([\"c\" + \"d\"])\n\tprint(snap.get(0).get(0))\n\tprint(xs.get(1).get(0))\n\tprint(xs.count)\n\t0\n}",
        );
        assert_eq!(out, "ab\ncd\n2\n");
    }

    #[test]
    fn vm_cloned_array_push_retains_enum_elements() {
        // Enum elements retain under tag dispatch — the branching walk
        // that makes the retain splice continuation-shaped.
        let (_, out) = run_on_both_engines_io(
            "func main() -> Int {\n\tlet xs = [Optional.some(\"a\" + \"b\")]\n\tlet snap = xs.clone()\n\txs.push(Optional.some(\"c\" + \"d\"))\n\tmatch snap.get(0) {\n\t\t.some(s) -> print(s),\n\t\t.none -> print(\"none\")\n\t}\n\tprint(xs.count)\n\t0\n}",
        );
        assert_eq!(out, "ab\n2\n");
    }

    #[test]
    fn vm_cloned_nested_array_set_retains_shared_elements() {
        let (_, out) = run_on_both_engines_io(
            "func main() -> Int {\n\tlet xs = [[\"a\" + \"b\"]]\n\tlet snap = xs.clone()\n\txs.set(0, [\"z\" + \"w\"])\n\tprint(snap.get(0).get(0))\n\tprint(xs.get(0).get(0))\n\t0\n}",
        );
        assert_eq!(out, "ab\nzw\n");
    }

    #[test]
    fn vm_array_set_drops_overwritten_element() {
        // set on an owned array must drop the element it overwrites (the
        // scalar-result leak fence asserts exact balance).
        let (_, out) = run_on_both_engines_io(
            "func main() -> Int {\n\tlet xs = [\"a\" + \"b\"]\n\txs.set(0, \"z\" + \"w\")\n\tprint(xs.get(0))\n\t0\n}",
        );
        assert_eq!(out, "zw\n");
    }

    #[test]
    fn vm_array_set_drops_overwritten_nested_element() {
        // The overwritten element's drop is a full deep drop: a nested
        // array element tears down its own strings.
        let (_, out) = run_on_both_engines_io(
            "func main() -> Int {\n\tlet xs = [[\"a\" + \"b\"]]\n\txs.set(0, [\"z\" + \"w\"])\n\tprint(xs.get(0).get(0))\n\t0\n}",
        );
        assert_eq!(out, "zw\n");
    }

    #[test]
    fn vm_sort_by_compares_the_last_element() {
        // Selection sort's inner scan must include the final index: with
        // [1, 3, 2] descending, the last element (2) has to move.
        let value =
            run_on_both_engines("let sorted = [1, 3, 2].sort_by { $0 > $1 }\nsorted == [3, 2, 1]");
        assert_eq!(value, Value::Bool(true));
    }

    #[test]
    fn vm_matches_evaluator_on_mut_inherent_extend_member() {
        // The inout convention is DERIVED from the member's scheme (first
        // param an exclusive borrow), not registered per declaration kind
        // — an inherent extend member must get it like any method.
        let (_, out) = run_on_both_engines_io(
            "struct Counter3 {\n\tlet n: Int\n}\nextend Counter3 {\n\tmut func bump2() -> Int {\n\t\tself.n = self.n + 1\n\t\tself.n\n\t}\n}\nlet c = Counter3(n: 0)\nc.bump2()\nprint(c.bump2())",
        );
        assert_eq!(out, "2\n");
    }

    #[test]
    fn vm_matches_evaluator_on_mut_protocol_defaults() {
        // A mut default body calls a mut requirement through self: both
        // the nested call and the default's own return use the inout
        // convention (requirement symbols must be in the mutating set).
        let (_, out) = run_on_both_engines_io(
            "protocol Bumper {\n\tmut func bump() -> Int\n\n\tmut func twice() -> Int {\n\t\tself.bump()\n\t\tself.bump()\n\t}\n}\nstruct Counter2 {\n\tlet n: Int\n}\nextend Counter2: Bumper {\n\tmut func bump() -> Int {\n\t\tself.n = self.n + 1\n\t\tself.n\n\t}\n}\nlet c = Counter2(n: 0)\nprint(c.twice())",
        );
        assert_eq!(out, "2\n");
    }

    #[test]
    fn vm_matches_evaluator_on_mut_protocol_extension_defaults() {
        let (_, out) = run_on_both_engines_io(
            "protocol Bumper {\n\tmut func bump() -> Int\n}\nextend Bumper {\n\tmut func twice() -> Int {\n\t\tself.bump()\n\t\tself.bump()\n\t}\n}\nstruct Counter2 {\n\tlet n: Int\n}\nextend Counter2: Bumper {\n\tmut func bump() -> Int {\n\t\tself.n = self.n + 1\n\t\tself.n\n\t}\n}\nlet c = Counter2(n: 0)\nprint(c.twice())",
        );
        assert_eq!(out, "2\n");
    }

    #[test]
    fn vm_matches_evaluator_on_handlers_in_two_functions() {
        // Each function's @handle mints its own capability for the same
        // effect.
        let (_, out) = run_on_both_engines_io(
            "effect 'fizz() -> Int\nfunc a() -> Int {\n\t@handle 'fizz {\n\t\tcontinue 1\n\t}\n\t'fizz()\n}\nfunc b() -> Int {\n\t@handle 'fizz {\n\t\tcontinue 2\n\t}\n\t'fizz()\n}\nprint_raw(a().show())\nprint_raw(b().show())",
        );
        assert_eq!(out, "12");
    }

    #[test]
    fn vm_matches_evaluator_on_nested_extend_with_generics() {
        // The old test used a generic protocol (`Getter<T>`); the new
        // type system expresses this with an associated type.
        let (_, out) = run_on_both_engines_io(
            "protocol Getter {\n\tassociated T\n\tconsuming func get() -> T\n}\nstruct Container<Element> {\n\tlet item: Element\n\n\textend Self: Getter {\n\t\tconsuming func get() -> Element {\n\t\t\tself.item\n\t\t}\n\t}\n}\nlet c = Container<Int>(item: 42)\nprint(c.get())",
        );
        assert_eq!(out, "42\n");
    }

    #[test]
    fn vm_matches_evaluator_on_nested_extend_with_self_access() {
        let (_, out) = run_on_both_engines_io(
            "protocol Doubler {\n\tfunc doubled() -> Int\n}\nstruct Wrapper {\n\tlet value: Int\n\n\textend Self: Doubler {\n\t\tfunc doubled() -> Int {\n\t\t\tself.value + self.value\n\t\t}\n\t}\n}\nlet w = Wrapper(value: 21)\nprint(w.doubled())",
        );
        assert_eq!(out, "42\n");
    }

    #[test]
    fn vm_matches_evaluator_on_string_operations() {
        let (value, _) = run_on_both_engines_io("\"hello\" == \"hello\"");
        assert_eq!(value, Value::Bool(true));
        let (value, _) = run_on_both_engines_io("\"hello\" == \"world\"");
        assert_eq!(value, Value::Bool(false));
        let (_, out) = run_on_both_engines_io("print(\"hello\".utf8().slice(1, 3).to_string())");
        assert_eq!(out, "ell\n");
        let (_, out) = run_on_both_engines_io(
            "print(\"hello\".as_substring().utf8().slice(1, 3).to_string())",
        );
        assert_eq!(out, "ell\n");
        let (_, out) = run_on_both_engines_io(
            "match \"hello world\".find(\"world\") {\n\t.some(i) -> print(i),\n\t.none -> print(0 - 1)\n}",
        );
        assert_eq!(out, "6\n");
        let (_, out) = run_on_both_engines_io(
            "match \"hello world\".find(\"missing\") {\n\t.some(i) -> print(i),\n\t.none -> print(0 - 1)\n}",
        );
        assert_eq!(out, "-1\n");
        let (_, out) = run_on_both_engines_io(
            "match \"banana\".find_from(\"na\", 3) {\n\t.some(i) -> print(i),\n\t.none -> print(0 - 1)\n}",
        );
        assert_eq!(out, "4\n");
    }

    #[test]
    fn vm_matches_evaluator_on_pure_method_calls_not_clobbering_receivers() {
        let (_, out) = run_on_both_engines_io(
            "let raw = \"GET / HTTP/1.1\\r\\nHost: localhost\\r\\n\\r\\n\"\nmatch raw.find(\" \") {\n\t.some(idx) -> {\n\t\tprint(raw.byte_count)\n\t\tprint(idx)\n\t\tprint(raw.byte_count - (idx + 1))\n\t},\n\t.none -> print(0 - 1)\n}",
        );
        assert_eq!(out, "35\n3\n31\n");
    }

    #[test]
    fn vm_matches_evaluator_on_show_for_scalars() {
        let (_, out) = run_on_both_engines_io(
            "print_raw(42.show())\nprint_raw(0.show())\nprint_raw((0 - 42).show())\nprint_raw(true.show())\nprint_raw(false.show())\nprint_raw(\"hello\".show())",
        );
        assert_eq!(out, "420-42truefalsehello");
    }

    #[test]
    fn vm_matches_evaluator_on_show_for_empty_and_payloadless() {
        let (_, out) = run_on_both_engines_io(
            "struct Empty {}\nenum Color {\n\tcase red\n\tcase blue\n}\nprint_raw(Empty().show())\nprint_raw(Color.red.show())",
        );
        assert_eq!(out, "Empty {}Color.red");
    }

    #[test]
    fn vm_matches_evaluator_on_show_with_multiple_payloads() {
        let (_, out) = run_on_both_engines_io(
            "enum Shape {\n\tcase rect(Int, Int)\n}\nprint_raw(Shape.rect(3, 4).show())",
        );
        assert_eq!(out, "Shape.rect(3, 4)");
    }

    #[test]
    fn vm_matches_evaluator_on_show_override() {
        let (_, out) = run_on_both_engines_io(
            "struct Foo {\n\tlet x: Int\n}\nextend Foo: Showable {\n\tfunc show() -> String { \"custom\" }\n}\nprint_raw(Foo(x: 1).show())",
        );
        assert_eq!(out, "custom");
    }

    #[test]
    fn vm_matches_evaluator_on_show_through_a_generic_bound() {
        let (_, out) = run_on_both_engines_io(
            "func show_it<T: Showable>(x: T) -> String { x.show() }\nstruct Pair {\n\tlet a: Int\n\tlet b: Int\n}\nprint_raw(show_it(Pair(a: 1, b: 2)))",
        );
        assert_eq!(out, "Pair(a: 1, b: 2)");
    }

    #[test]
    fn vm_matches_evaluator_on_generic_struct_show_erases_arguments() {
        let (_, out) = run_on_both_engines_io(
            "struct Wrapper<T> {\n\tlet value: Int\n}\nprint_raw(Wrapper<String>(value: 42).show())",
        );
        assert_eq!(out, "Wrapper(value: 42)");
    }

    #[test]
    fn vm_matches_evaluator_on_unshowable_fields_stay_lazy() {
        // A struct with a function-typed field is fine until something
        // demands show.
        let (value, _) = run_on_both_engines_io(
            "struct Wrapper {\n\tlet f: () -> Int\n}\nlet w = Wrapper(f: func() -> Int { 42 })\nw.f()",
        );
        assert_eq!(value, Value::I64(42));
    }

    #[test]
    fn vm_matches_evaluator_on_trunc_and_itof_splices() {
        let (value, _) = run_on_both_engines_io(
            "func trunc(f: Float) -> Int {\n\t@_ir(f) { %? = trunc $0 }\n}\ntrunc(3.7)",
        );
        assert_eq!(value, Value::I64(3));
        let (value, _) = run_on_both_engines_io(
            "func itof(i: Int) -> Float {\n\t@_ir(i) { %? = itof $0 }\n}\nitof(42)",
        );
        assert_eq!(value, Value::F64(42.0));
    }

    #[test]
    fn vm_matches_evaluator_on_btoi_splice() {
        let (value, _) = run_on_both_engines_io(
            "func first_byte(s: String) -> Int {\n\tlet b: Byte = s.utf8().at(0)\n\t@_ir(b) { %? = btoi $0 }\n}\nfirst_byte(\"A\")",
        );
        assert_eq!(value, Value::I64(65));
        // The core wrapper: Byte._toInt(), including a multi-byte lead byte.
        let (value, _) = run_on_both_engines_io("\"é\".utf8().at(0)._toInt()");
        assert_eq!(value, Value::I64(0xC3));
    }

    #[test]
    fn vm_matches_evaluator_on_utf8_view() {
        // Byte-level access lives behind the explicit utf8() view.
        let (value, _) = run_on_both_engines_io("\"café\".utf8().count()");
        assert_eq!(value, Value::I64(5));
        let (value, _) = run_on_both_engines_io("\"café\".utf8().at(4)._toInt()");
        assert_eq!(value, Value::I64(0xA9));
        let (value, _) = run_on_both_engines_io(
            "let s = \"hello world\"\nlet sub: Substring = s.utf8().slice(6, 5)\nsub.byte_count",
        );
        assert_eq!(value, Value::I64(5));
    }

    #[test]
    fn string_find_returns_optional() {
        let (_, out) = run_on_both_engines_io(
            "match \"hello world\".find(\"world\") {\n\t.some(i) -> print_raw(i.show()),\n\t.none -> print_raw(\"none\")\n}",
        );
        assert_eq!(out, "6");
        let (_, out) = run_on_both_engines_io(
            "match \"hello\".find(\"zzz\") {\n\t.some(i) -> print_raw(i.show()),\n\t.none -> print_raw(\"none\")\n}",
        );
        assert_eq!(out, "none");
    }

    #[test]
    fn vm_matches_evaluator_on_utf8_decode() {
        // _utf8_decode packs scalar * 8 + bytes_consumed. Valid scalars at
        // every encoded length, including the boundary scalars around the
        // surrogate gap and the top of the scalar range.
        let cases: &[(&str, i64)] = &[
            ("\"A\"", 65 * 8 + 1),
            ("\"é\"", 0xE9 * 8 + 2),
            ("\"€\"", 0x20AC * 8 + 3),
            ("\"😀\"", 0x1F600 * 8 + 4),
            ("\"\\u{7FF}\"", 0x7FF * 8 + 2),
            ("\"\\u{800}\"", 0x800 * 8 + 3),
            ("\"\\u{D7FF}\"", 0xD7FF * 8 + 3),
            ("\"\\u{E000}\"", 0xE000 * 8 + 3),
            ("\"\\u{FFFF}\"", 0xFFFF * 8 + 3),
            ("\"\\u{10000}\"", 0x10000 * 8 + 4),
            ("\"\\u{10FFFF}\"", 0x10FFFF * 8 + 4),
        ];
        for (lit, expected) in cases {
            let src = format!("let s = {lit}\n_utf8_decode(s.storage, 0, s.byte_count)");
            let (value, _) = run_on_both_engines_io(Box::leak(src.into_boxed_str()));
            assert_eq!(value, Value::I64(*expected), "{lit}");
        }
        // Ill-formed input decodes as U+FFFD error units consuming the
        // maximal subpart (Unicode §3.9.6). Byte views sliced out of valid
        // strings give lone leads, lone continuations, and truncations.
        // (Surrogate/overlong byte sequences are not constructible from
        // talk literals; those range checks are exercised from the valid
        // side by the boundary cases above.)
        let fffd = 0xFFFDi64 * 8;
        let invalid: &[(&str, &str, usize, usize, i64)] = &[
            ("lone 2-byte lead", "\"é\"", 0, 1, fffd + 1),
            ("lone continuation", "\"é\"", 1, 1, fffd + 1),
            ("3-byte truncated to 1", "\"€\"", 0, 1, fffd + 1),
            ("3-byte truncated to 2", "\"€\"", 0, 2, fffd + 2),
            ("4-byte truncated to 3", "\"😀\"", 0, 3, fffd + 3),
            ("continuation as lead", "\"😀\"", 2, 2, fffd + 1),
        ];
        for (label, lit, start, len, expected) in invalid {
            let src = format!(
                "let s = {lit}\nlet sub: Substring = s.utf8().slice({start}, {len})\n_utf8_decode(sub.storage, sub.start, sub.start + sub.byte_count)"
            );
            let (value, _) = run_on_both_engines_io(Box::leak(src.into_boxed_str()));
            assert_eq!(value, Value::I64(*expected), "{label}");
        }
    }

    #[test]
    fn vm_matches_evaluator_on_grapheme_category_lookup() {
        // Spot checks across the generated break table: ASCII fast paths,
        // combining marks, ZWJ, regional indicators, Indic conjuncts,
        // emoji, Hangul, and the ends of the table. Each case sets its own
        // bit so a failure names the case.
        let (value, _) = run_on_both_engines_io(concat!(
            "let failures = 0\n",
            "if _grapheme_category(97) != _GC_OTHER { failures = failures + 1 }\n",
            "if _grapheme_category(13) != _GC_CR { failures = failures + 2 }\n",
            "if _grapheme_category(10) != _GC_LF { failures = failures + 4 }\n",
            "if _grapheme_category(0) != _GC_CONTROL { failures = failures + 8 }\n",
            "if _grapheme_category(127) != _GC_CONTROL { failures = failures + 16 }\n",
            // U+0301 combining acute: GCB Extend and InCB Extend.
            "if _grapheme_category(769) != _GC_EXTEND_INCB_EXTEND { failures = failures + 32 }\n",
            // U+200D zero-width joiner.
            "if _grapheme_category(8205) != _GC_ZWJ { failures = failures + 64 }\n",
            // U+1F1FA regional indicator U.
            "if _grapheme_category(127482) != _GC_REGIONAL_INDICATOR { failures = failures + 128 }\n",
            // U+094D Devanagari virama: InCB Linker.
            "if _grapheme_category(2381) != _GC_EXTEND_INCB_LINKER { failures = failures + 256 }\n",
            // U+0915 Devanagari KA: InCB Consonant.
            "if _grapheme_category(2325) != _GC_INCB_CONSONANT { failures = failures + 512 }\n",
            // U+1F600 emoji.
            "if _grapheme_category(128512) != _GC_EXT_PICT { failures = failures + 1024 }\n",
            // Hangul L / LV / LVT.
            "if _grapheme_category(4352) != _GC_HANGUL_L { failures = failures + 2048 }\n",
            "if _grapheme_category(44032) != _GC_HANGUL_LV { failures = failures + 4096 }\n",
            "if _grapheme_category(44033) != _GC_HANGUL_LVT { failures = failures + 8192 }\n",
            // Top of the scalar range: unassigned plane-16 code points.
            "if _grapheme_category(1114111) != _GC_OTHER { failures = failures + 16384 }\n",
            "failures",
        ));
        assert_eq!(value, Value::I64(0));
    }

    #[test]
    fn vm_matches_evaluator_on_shadowed_locals() {
        // Same-named lets in sibling blocks are independent bindings.
        let (value, _) = run_on_both_engines_io(
            "func f(x: Int) -> Int {\n\tlet out = 0\n\tif x < 10 {\n\t\tlet y = x * 2\n\t\tout = y\n\t}\n\tif x < 20 {\n\t\tlet y = x * 3\n\t\tout = y\n\t}\n\tout\n}\nf(15)",
        );
        assert_eq!(value, Value::I64(45));
        // Nested shadowing: the inner binding wins inside its block, the
        // outer binding survives after it.
        let (value, _) = run_on_both_engines_io(
            "func g(x: Int) -> Int {\n\tlet y = 1\n\tlet inner = 0\n\tif x < 20 {\n\t\tlet y = x * 3\n\t\tinner = y\n\t}\n\tinner + y\n}\ng(5)",
        );
        assert_eq!(value, Value::I64(16));
    }

    #[test]
    fn vm_matches_evaluator_on_float_trunc_then_show() {
        let (_, out) =
            run_on_both_engines_io("let x = 1.5\nlet i = x._trunc()\nprint_raw(i.show())");
        assert_eq!(out, "1");
    }

    #[test]
    fn vm_matches_evaluator_on_parametered_trailing_blocks() {
        let (value, _) = run_on_both_engines_io(
            "func transform(x: Int, f: (Int) -> Int) -> Int {\n\tf(x)\n}\ntransform(10) { n in n * 2 }",
        );
        assert_eq!(value, Value::I64(20));
    }

    #[test]
    fn vm_matches_evaluator_on_loop_lets_not_evaluated_before_loop() {
        // Regression from the old backend: loop-body let initializers
        // must not run an extra time before the loop starts.
        let (_, out) = run_on_both_engines_io(
            "func side_effect() -> Int {\n\tprint(1)\n\t42\n}\nlet i = 0\nloop {\n\tif i >= 2 { break }\n\tlet x = side_effect()\n\ti = i + 1\n}",
        );
        assert_eq!(out, "1\n1\n");
        let (_, out) = run_on_both_engines_io(
            "let i = 0\nloop {\n\tif i >= 2 { break }\n\tlet x = i + 100\n\tprint(x)\n\ti = i + 1\n}",
        );
        assert_eq!(out, "100\n101\n");
    }

    #[test]
    fn vm_matches_evaluator_on_loop_with_calls_and_io() {
        let (_, out) = run_on_both_engines_io(
            "func double(n: Int) -> Int { n + n }\nlet i = 0\nloop {\n\tif i >= 3 { break }\n\tlet msg = double(i)\n\tprint(msg)\n\ti = i + 1\n}",
        );
        assert_eq!(out, "0\n2\n4\n");
    }

    #[test]
    fn vm_matches_evaluator_on_match_with_break_in_an_arm() {
        let (_, out) = run_on_both_engines_io(
            "enum Opt {\n\tcase yes(Int)\n\tcase no\n}\nlet i = 0\nloop {\n\tlet opt = if i < 3 { Opt.yes(i) } else { Opt.no }\n\tmatch opt {\n\t\t.yes(x) -> {\n\t\t\tprint(x)\n\t\t\ti = i + 1\n\t\t\t()\n\t\t},\n\t\t.no -> break\n\t}\n}",
        );
        assert_eq!(out, "0\n1\n2\n");
    }

    #[test]
    fn vm_matches_evaluator_on_tuple_match_with_borrowed_enum_elements() {
        let (value, out) = run_on_both_engines_io(
            "enum MaybeText {\n\tcase some(String)\n\tcase none\n}\nfunc lengths(lhs: MaybeText, rhs: MaybeText) -> Int {\n\tmatch (lhs, rhs) {\n\t\t(MaybeText.some(a), MaybeText.some(b)) -> a.byte_count + b.byte_count,\n\t\t(MaybeText.none, MaybeText.none) -> 0,\n\t\t_ -> 1\n\t}\n}\nlet lhs = MaybeText.some(\"ab\" + \"cd\")\nlet rhs = MaybeText.some(\"ef\" + \"gh\")\nprint(lengths(lhs, rhs))\nprint(lengths(lhs, rhs))",
        );
        assert_eq!(value, Value::Void);
        assert_eq!(out, "8\n8\n");
    }

    #[test]
    fn vm_matches_evaluator_on_match_on_an_unannotated_next() {
        let (_, out) = run_on_both_engines_io(
            "func main() {\n\tlet a = [42]\n\tlet i = a.iter()\n\tlet opt = i.next()\n\tmatch opt {\n\t\t.some(x) -> print(x),\n\t\t.none -> print(0)\n\t}\n}",
        );
        assert_eq!(out, "42\n");
    }

    #[test]
    fn vm_matches_evaluator_on_leading_dot_in_inference_position() {
        // The leading dot resolves through the solver (the parameter type
        // of `id` is a variable when the argument is checked), so the
        // variant's artifacts flow to lowering from the deferred path.
        let (_, out) = run_on_both_engines_io(
            "enum Maybe<T> {\n\tcase some(T)\n\tcase none\n}\nfunc id<T>(consume x: T) -> T { x }\nlet m: Maybe<Int> = id(.some(42))\nmatch m {\n\t.some(x) -> print(x),\n\t.none -> print(0)\n}",
        );
        assert_eq!(out, "42\n");
    }

    #[test]
    fn vm_matches_evaluator_on_generic_consume_inside_trailing_block() {
        // A generic (Param-typed) consume inside a trailing block tier-2
        // auto-clones per callee invocation (the loop treatment: the
        // body's re-entry self-edge makes a genuine move a checker error,
        // so the consume must clone instead) — both engines run it and
        // agree; concrete-typed consumes in the same position are rejected
        // by the flow checker (see flow_tests re-entry tests).
        assert_eq!(
            run_on_both_engines(
                "func eat<T>(consume x: T) -> Int {\n\t1\n}\nfunc run_twice(f: () -> Int) -> Int {\n\tf() + f()\n}\nfunc check<T>(consume v: T) -> Int {\n\tlet w = v\n\trun_twice {\n\t\teat(w)\n\t}\n}\ncheck(\"hello\" + \" world\")"
            ),
            Value::I64(2)
        );
    }

    #[test]
    fn vm_matches_evaluator_on_match_on_a_rebound_enum_param() {
        let (_, out) = run_on_both_engines_io(
            "enum Maybe<T> {\n\tcase some(T)\n\tcase none\n}\nfunc f(value: Maybe<Int>) -> Int {\n\tlet y = value\n\tmatch y {\n\t\t.some(x) -> x,\n\t\t.none -> 0\n\t}\n}\nprint(f(Maybe.some(42)))",
        );
        assert_eq!(out, "42\n");
    }

    #[test]
    fn vm_matches_evaluator_on_negative_io_counts_pass_through() {
        // A failed read's errno fed straight into the next write (the
        // chat client's loop) must come back untouched, not trap.
        let (value, _) = run_on_both_engines_io(
            "let buf = _alloc<Byte>(16)\nlet r = _io_write(STDOUT_FD, buf, 0 - 91)\n_free(buf)\nr",
        );
        assert_eq!(value, Value::I64(-91));
        let (value, _) = run_on_both_engines_io(
            "let buf = _alloc<Byte>(16)\nlet r = _io_read(STDIN_FD, buf, 0 - 91)\n_free(buf)\nr",
        );
        assert_eq!(value, Value::I64(-91));
    }

    #[test]
    fn vm_matches_evaluator_on_read_loop_with_split_writes() {
        // Two separate writes (prefix + buffer) read back through a loop
        // — the chat client's segment-splitting pattern.
        let (_, out) = run_on_both_engines_io(
            "let fd = _io_socket(AF_INET, SOCK_STREAM, 0)\nlet msg = \"hello\"\n_io_write(fd, msg.storage.base, msg.byte_count)\nlet buf = _alloc<Byte>(1024)\nlet n = _io_read(fd, buf, 1024)\nlet echo = \"echo: \"\n_io_write(fd, echo.storage.base, echo.byte_count)\n_io_write(fd, buf, n)\nlet rbuf = _alloc<Byte>(1024)\nloop {\n\tlet chunk = _io_read(fd, rbuf, 1024)\n\tif chunk <= 0 { break }\n\t_io_write(STDOUT_FD, rbuf, chunk)\n}\n_free(buf)\n_free(rbuf)",
        );
        assert_eq!(out, "echo: hello");
    }

    #[test]
    fn vm_matches_evaluator_on_echo_loop_over_two_connections() {
        // The ChatServer loop body twice over: greeting, read-back, echo.
        let (_, out) = run_on_both_engines_io(
            "let server = _io_socket(AF_INET, SOCK_STREAM, 0)\nlet i = 0\nloop {\n\tif i >= 2 { break }\n\tlet client = _io_accept(server)\n\tlet msg = \"hello\"\n\t_io_write(client, msg.storage.base, msg.byte_count)\n\tlet buf = _alloc<Byte>(1024)\n\tlet n = _io_read(client, buf, 1024)\n\t_io_write(STDOUT_FD, buf, n)\n\t_free(buf)\n\t_io_close(client)\n\ti = i + 1\n}",
        );
        assert_eq!(out, "hellohello");
    }

    #[test]
    fn vm_matches_evaluator_on_binding_surviving_an_early_return_branch() {
        let (_, out) = run_on_both_engines_io(
            "func test(x: Float) -> String {\n\tlet s = x.show()\n\tif x == 0.0 { return s + \"!\" }\n\ts + \"?\"\n}\nprint_raw(test(1.5))",
        );
        assert_eq!(out, "1.5?");
    }

    #[test]
    fn vm_matches_evaluator_on_array_show_through_conditional_conformance() {
        let (_, out) = run_on_both_engines_io(
            "func printy<T: Showable>(showable: T) {\n\tprint_raw(showable.show())\n\tprint_raw(\"\\n\")\n}\nprinty([1, 2, 3])",
        );
        assert_eq!(out, "[1, 2, 3]\n");
    }

    #[test]
    fn free_function_mut_parameter_writes_back() {
        // ADR 0018: `mut c: Counter` on a free function is an exclusive
        // borrow with caller write-back, like a `mut func` receiver.
        let (_, out) = run_on_both_engines_io(
            "struct Counter {\n\tlet count: Int\n}\nfunc bump(mut c: Counter) {\n\tc.count = c.count + 1\n}\nlet c = Counter(count: 1)\nbump(c)\nbump(c)\nprint(c.count)",
        );
        assert_eq!(out, "3\n");
    }

    #[test]
    fn copy_marker_clones_and_balances_frees() {
        // `copy s` forces an O(1) retain at the call; the callee frees its
        // owned copy and the caller's binding frees at scope exit — the
        // strict allocation fence holds on both engines.
        let (_, out) = run_on_both_engines_io(
            "func eat(consume s: String) -> Int {\n\ts.byte_count\n}\nlet s = \"hi\" + \"!\"\nlet n = eat(copy s)\nprint(n + s.byte_count)",
        );
        assert_eq!(out, "6\n");
    }

    #[test]
    fn borrowed_generic_rvalue_argument_is_freed_by_the_caller() {
        // An rvalue passed to a borrowed generic parameter stays the
        // caller's to free once the call returns (ADR 0018: unadorned
        // params borrow).
        let (_, out) = run_on_both_engines_io(
            "func peek<T>(x: T) -> Int { 0 }\npeek([1, 2, 3])\nprint_raw(\"ok\")",
        );
        assert_eq!(out, "ok");
    }

    #[test]
    fn borrowed_concrete_rvalue_argument_is_freed_by_the_caller() {
        let (_, out) = run_on_both_engines_io(
            "func peek(x: Array<Int>) -> Int { 0 }\npeek([1, 2, 3])\nprint_raw(\"ok\")",
        );
        assert_eq!(out, "ok");
    }

    #[test]
    fn borrowed_array_show_frees_its_element_string_temps() {
        let (_, out) = run_on_both_engines_io("print_raw([1, 2].show())\nprint_raw(\"\\n\")");
        assert_eq!(out, "[1, 2]\n");
    }

    // ----- The HTTP server's request handling, scripted (no sockets) ------

    #[test]
    fn vm_matches_evaluator_on_http_handle_for_a_registered_route() {
        let (_, out) = run_on_both_engines_io(
            "let http = HTTP.Server()\nhttp.get(\"/\", func() { \"root\" })\nlet wire = http.handle(\"GET / HTTP/1.1\\r\\nHost: localhost\\r\\n\\r\\n\")\nprint(wire)",
        );
        assert!(out.contains("HTTP/1.1 200 OK\r\n"), "{out:?}");
        assert!(
            out.contains("Content-Type: text/plain; charset=utf-8\r\n"),
            "{out:?}"
        );
        assert!(out.contains("Content-Length: 4\r\n"), "{out:?}");
        assert!(out.contains("\r\n\r\nroot"), "{out:?}");
    }

    #[test]
    fn vm_matches_evaluator_on_http_handle_for_an_unknown_route() {
        let (_, out) = run_on_both_engines_io(
            "let http = HTTP.Server()\nhttp.get(\"/\", func() { \"root\" })\nlet wire = http.handle(\"GET /missing HTTP/1.1\\r\\nHost: localhost\\r\\n\\r\\n\")\nprint(wire)",
        );
        assert!(out.contains("HTTP/1.1 404 Not Found\r\n"), "{out:?}");
        assert!(out.contains("Content-Length: 9\r\n"), "{out:?}");
        assert!(out.contains("\r\n\r\nNot Found"), "{out:?}");
    }

    #[test]
    fn vm_matches_evaluator_on_http_handle_rejecting_non_get() {
        let (_, out) = run_on_both_engines_io(
            "let http = HTTP.Server()\nhttp.get(\"/\", func() { \"root\" })\nlet wire = http.handle(\"POST / HTTP/1.1\\r\\nHost: localhost\\r\\n\\r\\n\")\nprint(wire)",
        );
        assert!(out.contains("HTTP/1.1 404 Not Found\r\n"), "{out:?}");
    }

    #[test]
    fn vm_matches_evaluator_on_http_handler_running_per_request() {
        let (_, out) = run_on_both_engines_io(
            "let http = HTTP.Server()\nhttp.get(\"/\", func() {\n\tprint(\"HIT\")\n\t\"root\"\n})\nhttp.handle(\"GET / HTTP/1.1\\r\\nHost: localhost\\r\\n\\r\\n\")\nhttp.handle(\"GET / HTTP/1.1\\r\\nHost: localhost\\r\\n\\r\\n\")",
        );
        assert_eq!(out, "HIT\nHIT\n");
    }

    #[test]
    fn vm_matches_evaluator_on_http_handle_with_multiple_routes() {
        let (_, out) = run_on_both_engines_io(
            "let http = HTTP.Server()\nhttp.get(\"/\", func() { \"root\" })\nhttp.get(\"/health\", func() { \"ok\" })\nlet wire = http.handle(\"GET /health HTTP/1.1\\r\\nHost: localhost\\r\\n\\r\\n\")\nprint(wire)",
        );
        assert!(out.contains("HTTP/1.1 200 OK\r\n"), "{out:?}");
        assert!(out.contains("Content-Length: 2\r\n"), "{out:?}");
        assert!(out.contains("\r\n\r\nok"), "{out:?}");
    }

    /// Real libc descriptors (StdioIO): heap bytes round-trip through an
    /// actual Unix socketpair, bypassing CaptureIO's simulated loopback —
    /// the byte-level check on the host io marshaling.
    #[test]
    #[cfg(unix)]
    fn vm_round_trips_heap_bytes_through_a_real_socketpair() {
        use crate::vm::io::{IO, StdioIO};

        struct Guard([i32; 2]);
        impl Drop for Guard {
            fn drop(&mut self) {
                unsafe {
                    libc::close(self.0[0]);
                    libc::close(self.0[1]);
                }
            }
        }
        let mut fds: [i32; 2] = [0; 2];
        let ret =
            unsafe { libc::socketpair(libc::AF_UNIX, libc::SOCK_STREAM, 0, fds.as_mut_ptr()) };
        assert_eq!(ret, 0, "socketpair failed");
        let _guard = Guard(fds);
        let (read_fd, write_fd) = (fds[0] as i64, fds[1] as i64);

        let mut io = StdioIO;
        let written = io.write(write_fd, b"Hello from Talk!\n");
        assert_eq!(written, 17);

        let code = format!(
            "let buf = _alloc<Byte>(1024)\nlet n = _io_read({read_fd}, buf, 1024)\n_io_write({write_fd}, buf, n)\n_free(buf)\nn"
        );
        let code = unsafe_marked_if_raw(&code);
        let driver = Driver::new(
            vec![Source::from(code.as_str())],
            DriverConfig::new("SocketPairTest"),
        );
        let typed = driver
            .parse()
            .expect("parse")
            .resolve_names()
            .expect("resolve")
            .type_check();
        assert!(
            !typed.has_errors(),
            "type errors: {:?}",
            typed.diagnostics()
        );
        let mut lowered = typed.lower();
        assert!(
            lowered.phase.diagnostics.is_empty(),
            "lowering: {:?}",
            lowered.phase.diagnostics
        );
        // run_vm executes against the host (StdioIO).
        let value = lowered.run_vm().expect("vm");
        assert_eq!(value, Value::I64(17));

        let mut buf = vec![0u8; 1024];
        let n = io.read(read_fd, &mut buf);
        assert_eq!(n, 17);
        assert_eq!(&buf[..17], b"Hello from Talk!\n");
    }

    #[test]
    fn vm_matches_evaluator_on_generic_methods() {
        // A method's own generics instantiate per call site; each
        // instantiation monomorphizes separately.
        let (value, _) = run_on_both_engines_io(
            "struct Person {\n\tfunc getAge<T>(consume t: T) -> T { t }\n}\nlet a = Person().getAge(123)\nlet b = Person().getAge(1.5)\n(a, b)",
        );
        assert_eq!(
            value,
            Value::Tuple(std::rc::Rc::new(vec![Value::I64(123), Value::F64(1.5)]))
        );
    }

    #[test]
    fn vm_matches_evaluator_on_enum_methods() {
        // Methods on enums dispatch like struct methods; self matches
        // its own variants.
        let (value, _) = run_on_both_engines_io(
            "enum Fizz<T> {\n\tcase foo(T)\n\tcase bar(T)\n\n\tfunc unwrap() -> T {\n\t\tmatch self {\n\t\t\t.foo(t) -> t,\n\t\t\t.bar(t) -> t\n\t\t}\n\t}\n}\nlet a = Fizz.foo(123).unwrap()\nlet b = Fizz.bar(1.5).unwrap()\n(a, b)",
        );
        assert_eq!(
            value,
            Value::Tuple(std::rc::Rc::new(vec![Value::I64(123), Value::F64(1.5)]))
        );
    }

    #[test]
    fn vm_matches_evaluator_on_row_polymorphic_projections() {
        // One function, two row instantiations: each call's concrete row
        // splices into the signature at monomorphization, so the field
        // index is computed per specialization.
        let (value, _) = run_on_both_engines_io(
            "func fstA(r) { r.a }\nlet x = fstA({ a: 1 })\nlet y = fstA({ a: 2, b: true })\nx + y",
        );
        assert_eq!(value, Value::I64(3));
        let (value, _) = run_on_both_engines_io(
            "func second(r) { r.z }\nlet x = second({ y: 123, z: 40 })\nlet f = second({ a: true, z: 2 })\nx + f",
        );
        assert_eq!(value, Value::I64(42));
    }

    #[test]
    fn vm_matches_evaluator_on_member_constrained_functions() {
        // A function generalized over a member constraint: each call
        // site's specialization resolves its own method.
        let (value, _) = run_on_both_engines_io(
            "struct A {\n\tfunc go() -> Int { 1 }\n}\nstruct B {\n\tfunc go() -> Int { 2 }\n}\nfunc call_go(x) {\n\tx.go()\n}\nlet a = call_go(A())\nlet b = call_go(B())\na + b",
        );
        assert_eq!(value, Value::I64(3));
        // The same shape over a FIELD — and the constraint is structural,
        // so an anonymous record with the field discharges it too.
        let (value, _) = run_on_both_engines_io(
            "struct P {\n\tlet n: Int\n}\nstruct Q {\n\tlet n: Int\n\tlet extra: Bool\n}\nfunc get_n(x) {\n\tx.n\n}\nlet p = get_n(P(n: 40))\nlet q = get_n(Q(n: 2, extra: true))\nlet r = get_n({n: 100})\np + q + r",
        );
        assert_eq!(value, Value::I64(142));
    }

    #[test]
    fn vm_matches_evaluator_on_protocol_static_disambiguation() {
        // Both protocols give Int an `m`; the protocol-static call names
        // which witness runs, so the sum proves each call hit its own.
        let (value, _) = run_on_both_engines_io(
            "protocol Aa {\n\tfunc m() -> Int\n}\nprotocol Bb {\n\tfunc m() -> Int\n}\nextend Int: Aa {\n\tfunc m() -> Int { 1 }\n}\nextend Int: Bb {\n\tfunc m() -> Int { 2 }\n}\nAa.m(5) + Bb.m(5)",
        );
        assert_eq!(value, Value::I64(3));
    }

    fn run_raw_module(code: Vec<Insn>, consts: Vec<Value>) -> Result<Value, String> {
        let module = Module {
            chunks: vec![Chunk {
                name: "main".into(),
                code,
                arity: 0,
                n_regs: 6,
                unwind: vec![],
            }],
            consts,
            arg_pool: vec![],
            switch_pool: vec![],
            traps: vec![],
            statics: vec![],
            entry: 0,
        };
        let mut io = CaptureIO::default();
        run(&module, &mut io)
    }

    #[test]
    fn vm_free_marks_allocation_dead() {
        let value = run_raw_module(
            vec![
                Insn::Const { dest: 0, k: 0 },
                Insn::Alloc { dest: 1, count: 0 },
                Insn::Free { dest: 2, ptr: 1 },
                Insn::Ret { src: 2 },
            ],
            vec![Value::I64(8)],
        )
        .expect("valid free");
        assert_eq!(value, Value::Void);
    }

    #[test]
    fn vm_rejects_double_free() {
        let error = run_raw_module(
            vec![
                Insn::Const { dest: 0, k: 0 },
                Insn::Alloc { dest: 1, count: 0 },
                Insn::Free { dest: 2, ptr: 1 },
                Insn::Free { dest: 3, ptr: 1 },
                Insn::Ret { src: 3 },
            ],
            vec![Value::I64(8)],
        )
        .expect_err("double-free should fail");
        assert!(error.contains("double free"), "{error}");
        // Balance-at-trap (plan 6.2c): the trap report carries the
        // allocation-balance state for diagnosis.
        assert!(error.contains("balance at trap"), "{error}");
    }

    #[test]
    fn vm_rejects_load_after_free() {
        let error = run_raw_module(
            vec![
                Insn::Const { dest: 0, k: 0 },
                Insn::Alloc { dest: 1, count: 0 },
                Insn::Free { dest: 2, ptr: 1 },
                Insn::Load {
                    dest: 3,
                    ptr: 1,
                    kind: MemKind::I64,
                },
                Insn::Ret { src: 3 },
            ],
            vec![Value::I64(8)],
        )
        .expect_err("use-after-free should fail");
        assert!(error.contains("invalid pointer"), "{error}");
    }

    #[test]
    fn vm_rejects_io_open_at_one_past_heap_allocation() {
        let error = run_raw_module(
            vec![
                Insn::Const { dest: 0, k: 0 },
                Insn::Const { dest: 4, k: 1 },
                Insn::Const { dest: 5, k: 1 },
                Insn::Alloc { dest: 1, count: 0 },
                Insn::Add {
                    dest: 2,
                    a: 1,
                    b: 0,
                },
                Insn::Io {
                    dest: 3,
                    op: crate::vm::IoOp::Open,
                    a: 2,
                    b: 4,
                    c: 5,
                },
                Insn::Ret { src: 3 },
            ],
            vec![Value::I64(4), Value::I64(0)],
        )
        .expect_err("one-past heap pointer should fail");
        assert!(
            error.contains("out of bounds") || error.contains("invalid pointer"),
            "{error}"
        );
    }

    #[test]
    fn vm_rejects_io_open_at_zero_length_heap_allocation() {
        let error = run_raw_module(
            vec![
                Insn::Const { dest: 0, k: 0 },
                Insn::Const { dest: 4, k: 0 },
                Insn::Const { dest: 5, k: 0 },
                Insn::Alloc { dest: 1, count: 0 },
                Insn::Io {
                    dest: 2,
                    op: crate::vm::IoOp::Open,
                    a: 1,
                    b: 4,
                    c: 5,
                },
                Insn::Ret { src: 2 },
            ],
            vec![Value::I64(0)],
        )
        .expect_err("zero-length heap pointer should fail");
        assert!(error.contains("invalid pointer"), "{error}");
    }

    #[test]
    fn vm_display_rejects_freed_string_storage() {
        let module = Module {
            chunks: vec![Chunk {
                name: "main".into(),
                code: vec![
                    Insn::Const { dest: 0, k: 0 },
                    Insn::Const { dest: 2, k: 0 },
                    Insn::Alloc { dest: 1, count: 0 },
                    Insn::RecordNew {
                        dest: 3,
                        symbol: crate::vm::runtime_symbol(Symbol::String),
                        args_start: 0,
                        args_len: 3,
                    },
                    Insn::Free { dest: 4, ptr: 1 },
                    Insn::Ret { src: 3 },
                ],
                arity: 0,
                n_regs: 6,
                unwind: vec![],
            }],
            consts: vec![Value::I64(4)],
            arg_pool: vec![1, 2, 2],
            switch_pool: vec![],
            traps: vec![],
            statics: vec![],
            entry: 0,
        };
        let names = ValueNames {
            string_struct: Some(crate::vm::runtime_symbol(Symbol::String)),
            ..ValueNames::default()
        };
        let mut io = CaptureIO::default();
        let error =
            run_displayed(&module, &mut io, &names).expect_err("freed string should not display");
        assert!(error.contains("invalid pointer"), "{error}");
    }

    #[test]
    fn vm_display_rejects_negative_string_length() {
        let module = Module {
            chunks: vec![Chunk {
                name: "main".into(),
                code: vec![
                    Insn::Const { dest: 0, k: 0 },
                    Insn::Const { dest: 2, k: 1 },
                    Insn::Alloc { dest: 1, count: 0 },
                    Insn::RecordNew {
                        dest: 3,
                        symbol: crate::vm::runtime_symbol(Symbol::String),
                        args_start: 0,
                        args_len: 3,
                    },
                    Insn::Ret { src: 3 },
                ],
                arity: 0,
                n_regs: 4,
                unwind: vec![],
            }],
            consts: vec![Value::I64(1), Value::I64(-1)],
            arg_pool: vec![1, 2, 2],
            switch_pool: vec![],
            traps: vec![],
            statics: vec![],
            entry: 0,
        };
        let names = ValueNames {
            string_struct: Some(crate::vm::runtime_symbol(Symbol::String)),
            ..ValueNames::default()
        };
        let mut io = CaptureIO::default();
        let error = run_displayed(&module, &mut io, &names)
            .expect_err("negative length should not display");
        assert!(error.contains("invalid length"), "{error}");
    }

    #[test]
    fn vm_rejects_negative_io_poll_count_before_scaling() {
        let error = run_raw_module(
            vec![
                Insn::Const { dest: 0, k: 0 },
                Insn::Const { dest: 2, k: 1 },
                Insn::Const { dest: 3, k: 2 },
                Insn::Alloc { dest: 1, count: 0 },
                Insn::Io {
                    dest: 4,
                    op: crate::vm::IoOp::Poll,
                    a: 1,
                    b: 2,
                    c: 3,
                },
                Insn::Ret { src: 4 },
            ],
            vec![Value::I64(8), Value::I64(-1), Value::I64(0)],
        )
        .expect_err("negative poll count should fail before count * 8");
        assert!(error.contains("negative count"), "{error}");
    }

    #[test]
    fn bytecode_renders_readably() {
        // `talk ir` shows the scheduled bytecode; pin the format on a
        // hand-built module so it stays readable and stable.
        let module = Module {
            chunks: vec![
                Chunk {
                    name: "main".into(),
                    code: vec![
                        Insn::Const { dest: 0, k: 0 },
                        Insn::Call {
                            dest: 1,
                            chunk: 1,
                            args_start: 0,
                            args_len: 1,
                        },
                        Insn::Branch {
                            cond: 1,
                            then_target: 3,
                            else_target: 4,
                        },
                        Insn::Ret { src: 1 },
                        Insn::Trap { message: 0 },
                    ],
                    arity: 0,
                    n_regs: 2,
                    unwind: vec![],
                },
                Chunk {
                    name: "is_even".into(),
                    code: vec![Insn::Ret { src: 0 }],
                    arity: 1,
                    n_regs: 1,
                    unwind: vec![],
                },
            ],
            consts: vec![Value::I64(42)],
            arg_pool: vec![0],
            switch_pool: vec![],
            traps: vec!["boom".into()],
            statics: vec![],
            entry: 0,
        };
        assert_eq!(
            module.render(),
            "\
chunk 0: main (arity 0, regs 2)
  0: const r0 <- consts[0]
  1: call r1 <- is_even(r0)
  2: branch r1 ? 3 : 4
  3: ret r1
  4: trap \"boom\"
chunk 1: is_even (arity 1, regs 1)
  0: ret r0
"
        );
    }

    #[test]
    fn bytecode_rendering_can_color_with_ansi() {
        let module = Module {
            chunks: vec![Chunk {
                name: "main".into(),
                code: vec![Insn::Ret { src: 0 }],
                arity: 0,
                n_regs: 1,
                unwind: vec![],
            }],
            consts: vec![],
            arg_pool: vec![],
            switch_pool: vec![],
            traps: vec![],
            statics: vec![],
            entry: 0,
        };
        let colored = module.render_ansi();
        assert!(colored.contains("\x1b[1;33mmain\x1b[0m"), "{colored:?}");
        assert!(colored.contains("\x1b[1;35mret\x1b[0m"), "{colored:?}");
        assert!(!module.render().contains('\x1b'));
    }

    #[test]
    fn conditional_field_scrutinee_match_does_not_double_free() {
        assert_eq!(
            run_on_both_engines(
                r#"
                struct Holder {
                    let name: String
                }

                func f(flag: Bool) -> Int {
                    let h = Holder(name: "a" + "b")
                    if flag {
                        match h.name { s -> s.byte_count }
                    }
                    0
                }

                f(true)
                "#
            ),
            Value::I64(0)
        );
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
