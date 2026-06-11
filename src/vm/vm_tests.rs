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
        let lowered = driver
            .parse()
            .unwrap()
            .resolve_names()
            .unwrap()
            .type_check()
            .lower();
        assert_eq!(lowered.run_vm().expect("vm"), Value::I64(6765));
    }
}
