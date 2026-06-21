#[cfg(test)]
pub mod tests {
    use crate::compiling::driver::{Driver, DriverConfig, Source};
    use crate::lambda_g::eval::EvalValue;

    /// Full pipeline: parse → resolve → type check → lower to λ_G → run on
    /// the reference evaluator (the executable spec; the bytecode VM is
    /// differentially tested against this in M2).
    fn run(code: &'static str) -> EvalValue {
        let driver = Driver::new(vec![Source::from(code)], DriverConfig::new("LowerTest"));
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
            "lowering diagnostics: {:?}",
            lowered.phase.diagnostics
        );
        lowered.eval_for_tests().expect("evaluation")
    }

    #[test]
    fn generic_effect_handlers_are_diagnosed() {
        // The checker accepts generic effects (instantiated per perform);
        // the backend needs per-instantiation capabilities and rejects
        // them loudly until it has them.
        let driver = Driver::new(
            vec![Source::from(
                "effect 'state<T>(value: T) -> T\n@handle 'state { v in\n\tcontinue v\n}\nlet r = 'state(42)\nprint(r)",
            )],
            DriverConfig::new("LowerTest"),
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
        let lowered = typed.lower();
        assert!(
            lowered
                .phase
                .diagnostics
                .iter()
                .any(|d| d.contains("generic effect")),
            "expected a generic-effect diagnostic, got {:?}",
            lowered.phase.diagnostics
        );
    }

    #[test]
    fn arithmetic_through_operator_witnesses() {
        // 2 + 3 * 3: operators desugar to protocol-static calls; lowering
        // resolves them to Int's conformance witnesses, whose bodies are
        // @_ir splices from core/Operators.tlk.
        assert_eq!(run("2 + 3 * 3"), EvalValue::I64(11));
    }

    #[test]
    fn if_expressions_branch() {
        assert_eq!(run("if true { 1 } else { 2 }"), EvalValue::I64(1));
        assert_eq!(run("if 2 > 3 { 1 } else { 2 }"), EvalValue::I64(2));
    }

    #[test]
    fn locals_and_blocks() {
        assert_eq!(run("let a = 4\nlet b = a + 1\nb * 2"), EvalValue::I64(10));
    }

    #[test]
    fn user_functions_and_calls() {
        assert_eq!(
            run("func double(x: Int) -> Int { x * 2 }\ndouble(21)"),
            EvalValue::I64(42)
        );
    }

    #[test]
    fn generic_functions_monomorphize() {
        // identity used at Int and Float: two specializations, the last
        // top-level expression is the program value.
        assert_eq!(
            run("func identity(x) { x }\nidentity(123)\nidentity(1.5)"),
            EvalValue::F64(1.5)
        );
    }

    #[test]
    fn early_returns() {
        assert_eq!(
            run("func f(x: Int) -> Int {\n\tif x > 0 { return 1 }\n\treturn 2\n}\nf(5)"),
            EvalValue::I64(1)
        );
    }

    #[test]
    fn loops_with_mutable_locals() {
        // Mutable locals are assignment-converted to cells (ORBIT-style);
        // loops are recursive continuations.
        assert_eq!(
            run(
                "func count() -> Int {\n\tlet i = 0\n\tloop {\n\t\tif i >= 5 { break }\n\t\ti = i + 1\n\t}\n\ti\n}\ncount()"
            ),
            EvalValue::I64(5)
        );
    }

    #[test]
    fn conditional_loops() {
        assert_eq!(
            run(
                "func sum() -> Int {\n\tlet total = 0\n\tlet i = 0\n\tloop i < 4 {\n\t\ttotal = total + i\n\t\ti = i + 1\n\t}\n\ttotal\n}\nsum()"
            ),
            EvalValue::I64(6)
        );
    }

    #[test]
    fn continue_skips() {
        assert_eq!(
            run(
                "func evens() -> Int {\n\tlet total = 0\n\tlet i = 0\n\tloop {\n\t\tif i >= 6 {\n\t\t\tbreak\n\t\t}\n\t\ti = i + 1\n\t\tif i > 3 {\n\t\t\tcontinue\n\t\t}\n\t\ttotal = total + i\n\t}\n\ttotal\n}\nevens()"
            ),
            EvalValue::I64(6)
        );
    }

    #[test]
    fn fib_runs_through_defaults_and_witnesses() {
        // fib exercises: recursion, Comparable.lte's protocol DEFAULT body
        // (`self.equals(rhs) || !self.gt(rhs)` — ||-desugar, Not witness,
        // Equatable/Comparable witnesses), Subtract/Add witnesses, and
        // monomorphization of fib itself.
        assert_eq!(
            run(
                "func fib(n) {\n\tif n <= 1 { return n }\n\treturn fib(n - 2) + fib(n - 1)\n}\nfib(10)"
            ),
            EvalValue::I64(55)
        );
    }
}
