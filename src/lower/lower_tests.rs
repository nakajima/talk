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

    fn lowered_ir(code: &'static str) -> String {
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
        lowered.phase.program.render()
    }

    fn has_drop_flag_set(ir: &str, value: bool) -> bool {
        let suffix = if value { ", true)" } else { ", false)" };
        ir.lines()
            .any(|line| line.contains("cell_set(var drop_flag") && line.contains(suffix))
    }

    fn has_drop_flag_branch(ir: &str) -> bool {
        ir.lines()
            .any(|line| line.contains("br(cell_get(var drop_flag"))
    }

    #[test]
    fn imported_stdlib_memberwise_init_has_a_body() {
        let ir = lowered_ir("fs::Directory(path: Path([]))");
        assert!(ir.contains("func init("), "{ir}");
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
    fn sequential_statement_ifs_share_their_tail() {
        let ir = lowered_ir(
            "func f(a: Bool, b: Bool, c: Bool, d: Bool) -> Int {\n\tif a { } else { }\n\tif b { } else { }\n\tif c { } else { }\n\tif d { } else { }\n\t123\n}\nf(true, false, true, false)",
        );
        let tail_copies = ir.matches("var f.k(123)").count();
        assert!(
            tail_copies <= 2,
            "expected the shared tail to be lowered once or twice, got {tail_copies} copies:\n{ir}"
        );
    }

    #[test]
    fn branch_local_owned_values_drop_before_shared_tail() {
        let ir = lowered_ir(
            "func f(a: Bool, b: Bool) -> Int {\n\tif a {\n\t\tlet s = \"a\" + \"b\"\n\t} else {\n\t\tlet t = \"c\" + \"d\"\n\t}\n\tif b { } else { }\n\t123\n}\nf(true, false)",
        );
        assert!(
            ir.contains("free(get_field(0, get_field(0, var let_s)))"),
            "{ir}"
        );
        assert!(
            ir.contains("free(get_field(0, get_field(0, var let_t)))"),
            "{ir}"
        );
        let tail_copies = ir.matches("var f.k(123)").count();
        assert_eq!(
            tail_copies, 1,
            "expected branch-local cleanup to join before the shared tail:\n{ir}"
        );
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
    fn for_loop_continues_to_following_expression() {
        assert_eq!(
            run("func f() -> Int {\n\tfor x in [1] { }\n\t2\n}\nf()"),
            EvalValue::I64(2)
        );
    }

    #[test]
    fn break_and_continue_drop_owned_loop_locals() {
        let break_ir = lowered_ir(
            "func f() -> Int {\n\tloop {\n\t\tlet s = \"a\" + \"b\"\n\t\tbreak\n\t}\n\t0\n}\nf()",
        );
        assert!(
            break_ir.contains("free(get_field(0, get_field(0, var let_s)))"),
            "{break_ir}"
        );
        assert!(break_ir.contains("loop_exit(())"), "{break_ir}");

        let continue_ir = lowered_ir(
            "func f() -> Int {\n\tlet keep_going = true\n\tloop {\n\t\tlet s = \"a\" + \"b\"\n\t\tif keep_going {\n\t\t\tcontinue\n\t\t}\n\t\tbreak\n\t}\n\t0\n}\nf()",
        );
        assert!(
            continue_ir.contains("free(get_field(0, get_field(0, var let_s)))"),
            "{continue_ir}"
        );
        assert!(continue_ir.contains("loop_head(())"), "{continue_ir}");
    }

    #[test]
    fn tail_value_runs_following_scope_drops() {
        let ir = lowered_ir("func f() -> Int {\n\tlet s = \"a\" + \"b\"\n\t123\n}\nf()");
        assert!(
            ir.contains("free(get_field(0, get_field(0, var let_s)))"),
            "{ir}"
        );
        assert!(ir.contains("drop_scope(123)"), "{ir}");
        assert!(ir.contains("var f.k(var drop_scope)"), "{ir}");
    }

    #[test]
    fn conditional_owned_drop_uses_runtime_drop_flag() {
        let ir = lowered_ir(
            "func maybe(flag: Bool) -> Int {\n\tlet s = \"hi\" + \"!\"\n\tif flag {\n\t\tlet t = s\n\t\tt.length\n\t} else {\n\t\t2\n\t}\n\t0\n}\nmaybe(false)",
        );
        assert!(ir.contains("cell_new(true)"), "{ir}");
        assert!(has_drop_flag_set(&ir, false), "{ir}");
        assert!(has_drop_flag_branch(&ir), "{ir}");
    }

    #[test]
    fn open_field_move_drop_uses_field_drop_flag() {
        let ir = lowered_ir(
            "struct Person {\n\tlet name: String\n\tlet title: String\n\tlet age: Int\n}\nfunc f() -> Int {\n\tlet person = Person(name: \"Pat\" + \"\", title: \"Dr\" + \"\", age: 41)\n\tlet name = person.name\n\tname.length + person.title.length + person.age\n}\nf()",
        );
        assert!(ir.contains("cell_new(true)"), "{ir}");
        assert!(has_drop_flag_set(&ir, false), "{ir}");
        assert!(has_drop_flag_branch(&ir), "{ir}");
        assert!(ir.contains("get_field(1, var let_person)"), "{ir}");
    }

    #[test]
    fn field_assignment_reinitializes_drop_flag() {
        let ir = lowered_ir(
            "struct Person {\n\tlet name: String\n\tlet title: String\n}\nfunc f() -> Int {\n\tlet person = Person(name: \"Pat\" + \"\", title: \"Dr\" + \"\")\n\tlet old = person.name\n\tperson.name = \"Sue\" + \"\"\n\told.length + person.name.length + person.title.length\n}\nf()",
        );
        assert!(has_drop_flag_set(&ir, false), "{ir}");
        assert!(has_drop_flag_set(&ir, true), "{ir}");
        assert!(has_drop_flag_branch(&ir), "{ir}");
    }

    #[test]
    fn borrowed_derived_show_lowers() {
        let ir = lowered_ir(
            "struct Box {\n\tlet value: Int\n}\nfunc main() {\n\tfor item in [Box(value: 1)] {\n\t\tprint(item)\n\t}\n}",
        );
        assert!(ir.contains("show_Box"), "{ir}");
    }

    #[test]
    fn stdlib_fs_directory_runner_lowers() {
        let ir = lowered_ir(
            "func main() {\n\tlet directory = fs::Directory(path: Path([\".\"]))\n\tprint(directory)\n\tfor entry in directory.entries() {\n\t\tprint(entry)\n\t}\n}",
        );
        assert!(ir.contains("show_DirectoryEntry"), "{ir}");
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
