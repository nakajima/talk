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
    fn all_return_match_with_live_local_lowers() {
        // A needs-release local live at a match whose arms ALL return: the
        // candidates at the (dataflow-unreachable) join must classify Dead,
        // not reach lowering unelaborated.
        run("func f() {\n\tlet s = \"e\"\n\tmatch 0 {\n\t\t_ -> return\n\t}\n}\nf()");
    }

    #[test]
    fn all_return_inner_match_with_live_binder_lowers() {
        // Same shape through a match-pattern binder instead of a declared
        // local (the PatternBindLocal flavor).
        run(
            "func f() {\n\tmatch Optional.some(\"e\") {\n\t\t.some(s) -> {\n\t\t\tmatch 0 {\n\t\t\t\t_ -> return\n\t\t\t}\n\t\t},\n\t\t.none -> ()\n\t}\n}\nf()",
        );
    }

    #[test]
    fn unwind_entries_ride_capability_passing_applications() {
        // ADR 0027: a perform with an owned local live across it carries
        // an unwind entry (rendered as a trailing `unwind …` annotation)
        // whose body frees the local and terminates in `unwind_done`.
        let ir = lowered_ir(
            "effect 'oops(error) -> Never\n@handle 'oops { err in print(err) }\nfunc boom() 'oops -> () {\n\tlet owned = [1, 2]\n\t'oops(\"bang\")\n}\nboom()",
        );
        assert!(
            ir.contains("unwind unwind_entry"),
            "expected an unwind operand on the perform application:\n{ir}"
        );
        assert!(
            ir.contains("unwind_done"),
            "expected the entry to terminate in unwind_done:\n{ir}"
        );
    }

    #[test]
    fn suspension_sites_with_nothing_live_carry_no_unwind_entry() {
        // The zero-cost half: when no owned local is live across the
        // suspension, no entry is minted (code size only where needed).
        let ir = lowered_ir(
            "effect 'oops(error) -> Never\n@handle 'oops { err in print(err) }\nfunc boom() 'oops -> () {\n\t'oops(\"bang\")\n}\nboom()",
        );
        assert!(
            !ir.contains("unwind_entry"),
            "expected no unwind entries when nothing owned is live:\n{ir}"
        );
    }

    #[test]
    fn character_literals_match_by_utf8_bytes() {
        assert_eq!(
            run("match '😎' { '😁' -> 1, '\\u{1F60E}' -> 2, _ -> 3 }"),
            EvalValue::I64(2)
        );
        assert_eq!(
            run("match 'a' { 'ab' -> 1, 'a' -> 2, _ -> 3 }"),
            EvalValue::I64(2)
        );
        assert_eq!(
            run(
                "func test() -> Int {\n\tlet chars = \"x😎\".iter()\n\tchars.next()\n\tmatch chars.next() { .some('😎') -> 4, .some(_) -> 5, .none -> 6 }\n}\ntest()"
            ),
            EvalValue::I64(4)
        );
    }

    #[test]
    fn imported_stdlib_memberwise_init_has_a_body() {
        let ir = lowered_ir("fs::Directory(path: Path([]))");
        assert!(ir.contains("func init("), "{ir}");
    }

    #[test]
    fn generic_effect_handlers_lower() {
        // A generic effect's handler: the capability materializes from the
        // handler template at the perform's instantiation
        // (docs/generic-effects-plan.md), so this runs instead of hitting
        // the old "not yet supported" fence.
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
        let mut lowered = typed.lower();
        assert!(
            lowered.phase.diagnostics.is_empty(),
            "lowering: {:?}",
            lowered.phase.diagnostics
        );
        let (_, out) = lowered.eval_with_output().expect("evaluator");
        assert_eq!(out, "42\n");
    }

    #[test]
    fn non_first_mut_parameter_is_diagnosed() {
        // V1 inout supports exactly one write-back slot (the receiver /
        // first parameter). A `mut` parameter anywhere else would silently
        // drop its mutations, so lowering rejects it.
        let driver = Driver::new(
            vec![Source::from(
                "struct Counter {\n\tlet count: Int\n}\nfunc bump(tag: Int, mut c: Counter) {\n\tc.count = c.count + 1\n}\nlet c = Counter(count: 1)\nbump(0, c)\nprint(c.count)",
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
                .any(|diagnostic| diagnostic.contains("mut` parameter")),
            "expected a mut-parameter diagnostic, got {:?}",
            lowered.phase.diagnostics
        );
    }

    #[test]
    fn mut_parameter_on_a_function_value_is_diagnosed() {
        // Value calls have no inout convention: a closure's `mut` param
        // would silently drop its mutations, so lowering rejects it.
        let driver = Driver::new(
            vec![Source::from(
                "struct Counter {\n\tlet count: Int\n}\nfunc call_it(f: (mut Counter) -> Int, mut c: Counter) -> Int {\n\tf(c)\n}\nfunc bump(mut c: Counter) -> Int {\n\tc.count = c.count + 1\n\tc.count\n}\nlet c = Counter(count: 0)\ncall_it(bump, c)",
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
                .any(|diagnostic| diagnostic.contains("mut` parameter on a function value")),
            "expected a mut-parameter diagnostic, got {:?}",
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
    fn conditional_equatable_witness_specializes_derived_payload_conformances() {
        assert_eq!(
            run(
                "struct Token {\n\tlet kind: Int\n}\nstruct LexError {\n\tlet code: Int\n}\nlet left: Result<Token, LexError> = .ok(Token(kind: 1))\nlet right: Result<Token, LexError> = .ok(Token(kind: 1))\nleft == right"
            ),
            EvalValue::Bool(true)
        );
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
    fn loop_condition_match_reevaluates_from_header() {
        assert_eq!(
            run(
                "let i = 0\nloop match i < 3 { true -> true, false -> false } {\n\ti = i + 1\n}\ni",
            ),
            EvalValue::I64(3)
        );
    }

    #[test]
    fn value_block_rhs_delivers_to_binding() {
        assert_eq!(
            run("func f() -> Int {\n\tlet x = {\n\t\tlet y = 40\n\t\ty + 2\n\t}\n\tx\n}\nf()"),
            EvalValue::I64(42)
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
            "func maybe(flag: Bool) -> Int {\n\tlet s = \"hi\" + \"!\"\n\tif flag {\n\t\tlet t = s\n\t\tt.byte_count\n\t} else {\n\t\t2\n\t}\n\t0\n}\nmaybe(false)",
        );
        assert!(ir.contains("cell_new(true)"), "{ir}");
        assert!(has_drop_flag_set(&ir, false), "{ir}");
        assert!(has_drop_flag_branch(&ir), "{ir}");
    }

    #[test]
    fn consuming_method_receiver_clears_conditional_drop_flag() {
        let ir = lowered_ir(
            "extend String {\n\tconsuming func consume_len() -> Int {\n\t\tself.byte_count\n\t}\n}\nfunc f(flag: Bool) -> Int {\n\tlet s = \"a\" + \"b\"\n\tif flag { s.consume_len() }\n\t0\n}\nf(true)",
        );
        let top_level_clears = ir.matches("cell_set(var drop_flag, false)").count();
        assert!(
            top_level_clears >= 2,
            "expected the consuming receiver and scope drop to both clear the top drop flag:\n{ir}"
        );
    }

    #[test]
    fn open_field_move_drop_uses_field_drop_flag() {
        let ir = lowered_ir(
            "struct Person {\n\tlet name: String\n\tlet title: String\n\tlet age: Int\n}\nfunc f() -> Int {\n\tlet person = Person(name: \"Pat\" + \"\", title: \"Dr\" + \"\", age: 41)\n\tlet name = person.name\n\tname.byte_count + person.title.byte_count + person.age\n}\nf()",
        );
        assert!(ir.contains("cell_new(true)"), "{ir}");
        assert!(has_drop_flag_set(&ir, false), "{ir}");
        assert!(has_drop_flag_branch(&ir), "{ir}");
        assert!(ir.contains("get_field(1, var let_person)"), "{ir}");
    }

    #[test]
    fn field_assignment_reinitializes_drop_flag() {
        let ir = lowered_ir(
            "struct Person {\n\tlet name: String\n\tlet title: String\n}\nfunc f() -> Int {\n\tlet person = Person(name: \"Pat\" + \"\", title: \"Dr\" + \"\")\n\tlet old = person.name\n\tperson.name = \"Sue\" + \"\"\n\told.byte_count + person.name.byte_count + person.title.byte_count\n}\nf()",
        );
        assert!(has_drop_flag_set(&ir, false), "{ir}");
        assert!(has_drop_flag_set(&ir, true), "{ir}");
        assert!(has_drop_flag_branch(&ir), "{ir}");
    }

    #[test]
    fn mixed_rawptr_struct_drop_frees_sibling_droppable_fields() {
        // R5/6.3(c): teardown of a struct with a RawPtr field PLUS another
        // droppable field must free BOTH — the walk used to stop at the
        // first RawPtr field and silently leak the siblings. The eval leak
        // fence (scalar result) asserts the balance.
        assert_eq!(
            run(
                "// unsafe\nstruct Mixed {\n\tlet buf: RawPtr\n\tlet name: String\n}\nfunc check() -> Int {\n\tlet m = Mixed(buf: _alloc<Byte>(4), name: \"a\" + \"b\")\n\t0\n}\ncheck()"
            ),
            EvalValue::I64(0)
        );
    }

    #[test]
    fn mixed_rawptr_struct_retain_covers_sibling_droppable_fields() {
        // The retain twin: a tier-2 clone of the mixed struct must bump
        // BOTH buffers (raw field + String), so the clone and the region's
        // original each free exactly once per buffer.
        assert_eq!(
            run(
                "// unsafe\nstruct Mixed {\n\tlet buf: RawPtr\n\tlet name: String\n}\nextend Mixed: CheapClone {}\nstruct Holder<Value> 'heap {\n\tlet value: Value\n}\nfunc extract<Value: CheapClone>(h: Holder<Value>) -> Value {\n\th.value\n}\nfunc check() -> Int {\n\tlet h = Holder(value: Mixed(buf: _alloc<Byte>(4), name: \"a\" + \"b\"))\n\tlet m = extract(h)\n\tm.name.byte_count\n}\ncheck()"
            ),
            EvalValue::I64(2)
        );
    }

    #[test]
    fn mixed_rawptr_struct_retain_walk_matches_drop_walk() {
        // The two walks visit the same field set: Mixed's retain must
        // touch the raw buffer AND the String's storage base (2 retains),
        // exactly the pointers its teardown frees.
        let ir = lowered_ir(
            "// unsafe\nstruct Mixed {\n\tlet buf: RawPtr\n\tlet name: String\n}\nextend Mixed: CheapClone {}\nstruct Holder<Value> 'heap {\n\tlet value: Value\n}\nfunc extract<Value: CheapClone>(h: Holder<Value>) -> Value {\n\th.value\n}\nfunc check() -> Int {\n\tlet h = Holder(value: Mixed(buf: _alloc<Byte>(4), name: \"a\" + \"b\"))\n\tlet m = extract(h)\n\tm.name.byte_count\n}\ncheck()",
        );
        // Op-level retains on the walked fields render as
        // `retain(get_field(…))` — the `retain` continuation's declaration
        // and application don't match the pattern.
        let retain_count = ir.matches("retain(get_field").count();
        assert_eq!(
            retain_count, 2,
            "the retain walk must visit both droppable fields (raw buf + name's storage), got {retain_count}:\n{ir}"
        );
    }

    #[test]
    fn retain_walk_acquires_regions_of_object_carrying_values() {
        // 6.3(a): the retain walk's RegionAcquire counterpart to the drop
        // walk's RegionRelease. `_retain<M>` over an object-carrying M
        // (unreachable through tier-2 today — typing forbids CheapClone
        // object fields and raw storage rejects objects — but reachable
        // through the splice, and the safety net for widening auto-clone
        // later) must acquire M's regions exactly where M's drop releases
        // them, alongside the sibling buffer retain.
        let ir = lowered_ir(
            "// unsafe\nstruct Obj 'heap {\n\tlet n: Int\n}\nstruct M {\n\tlet o: Obj\n\tlet name: String\n}\nfunc bump(m: &M) -> Int {\n\t_retain<M>(m)\n\t0\n}\nfunc run() -> Int {\n\tlet m = M(o: Obj(n: 1), name: \"a\" + \"b\")\n\tbump(m)\n}\nrun()",
        );
        // Scope the assertions to the `_retain<M>` specialization's body —
        // rule-B acquires elsewhere (M's init) must not satisfy them.
        let start = ir
            .find("func _retain<")
            .expect("the _retain specialization is in the program");
        let body_indent = &ir[start..];
        let end = body_indent[5..]
            .find("\nfunc ")
            .map(|i| i + 5)
            .unwrap_or(body_indent.len());
        let walk = &body_indent[..end];
        assert!(
            walk.contains("region_acquire("),
            "the retain walk must acquire the value's regions:\n{walk}"
        );
        assert!(
            walk.contains("retain(get_field"),
            "the retain walk must still bump the sibling String buffer:\n{walk}"
        );
    }

    #[test]
    fn borrowed_derived_show_lowers() {
        let ir = lowered_ir(
            "struct Box {\n\tlet value: Int\n}\nfunc main() {\n\tfor item in [Box(value: 1)] {\n\t\tprint(item)\n\t}\n}",
        );
        assert!(ir.contains("show_Box"), "{ir}");
    }

    #[test]
    fn stdlib_fs_direct_iteration_runs_balanced_on_both_engines() {
        // The old string-presence test's exact program, executed: direct
        // `for` iteration over a borrowed-receiver method source.
        let code = "func main() {\n\tlet directory = fs::Directory(path: Path([\".\"]))\n\tprint(directory)\n\tfor entry in directory.entries() {\n\t\tprint(entry)\n\t}\n}";
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
            "lowering: {:?}",
            lowered.phase.diagnostics
        );
        let (_, vm_out) = lowered.run_vm_with_output().expect("vm");
        let (_, eval_out) = lowered.eval_with_output().expect("evaluator");
        assert_eq!(eval_out, vm_out);
    }

    #[test]
    fn stdlib_fs_directory_runner_runs_balanced_on_both_engines() {
        // ADR 0017's fs-walk shape: a method on a BORROWED receiver as the
        // for-source, with the binder fed to a `(&DirectoryEntry) -> ()`
        // consumer. Executed, not just lowered: the evaluator run asserts
        // the free balance, and both engines must agree on stdout.
        let code = "func walk(directory: &fs::Directory, fn: (&fs::DirectoryEntry) -> ()) {\n\tfor entry in directory.entries() {\n\t\tfn(entry)\n\t}\n}\nfunc main() {\n\tlet directory = fs::Directory(path: Path([\".\"]))\n\tprint(directory)\n\twalk(directory) { entry in\n\t\tprint(entry)\n\t}\n}";
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
        let ir = lowered.phase.program.render();
        assert!(ir.contains("show_DirectoryEntry"), "{ir}");
        let (_, vm_out) = lowered.run_vm_with_output().expect("vm");
        let (_, eval_out) = lowered.eval_with_output().expect("evaluator");
        assert_eq!(eval_out, vm_out, "stdout diverged");
        assert!(!vm_out.is_empty(), "the walk printed nothing");
    }

    #[test]
    fn continue_value_in_a_trailing_block_is_diagnosed() {
        // The checker deliberately lets a trailing block keep the handler
        // context, but lowering has no resume continuation across the
        // closure boundary: that must be a diagnostic, not a silent
        // evaluate-and-discard of the resumed value.
        let code = "effect 'ask(prompt) -> Int\nfunc twice(fn: () -> Int) -> Int {\n\tfn() + fn()\n}\n@handle 'ask { p in\n\ttwice {\n\t\tcontinue 42\n\t}\n}\nlet r = 'ask(\"meaning?\")\nr + 1";
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
        let lowered = typed.lower();
        assert!(
            lowered
                .phase
                .diagnostics
                .iter()
                .any(|d| d.contains("continue with a value outside an effect handler")),
            "expected the trailing-block continue to be diagnosed, got {:?}",
            lowered.phase.diagnostics
        );
    }

    #[test]
    fn break_crossing_a_closure_boundary_is_diagnosed() {
        // A break inside a trailing block crosses a closure boundary: it
        // must be diagnosed, not silently re-lower the enclosing
        // function's post-loop code into the closure. (The handler-body
        // analogue is unreachable today: @handle inside a loop is fenced
        // as a nested block.)
        let code = "func twice(fn: () -> ()) {\n\tfn()\n\tfn()\n}\nfunc f() {\n\tloop true {\n\t\ttwice {\n\t\t\tbreak\n\t\t}\n\t}\n}\nf()";
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
        let lowered = typed.lower();
        assert!(
            lowered
                .phase
                .diagnostics
                .iter()
                .any(|d| d.contains("break outside loop")),
            "expected a break-outside-loop diagnostic, got {:?}",
            lowered.phase.diagnostics
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

    /// Full pipeline, executed on BOTH engines with stdout compared. The
    /// evaluator's leak fence and the VM's live-count assertion (always on
    /// under cfg(test)) make every call a free-balance check.
    fn run_balanced_on_both_engines(code: &'static str) -> String {
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
        let (_, vm_out) = lowered.run_vm_with_output().expect("vm");
        let (_, eval_out) = lowered.eval_with_output().expect("evaluator");
        assert_eq!(eval_out, vm_out, "stdout diverged between engines");
        vm_out
    }

    // ----- Early-exit drop characterization (track 7.1 / M2) --------------
    //
    // These pin the shapes `lower_early_exit_then` must cover from flow's
    // `EarlyExit` candidates alone (ADR 0010 stage 3: the candidates are the
    // single drop authority; lowering keeps no shadow drop stack). Each
    // shape puts droppable owned locals at several scope depths between the
    // exit and its target and asserts balance on both engines.

    #[test]
    fn break_at_depth_drops_loop_locals_and_keeps_enclosing() {
        // `break` from a nested block: the loop-iteration local and the
        // if-block local drop on the exit edge; the enclosing function's
        // local survives the loop and is used after it.
        let out = run_balanced_on_both_engines(
            "func f() -> Int {\n\tlet outer = \"aa\" + \"bb\"\n\tlet i = 0\n\tloop i < 5 {\n\t\ti = i + 1\n\t\tlet ring = \"cc\" + \"dd\"\n\t\tif i == 2 {\n\t\t\tlet deep = \"ee\" + \"ff\"\n\t\t\tbreak\n\t\t}\n\t}\n\touter.byte_count + i\n}\nprint(f())",
        );
        assert_eq!(out, "6\n");
    }

    #[test]
    fn continue_drops_per_iteration_locals_each_iteration() {
        // `continue` re-enters the loop head: the iteration's local must
        // drop on every continue edge (a per-iteration leak amplifies).
        let out = run_balanced_on_both_engines(
            "func f() -> Int {\n\tlet outer = \"aa\" + \"bb\"\n\tlet i = 0\n\tlet total = 0\n\tloop i < 4 {\n\t\ti = i + 1\n\t\tlet ring = \"cc\" + \"dd\"\n\t\tif i == 2 {\n\t\t\tcontinue\n\t\t}\n\t\ttotal = total + ring.byte_count\n\t}\n\ttotal + outer.byte_count\n}\nprint(f())",
        );
        assert_eq!(out, "16\n");
    }

    #[test]
    fn return_from_nested_loop_scopes_drops_all_depths() {
        // `return` from inside if-in-loop: locals at every depth (the
        // if-block's, the iteration's, the function's) drop on the return
        // edge after the returned value is computed from all three.
        let out = run_balanced_on_both_engines(
            "func f() -> Int {\n\tlet outer = \"aa\" + \"bb\"\n\tlet i = 0\n\tloop i < 5 {\n\t\ti = i + 1\n\t\tlet ring = \"cc\" + \"dd\"\n\t\tif i == 3 {\n\t\t\tlet deep = \"ee\" + \"ff\"\n\t\t\treturn deep.byte_count + ring.byte_count + outer.byte_count\n\t\t}\n\t}\n\t0\n}\nprint(f())",
        );
        assert_eq!(out, "12\n");
    }

    #[test]
    fn break_from_inner_of_nested_loops_drops_inner_scope_only() {
        // Nested loops: the inner `break` drops only the inner iteration's
        // local; the outer iteration's local and the function's local stay
        // live (their own scope exits drop them).
        let out = run_balanced_on_both_engines(
            "func f() -> Int {\n\tlet outer = \"aa\" + \"bb\"\n\tlet i = 0\n\tloop i < 3 {\n\t\ti = i + 1\n\t\tlet mid = \"cc\" + \"dd\"\n\t\tlet j = 0\n\t\tloop j < 3 {\n\t\t\tj = j + 1\n\t\t\tlet inner = \"ee\" + \"ff\"\n\t\t\tif j == 2 {\n\t\t\t\tbreak\n\t\t\t}\n\t\t}\n\t}\n\touter.byte_count\n}\nprint(f())",
        );
        assert_eq!(out, "4\n");
    }

    #[test]
    fn break_inside_match_arm_drops_loop_locals() {
        // The arm body is a separate lowered body (the pattern compiler's
        // `make_arm`): a `break` inside it exits the enclosing loop and
        // must still drop the iteration's droppable local.
        let out = run_balanced_on_both_engines(
            "func f() -> Int {\n\tlet outer = \"aa\" + \"bb\"\n\tlet i = 0\n\tloop i < 5 {\n\t\ti = i + 1\n\t\tlet ring = \"cc\" + \"dd\"\n\t\tmatch i {\n\t\t\t2 -> break,\n\t\t\t_ -> 0,\n\t\t}\n\t}\n\touter.byte_count + i\n}\nprint(f())",
        );
        assert_eq!(out, "6\n");
    }

    #[test]
    fn return_inside_match_arm_at_depth_runs_balanced() {
        // `return` from a match arm inside a loop: the arm-scope local, the
        // iteration's local, and the function's local all drop on the
        // return edge.
        let out = run_balanced_on_both_engines(
            "func f() -> Int {\n\tlet outer = \"aa\" + \"bb\"\n\tlet i = 0\n\tloop i < 5 {\n\t\ti = i + 1\n\t\tlet ring = \"cc\" + \"dd\"\n\t\tmatch i {\n\t\t\t3 -> {\n\t\t\t\tlet deep = \"gg\" + \"hh\"\n\t\t\t\treturn deep.byte_count + outer.byte_count\n\t\t\t},\n\t\t\t_ -> 0,\n\t\t}\n\t}\n\t0\n}\nprint(f())",
        );
        assert_eq!(out, "8\n");
    }

    #[test]
    fn temporary_end_disposition_flags_non_static_elaborations() {
        // R6: flow classifies temps `Static` (drop), `Dead` (consumed), or
        // `Open` with a moved path (a consuming projection took one field
        // path; the rest drops) — consumption is static per temp, so temps
        // never carry drop flags. `Conditional` (or a pathless `Open`)
        // therefore means a stage upstream broke that contract: lowering
        // must flag them (debug assert + lowering diagnostic), never skip
        // them silently — a silent skip is a silent leak. Flow cannot
        // produce the Invalid inputs today, so the dispatch is pinned
        // directly.
        use crate::lower::Lowering;
        use crate::lower::mir::{DropElaboration, DropElaborationResult};
        use crate::lower::mir_lowering::TempDropDisposition;

        let result = |kind, moved_path| DropElaborationResult {
            key_path: None,
            kind,
            moved_path,
        };
        assert_eq!(
            Lowering::temp_drop_disposition(Some(&result(DropElaboration::Static, vec![]))),
            TempDropDisposition::Drop
        );
        assert_eq!(
            Lowering::temp_drop_disposition(Some(&result(DropElaboration::Dead, vec![]))),
            TempDropDisposition::Skip
        );
        assert_eq!(
            Lowering::temp_drop_disposition(None),
            TempDropDisposition::Skip
        );
        let field = crate::name_resolution::symbol::Symbol::DeclaredLocal(
            crate::name_resolution::symbol::DeclaredLocalId(1),
        );
        assert_eq!(
            Lowering::temp_drop_disposition(Some(&result(DropElaboration::Open, vec![field]))),
            TempDropDisposition::DropExcept(vec![field])
        );
        assert_eq!(
            Lowering::temp_drop_disposition(Some(&result(DropElaboration::Conditional, vec![]))),
            TempDropDisposition::Invalid(DropElaboration::Conditional)
        );
        assert_eq!(
            Lowering::temp_drop_disposition(Some(&result(DropElaboration::Open, vec![]))),
            TempDropDisposition::Invalid(DropElaboration::Open)
        );
    }

    #[test]
    fn symbol_drop_facts_collects_moves_flags_and_live_unwind_in_one_pass() {
        // `SymbolDropFacts::collect` replaced three per-binding full-body
        // scans (move facts, drop-flag keys, live-at-Unwind facts) with one
        // walk; this pins the per-symbol answers those scans produced.
        use crate::flow::Place;
        use crate::lower::SymbolDropFacts;
        use crate::lower::mir::{
            BasicBlock, BlockId, Body, DropElaboration, DropElaborationResult, DropReason,
            DropTarget, LocatedStatement, ScopeId, Statement, StatementOwnership,
            TerminatorOwnership,
        };
        use crate::name_resolution::symbol::{DeclaredLocalId, Symbol};
        use crate::parsing::node_id::NodeID;

        let local = |id| Symbol::DeclaredLocal(DeclaredLocalId(id));
        let (moved, flagged, suspended, dead, untouched) =
            (local(1), local(2), local(3), local(4), local(5));
        let field = local(6);
        let statement = |kind, ownership| LocatedStatement { kind, ownership };
        let unwind_candidate = |symbol, elaboration| {
            statement(
                Statement::DropCandidate {
                    target: DropTarget::Symbol {
                        id: NodeID::ANY,
                        symbol,
                    },
                    key_path: Some(Place::root(symbol)),
                    reason: DropReason::Unwind,
                    source: NodeID::ANY,
                },
                StatementOwnership {
                    drop: Some(DropElaborationResult {
                        key_path: Some(Place::root(symbol)),
                        kind: elaboration,
                        moved_path: vec![],
                    }),
                    moves: vec![],
                },
            )
        };
        let field_place = Place {
            root: flagged,
            fields: vec![field],
        };
        let body = Body {
            entry: BlockId(0),
            blocks: vec![
                BasicBlock {
                    statements: vec![
                        // A whole-value move: a move fact, root flag only.
                        statement(
                            Statement::ScopeEnter { scope: ScopeId(0) },
                            StatementOwnership {
                                drop: None,
                                moves: vec![Place::root(moved)],
                            },
                        ),
                        // A Conditional field drop + a partial move of the
                        // same field: root flag first, the field key once.
                        statement(
                            Statement::ScopeExit { scope: ScopeId(0) },
                            StatementOwnership {
                                drop: Some(DropElaborationResult {
                                    key_path: Some(field_place.clone()),
                                    kind: DropElaboration::Conditional,
                                    moved_path: vec![],
                                }),
                                moves: vec![field_place.clone()],
                            },
                        ),
                        // Live at a suspension site vs. Dead there.
                        unwind_candidate(suspended, DropElaboration::Static),
                        unwind_candidate(dead, DropElaboration::Dead),
                    ],
                    ..Default::default()
                },
                // Terminator moves count as move facts too.
                BasicBlock {
                    terminator_ownership: TerminatorOwnership {
                        moves: vec![Place::root(suspended)],
                    },
                    ..Default::default()
                },
            ],
            scaffolds: Default::default(),
        };

        let facts = SymbolDropFacts::collect(&body);
        assert!(facts.has_move(moved));
        assert!(facts.has_move(suspended));
        // The field move roots at `flagged`.
        assert!(facts.has_move(flagged));
        assert!(!facts.has_move(untouched));
        assert!(facts.has_live_unwind(suspended));
        assert!(!facts.has_live_unwind(dead));
        assert!(!facts.has_live_unwind(moved));
        assert_eq!(facts.drop_flag_keys(moved), vec![Place::root(moved)]);
        assert_eq!(
            facts.drop_flag_keys(flagged),
            vec![Place::root(flagged), field_place]
        );
        assert_eq!(facts.drop_flag_keys(untouched), Vec::<Place>::new());
    }
}
