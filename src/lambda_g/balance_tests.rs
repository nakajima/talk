//! Free-balance verifier tests (ADR 0017 stage 2, ownership-soundness plan
//! track 6.1). The `balance_verifier_detects_*` tests run the verifier on
//! CURRENTLY-BUGGY programs from the plan and assert it REPORTS the
//! imbalance — the verifier is built expecting red, and reproducing the
//! known bugs is its own validation. When the wave-1 fix streams land
//! each detect test flips to asserting ZERO reports for that shape once
//! the corresponding fix lands; the flip is noted per test. S1 flipped
//! 2026-07-11 (plan 1.1 merged); B8 flipped 2026-07-12 (wave-2 triage).

#[cfg(test)]
mod tests {
    use crate::compiling::driver::{Driver, DriverConfig, Source};
    use crate::lambda_g::balance::{BalanceOutcome, verify_balance};

    /// Compile a program string through the full pipeline and run the
    /// free-balance verifier over the lowered λ_G.
    fn balance_outcome(code: &str) -> BalanceOutcome {
        let driver = Driver::new(
            vec![Source::from(code)],
            DriverConfig::new("BalanceVerifierTest"),
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
            lowered.phase.diagnostics.is_empty(),
            "lowering: {:?}",
            lowered.phase.diagnostics
        );
        verify_balance(
            &lowered.phase.program,
            lowered.phase.main,
            &lowered.phase.entry_funcs,
        )
    }

    /// Reports whose unit is one of the program's own functions (as opposed
    /// to core library units, which have their own pre-existing findings).
    fn reports_in_unit<'a>(
        outcome: &'a BalanceOutcome,
        unit: &str,
    ) -> Vec<&'a crate::lambda_g::balance::BalanceReport> {
        outcome
            .reports
            .iter()
            .filter(|report| report.unit == unit || report.unit.starts_with(&format!("{unit}#")))
            .collect()
    }

    // ------------------------------------------------------------------
    // Known-bug detection (EXPECTED RED until the wave-1 fixes land)
    // ------------------------------------------------------------------

    #[test]
    fn balance_verifier_accepts_fixed_b8_literal_arm_shape() {
        // FLIPPED (was balance_verifier_detects_b8_taken_literal_arm_
        // scrutinee_leak; before that, written against plan finding B2):
        // the pattern compiler freed owned occurrences only for WILDCARD
        // cells, so the taken "ab" arm never freed the scrutinee. B8
        // landed (matched literal cells stay in the matrix as owned-
        // discard wildcards — lower/patterns.rs literal_column), so the
        // verifier now finds the shape balanced on every arm.
        let outcome = balance_outcome(
            "func g() -> String {\n\t\"a\" + \"b\"\n}\nfunc main() -> Int {\n\tlet a = match g() {\n\t\t\"ab\" -> return 1,\n\t\t_ -> 2\n\t}\n\ta\n}\nmain()",
        );
        let reports = reports_in_unit(&outcome, "main");
        assert!(
            reports.is_empty(),
            "expected zero reports in main (B8 is fixed; the taken literal arm frees the scrutinee); got:\n{}",
            outcome.render()
        );
    }

    #[test]
    fn balance_verifier_accepts_fixed_s1_deinit_shape() {
        // FLIPPED (was balance_verifier_detects_s1_deinit_double_free):
        // written against plan finding S1 — the deinit body's scope-exit
        // drop of `self` fell through the recursion guard into structural
        // teardown, duplicating the caller-side glue. Plan 1.1 landed
        // (DropBinding::is_deinit_self elaborates the body's self drop to
        // a no-op; the guard is deleted), so the verifier now finds the
        // shape balanced — glue frees each field exactly once.
        let outcome = balance_outcome(
            "struct Loud {\n\tlet s: String\n}\nextend Loud: Deinit {\n\tconsuming func deinit() -> Void {\n\t\tprint(\"bye\")\n\t}\n}\nfunc main() -> Int {\n\tlet l = Loud(s: \"a\" + \"b\")\n\t1\n}\nmain()",
        );
        let reports = reports_in_unit(&outcome, "main");
        assert!(
            reports.is_empty(),
            "expected zero reports in main (S1 is fixed; glue frees fields exactly once); got:\n{}",
            outcome.render()
        );
    }

    // ------------------------------------------------------------------
    // Balanced programs: zero reports (false-positive fence). These stay
    // green forever.
    // ------------------------------------------------------------------

    #[test]
    fn balance_verifier_accepts_balanced_let_drop() {
        // A heap String local, dropped at scope exit: one alloc path, one
        // free, every exit balanced.
        let outcome = balance_outcome(
            "func main() -> Int {\n\tlet s = \"a\" + \"b\"\n\ts.byte_count\n}\nmain()",
        );
        assert!(
            reports_in_unit(&outcome, "main").is_empty(),
            "balanced let-drop must produce no reports in main; got:\n{}",
            outcome.render()
        );
        assert!(outcome.analyzed > 0, "verifier analyzed nothing");
    }

    #[test]
    fn balance_verifier_accepts_balanced_branch() {
        // The droppable local is freed once after the branches join; both
        // exit paths agree.
        let outcome = balance_outcome(
            "func main() -> Int {\n\tlet s = \"a\" + \"b\"\n\tlet r = if s.byte_count == 2 { 1 } else { 2 }\n\tr\n}\nmain()",
        );
        assert!(
            reports_in_unit(&outcome, "main").is_empty(),
            "balanced branch must produce no reports in main; got:\n{}",
            outcome.render()
        );
    }

    #[test]
    fn balance_verifier_accepts_balanced_loop_with_droppable_local() {
        // A droppable local allocated and freed once per iteration: the
        // loop-carried facts widen but stay balanced.
        let outcome = balance_outcome(
            "func main() -> Int {\n\tlet i = 0\n\tloop i < 3 {\n\t\tlet s = \"a\" + \"b\"\n\t\tprint(s.byte_count)\n\t\ti = i + 1\n\t}\n\ti\n}\nmain()",
        );
        assert!(
            reports_in_unit(&outcome, "main").is_empty(),
            "balanced loop must produce no reports in main; got:\n{}",
            outcome.render()
        );
    }

    #[test]
    fn balance_verifier_accepts_flag_guarded_partial_move() {
        // `let name = person.name` moves one field out and clears its drop
        // flag (cell_set false) BEFORE the scope-exit branch reads it. The
        // verifier tracks constant-bool cells and prunes flag-infeasible
        // branch edges — without that, the impossible flag=true path
        // re-frees the moved field after its unconditional binder-side
        // free (a phantom DoubleFree) and the impossible flag=false exit
        // never frees the sibling (a phantom Leak). Found by the 6.1
        // enablement sweep on `open_field_move_drop_uses_field_drop_flag`.
        let outcome = balance_outcome(
            "struct Person {\n\tlet name: String\n\tlet title: String\n\tlet age: Int\n}\nfunc f() -> Int {\n\tlet person = Person(name: \"Pat\" + \"\", title: \"Dr\" + \"\", age: 41)\n\tlet name = person.name\n\tname.byte_count + person.title.byte_count + person.age\n}\nf()",
        );
        let reports = reports_in_unit(&outcome, "f");
        assert!(
            reports.is_empty(),
            "flag-guarded partial move must produce no reports in f; got:\n{}",
            outcome.render()
        );
    }

    #[test]
    fn balance_verifier_counts_skips_loudly() {
        // Effect-handler bodies are out of v1 scope: the handler lowers to
        // its own escaping chunk whose body delivers a value into another
        // unit's continuation, and that unit must land on the counted skip
        // list (never silently ignored). The performing function and the
        // installing scope still analyze.
        let outcome = balance_outcome(
            "effect 'oops(error) -> Never\n@handle 'oops { err in print(err) }\nfunc boom() 'oops -> () {\n\t'oops(\"bang\")\n}\nboom()",
        );
        assert!(
            outcome
                .skipped
                .iter()
                .any(|(unit, _)| unit == "handler" || unit.starts_with("handler#")),
            "the handler-body unit must be skipped loudly; got:\n{}",
            outcome.render()
        );
    }
}
