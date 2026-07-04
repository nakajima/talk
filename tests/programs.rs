//! The real-program corpus (A2 of docs/confidence-and-core-plan.md):
//! small, idiomatic, complete programs, each checked and run on BOTH
//! engines — any stdout divergence is a bug (differential testing,
//! McKeeman 1998) — under the allocation-balance policy of A1.

use talk::compiling::driver::{Driver, DriverConfig, Lowered, Source};

/// Programs whose containers leak buffers today — the corpus slice of the
/// Track B fence. B2 empties this list.
const EXPECTS_CONTAINER_ELEMENT_LEAK: &[&str] = &[
    "iterate_and_match",
    "string_building",
    "conditional_moves",
    "handlers",
    "graphemes",
    "caller_locals_handler",
    "multi_effect_handlers",
];

fn run_program(name: &str) {
    let path = std::path::PathBuf::from(format!("tests/programs/{name}.tlk"));
    let driver = Driver::new(vec![Source::from(path)], DriverConfig::new("Corpus"));
    let typed = driver
        .parse()
        .expect("parse")
        .resolve_names()
        .expect("resolve")
        .type_check();
    assert!(
        !typed.has_errors(),
        "{name}: type/flow errors: {:?}",
        typed.diagnostics()
    );
    let mut lowered: Driver<Lowered> = typed.lower();
    assert!(
        lowered.phase.diagnostics.is_empty(),
        "{name}: lowering: {:?}",
        lowered.phase.diagnostics
    );
    let verified = lowered.phase.program.verify();
    assert!(verified.is_ok(), "{name}: verifier: {:?}", verified.err());

    let (_, vm_out) = lowered.run_vm_with_output().expect("vm");
    let (_, evaluator_out) = if EXPECTS_CONTAINER_ELEMENT_LEAK.contains(&name) {
        lowered
            .eval_expecting_container_element_leak()
            .expect("evaluator")
    } else {
        lowered.eval_with_output().expect("evaluator")
    };
    assert_eq!(evaluator_out, vm_out, "{name}: stdout diverged");
    assert!(!vm_out.is_empty(), "{name}: corpus programs print evidence");
}

#[test]
fn iterate_and_match() {
    run_program("iterate_and_match");
}

#[test]
fn string_building() {
    run_program("string_building");
}

#[test]
fn conditional_moves() {
    run_program("conditional_moves");
}

#[test]
fn handlers() {
    run_program("handlers");
}

#[test]
fn heap_graph() {
    run_program("heap_graph");
}

#[test]
fn graphemes() {
    run_program("graphemes");
}

#[test]
fn caller_locals_handler() {
    // The handler body captures a caller local: the capability is a real
    // closure over the installing frame, passed down to the performer.
    run_program("caller_locals_handler");
}

#[test]
fn nested_handlers() {
    // Two frames in a call chain each install a handler for the same
    // effect: the nearest dynamic extent wins.
    run_program("nested_handlers");
}

#[test]
fn resume_across_frames() {
    // A resuming handler in a caller: the callee's performs resume with
    // the handler's value, twice, across the call boundary.
    run_program("resume_across_frames");
}

#[test]
fn multi_effect_handlers() {
    // One function performs two effects (one resuming, one aborting),
    // both handled by its caller — two capabilities threaded per call.
    run_program("multi_effect_handlers");
}

#[test]
fn generic_state() {
    // A generic effect performed in an unannotated callee under a caller
    // handler: the capability materializes from the handler template at
    // Int (docs/generic-effects-plan.md).
    run_program("generic_state");
}

#[test]
fn generic_two_instantiations() {
    // One handler covers several instantiations in one extent — a
    // generic function specialized at Int AND Bool, plus a direct
    // perform — each with its own materialized capability.
    run_program("generic_two_instantiations");
}

#[test]
fn effectful_closures() {
    // Function values carry capabilities from their creation site
    // (lexical capture, ADR 0011): a literal performing under a handler
    // works through a HOF, and a named effectful function taken as a
    // value eta-expands over the capabilities in scope.
    run_program("effectful_closures");
}

/// Every `.tlk` in the corpus directory has a test — a new program without
/// one fails here instead of silently going unexercised.
#[test]
fn every_corpus_program_is_exercised() {
    let known = [
        "iterate_and_match",
        "string_building",
        "conditional_moves",
        "handlers",
        "heap_graph",
        "graphemes",
        "caller_locals_handler",
        "nested_handlers",
        "resume_across_frames",
        "multi_effect_handlers",
        "effectful_closures",
        "generic_state",
        "generic_two_instantiations",
    ];
    for entry in std::fs::read_dir("tests/programs").expect("corpus dir") {
        let path = entry.expect("entry").path();
        if path.extension().is_some_and(|ext| ext == "tlk") {
            let stem = path.file_stem().expect("stem").to_string_lossy();
            assert!(
                known.contains(&stem.as_ref()),
                "corpus program {stem}.tlk has no test"
            );
        }
    }
}
