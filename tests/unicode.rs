//! Unicode conformance: the official GraphemeBreakTest cases (generated
//! into a self-checking talk program by `cargo run --bin gen_unicode`)
//! asserting zero failures. The program prints one line per failing case
//! and a final `failures: 0 / N` summary.
//!
//! VM only, deliberately: the reference evaluator executes calls by term
//! substitution (~100x the VM), which puts this CPU-bound program at
//! 10-20+ minutes. The evaluator still covers the same decode, category,
//! and boundary code differentially through `tests/programs/graphemes.tlk`
//! and the vm_tests unit corpus.

use talk::compiling::driver::{Driver, DriverConfig, Lowered, Source};

#[test]
fn grapheme_break_conformance() {
    let path = std::path::PathBuf::from("tests/unicode/grapheme_conformance.tlk");
    let driver = Driver::new(vec![Source::from(path)], DriverConfig::new("Unicode"));
    let typed = driver
        .parse()
        .expect("parse")
        .resolve_names()
        .expect("resolve")
        .type_check();
    assert!(
        !typed.has_errors(),
        "type/flow errors: {:?}",
        typed.diagnostics()
    );
    let mut lowered: Driver<Lowered> = typed.lower();
    assert!(
        lowered.phase.diagnostics.is_empty(),
        "lowering: {:?}",
        lowered.phase.diagnostics
    );
    let verified = lowered.phase.program.verify();
    assert!(verified.is_ok(), "verifier: {:?}", verified.err());

    let (_, vm_out) = lowered.run_vm_with_output().expect("vm");
    assert!(
        vm_out.starts_with("failures: 0 / "),
        "conformance failures:\n{vm_out}"
    );
}
