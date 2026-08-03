//! Explicit bootstrap regeneration (ADR 0043 §3): compile a source set
//! into a service artifact TWICE with fresh pipelines, require the two
//! images byte-identical (the fixed-point check), and produce the
//! artifact together with its manifest so neither can go stale alone.
//!
//! This is a true bootstrap (ADR 0043 Stage 5): stage 1 parses with
//! the embedded artifact and stage 2 parses with the stage-1 candidate
//! whenever the artifact exposes the parser surface, so the fixed
//! point proves the candidate parses its own sources identically. A
//! non-parser service set has no such fixed point; its stage 2 checks
//! deterministic recompilation.

use crate::compiling::driver::{Driver, DriverConfig, OptimizationStats, Source};
use crate::compiling::manifest::ArtifactManifest;

pub struct BootstrapOutcome {
    pub image: Vec<u8>,
    pub manifest: ArtifactManifest,
    /// The ABI descriptor (ADR 0043 §5), when the service declares a
    /// schema root.
    pub abi: Option<String>,
    /// Optimization rewrites performed by each side of the fixed point.
    pub stage_optimizations: [OptimizationStats; 2],
}

struct CompiledStage {
    image: Vec<u8>,
    abi: Option<String>,
    optimizations: OptimizationStats,
}

/// One compile of the source set to an encoded service image, plus the
/// ABI descriptor and optimization counts.
fn compile_stage(
    sources: &[(String, String)],
    exports: &[String],
    allowed_effects: &[String],
    schema_root: Option<&str>,
    parser: Option<&std::sync::Arc<crate::compiling::frontend::ParserSession>>,
) -> Result<CompiledStage, String> {
    crate::profile::init();
    profiling::scope!("bootstrap.compile_stage");
    let inputs: Vec<Source> = sources
        .iter()
        .map(|(name, text)| Source::in_memory(name.into(), text.clone()))
        .collect();
    let mut config = DriverConfig::new("Bootstrap");
    config.parser = parser.cloned();
    let parsed = Driver::new(inputs, config)
        .parse()
        .map_err(|error| format!("bootstrap parse failed: {error:?}"))?;
    let resolved = parsed
        .resolve_names()
        .map_err(|errors| format!("bootstrap name resolution failed: {errors:?}"))?;
    let typed = resolved.type_check();
    if typed.has_errors() {
        let messages: Vec<String> = typed
            .diagnostics()
            .iter()
            .map(|diagnostic| diagnostic.to_string())
            .collect();
        return Err(format!(
            "bootstrap type check failed:\n{}",
            messages.join("\n")
        ));
    }
    let abi = {
        profiling::scope!("bootstrap.describe_abi");
        schema_root
            .map(|root| crate::compiling::abi::describe(&typed.phase.program, root))
            .transpose()?
    };
    let output = {
        profiling::scope!("bootstrap.compile_service");
        typed.compile_mir(crate::compiling::driver::MirEntry::Exports {
            names: exports,
            allowed_effects,
        })?
    };
    let optimizations = output.optimizations.clone();
    let image = {
        profiling::scope!("bootstrap.encode");
        talk_bytecode::compile(&output.module)
            .map_err(|error| error.message().to_string())?
            .encode_bytecode()
            .map_err(|error| format!("bootstrap encode failed: {error:?}"))?
    };
    Ok(CompiledStage {
        image,
        abi,
        optimizations,
    })
}

/// Regenerate the artifact, manifest, and ABI descriptor for a source
/// set. The source list is `(name, content)` pairs; names participate
/// in the digest, so renames invalidate the manifest exactly like
/// edits.
pub fn bootstrap(
    sources: &[(String, String)],
    exports: &[String],
    allowed_effects: &[String],
    schema_root: Option<&str>,
) -> Result<BootstrapOutcome, String> {
    crate::profile::init();
    profiling::scope!("bootstrap");
    let stage1 = {
        profiling::scope!("bootstrap.stage_1");
        compile_stage(sources, exports, allowed_effects, schema_root, None)?
    };
    // The self-hosting fixed point (ADR 0043 §3): when the artifact IS
    // a parser — it exposes the parse surface and carries a descriptor
    // — stage 2 parses the source set with the stage-1 candidate, so a
    // candidate that cannot rebuild itself fails here rather than on
    // the next regeneration. Core and stdlib still arrive through the
    // process-wide cached artifacts in both stages; the fixed point is
    // over the sources being bootstrapped. A non-parser service has no
    // such fixed point to prove, and stage 2 checks deterministic
    // recompilation instead.
    let candidate = match &stage1.abi {
        Some(abi) => {
            let session =
                crate::compiling::frontend::ParserSession::from_artifact(&stage1.image, abi)?;
            session
                .exports_parser()
                .then(|| std::sync::Arc::new(session))
        }
        None => None,
    };
    let stage2 = {
        profiling::scope!("bootstrap.stage_2");
        compile_stage(
            sources,
            exports,
            allowed_effects,
            schema_root,
            candidate.as_ref(),
        )?
    };
    if stage1.image != stage2.image || stage1.abi != stage2.abi {
        return Err(
            "bootstrap did not reach a fixed point: stage-1 and stage-2 artifacts differ".into(),
        );
    }
    let manifest = ArtifactManifest::compute(sources, &stage1.image, stage1.abi.as_deref());
    Ok(BootstrapOutcome {
        image: stage1.image,
        manifest,
        abi: stage1.abi,
        stage_optimizations: [stage1.optimizations, stage2.optimizations],
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use talk_vm::interp::{Budgets, HostValue, Value};
    use talk_vm::io::CaptureIO;

    fn frontendish_sources() -> Vec<(String, String)> {
        vec![(
            "Svc.tlk".into(),
            "pub func double(n: Int) -> Int { n * 2 }\n\npub func shout(text: String) -> String { text + \"!\" }\n"
                .into(),
        )]
    }

    // Stage 2's parsing must actually route through the supplied
    // candidate session: a session whose descriptor names the wrong
    // root fails the parse bridge, where the shared embedded session
    // would have succeeded.
    #[test]
    fn stage_two_routes_parsing_through_the_supplied_session() {
        let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"));
        let image = std::fs::read(root.join("bootstrap/frontend.tbc"))
            .expect("checked-in artifact");
        let abi = std::fs::read_to_string(root.join("bootstrap/frontend.abi"))
            .expect("checked-in descriptor");
        // The optional identity is checked on every Optional crossing;
        // pointing it at the wrong symbol fails the very first adapt.
        let poisoned = abi.replace("optional: enum:1.1", "optional: enum:1.2");
        assert_ne!(poisoned, abi, "the descriptor names the optional enum");
        let session = crate::compiling::frontend::ParserSession::from_artifact(
            &image, &poisoned,
        )
        .expect("candidate session builds");
        assert!(session.exports_parser());
        let sources = frontendish_sources();
        let error = match compile_stage(
            &sources,
            &["double".into()],
            &["alloc".into()],
            None,
            Some(&std::sync::Arc::new(session)),
        ) {
            Err(error) => error,
            Ok(_) => panic!("a poisoned candidate schema must fail the parse"),
        };
        assert!(
            error.contains("parse"),
            "the failure should come from parsing: {error}"
        );
        compile_stage(&sources, &["double".into()], &["alloc".into()], None, None)
            .expect("the shared session parses the same sources");
    }

    #[test]
    fn bootstrap_produces_a_verified_runnable_artifact() {
        let sources = frontendish_sources();
        let outcome = bootstrap(
            &sources,
            &["double".into(), "shout".into()],
            &["alloc".into()],
            None,
        )
        .expect("bootstrap succeeds");

        outcome
            .manifest
            .verify(&sources, &outcome.image, None)
            .expect("manifest verifies its own output");
        assert_eq!(
            outcome.stage_optimizations[0].passes.len(),
            8,
            "compiler passes only; the bytecode adapter reports its own fusion count"
        );
        assert_eq!(
            outcome.stage_optimizations[0],
            outcome.stage_optimizations[1],
            "fixed-point stages should perform the same rewrites"
        );

        let module = talk_vm::Module::decode_bytecode(&outcome.image).expect("image decodes");
        let mut io = CaptureIO::default();
        let result = talk_vm::interp::run_export(
            &module,
            "double",
            &[HostValue::Int(21)],
            crate::backend::string_shape(),
            Budgets::default(),
            &mut io,
        )
        .expect("artifact export runs");
        assert_eq!(result.value, Value::I64(42));
    }

    #[test]
    fn manifest_goes_stale_when_a_source_changes() {
        let sources = frontendish_sources();
        let outcome = bootstrap(&sources, &["double".into()], &[], None).expect("bootstrap succeeds");

        let mut edited = sources.clone();
        edited[0].1.push_str("\n// edited\n");
        let stale = outcome.manifest.verify(&edited, &outcome.image, None);
        assert!(
            stale.err().expect("edited source must fail").contains("sources"),
            "source edits must invalidate the manifest"
        );
    }

    /// Explicit codegen-staleness gate. Normal tests validate that the
    /// checked-in artifact is internally consistent and runnable, but compiler
    /// changes must not make `cargo test` depend on regenerating repository
    /// artifacts. CI and release workflows should use `talk bootstrap --check`.
    #[test]
    #[ignore = "explicit artifact gate; use `talk bootstrap --check`"]
    fn checked_in_frontend_artifacts_are_a_fixed_point() {
        let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"));
        let outcome = crate::compiling::frontend::regenerate(root).expect("frontend bootstraps");

        // The strong explicit staleness gate (ADR 0043 section 3): the artifact this
        // compiler regenerates from the current sources must be the checked-in
        // one, byte for byte. The default tests catch inconsistent checked-in
        // sources, bytes, and ABI; this opt-in gate also catches compiler
        // codegen drift.
        let checked_in = std::fs::read(crate::compiling::frontend::artifact_path(root)).expect(
            "bootstrap/frontend.tbc is missing; regenerate with `talk bootstrap`",
        );
        assert!(
            checked_in == outcome.image,
            "checked-in frontend artifact differs from a fresh bootstrap; regenerate with `talk bootstrap`"
        );
        let manifest_text = std::fs::read_to_string(crate::compiling::frontend::manifest_path(root))
            .expect("bootstrap/frontend.manifest is missing; regenerate with `talk bootstrap`");
        assert_eq!(
            manifest_text,
            outcome.manifest.to_text(),
            "checked-in frontend manifest is stale; regenerate with `talk bootstrap`"
        );
        let abi_text = std::fs::read_to_string(crate::compiling::frontend::abi_path(root))
            .expect("bootstrap/frontend.abi is missing; regenerate with `talk bootstrap`");
        assert_eq!(
            Some(abi_text),
            outcome.abi,
            "checked-in frontend ABI descriptor is stale; regenerate with `talk bootstrap`"
        );
    }

    #[test]
    fn bootstrap_surfaces_compile_errors() {
        let broken = vec![("Svc.tlk".into(), "pub func broken(".into())];
        let error = bootstrap(&broken, &["broken".into()], &[], None)
            .err()
            .expect("broken source must fail");
        assert!(error.contains("parse failed"), "{error}");

        // Effects with declared rows propagate to the export's scheme
        // and are denied. KNOWN GAP (recorded in memory + ADR notes):
        // an effect reaching the export only through protocol dispatch
        // (e.g. 'alloc via String's `+`) vanishes into the generalized
        // row tail and is NOT denied — the restrictive host IO impl is
        // the runtime backstop for those.
        let effectful = vec![(
            "Svc.tlk".into(),
            "pub func nap() -> Int { sleep(ms: 0) }\n".into(),
        )];
        let denied = bootstrap(&effectful, &["nap".into()], &[], None)
            .err()
            .expect("denied effect must fail");
        assert!(denied.contains("'io"), "{denied}");
    }
}
