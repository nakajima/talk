//! Explicit bootstrap regeneration (ADR 0043 §3): compile a source set
//! into a service artifact TWICE with fresh pipelines, require the two
//! images byte-identical (the fixed-point check), and produce the
//! artifact together with its manifest so neither can go stale alone.
//!
//! Today both stages compile with the same (Rust) frontend, so the
//! fixed point is a determinism guarantee. Once the self-hosted
//! frontend drives parsing, the same sequence becomes the true
//! bootstrap: stage 1 parses with the checked-in artifact, stage 2
//! with the candidate — the check's meaning strengthens without the
//! command changing shape.

use crate::compiling::driver::{Driver, DriverConfig, Source};
use crate::compiling::manifest::ArtifactManifest;

pub struct BootstrapOutcome {
    pub image: Vec<u8>,
    pub manifest: ArtifactManifest,
}

/// One compile of the source set to an encoded service image.
fn compile_stage(
    sources: &[(String, String)],
    exports: &[String],
    allowed_effects: &[String],
) -> Result<Vec<u8>, String> {
    let inputs: Vec<Source> = sources
        .iter()
        .map(|(name, text)| Source::in_memory(name.into(), text.clone()))
        .collect();
    let parsed = Driver::new(inputs, DriverConfig::new("Bootstrap"))
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
    let executable = typed.compile_service(exports, allowed_effects)?;
    executable
        .encode_bytecode()
        .map_err(|error| format!("bootstrap encode failed: {error:?}"))
}

/// Regenerate the artifact and manifest for a source set. The source
/// list is `(name, content)` pairs; names participate in the digest,
/// so renames invalidate the manifest exactly like edits.
pub fn bootstrap(
    sources: &[(String, String)],
    exports: &[String],
    allowed_effects: &[String],
) -> Result<BootstrapOutcome, String> {
    let stage1 = compile_stage(sources, exports, allowed_effects)?;
    let stage2 = compile_stage(sources, exports, allowed_effects)?;
    if stage1 != stage2 {
        return Err(
            "bootstrap did not reach a fixed point: stage-1 and stage-2 artifacts differ".into(),
        );
    }
    let manifest = ArtifactManifest::compute(sources, &stage1);
    Ok(BootstrapOutcome {
        image: stage1,
        manifest,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use talk_runtime::interp::{Budgets, HostValue, Value};
    use talk_runtime::io::CaptureIO;

    fn frontendish_sources() -> Vec<(String, String)> {
        vec![(
            "Svc.tlk".into(),
            "pub func double(n: Int) -> Int { n * 2 }\n\npub func shout(text: String) -> String { text + \"!\" }\n"
                .into(),
        )]
    }

    #[test]
    fn bootstrap_produces_a_verified_runnable_artifact() {
        let sources = frontendish_sources();
        let outcome = bootstrap(
            &sources,
            &["double".into(), "shout".into()],
            &["alloc".into()],
        )
        .expect("bootstrap succeeds");

        outcome
            .manifest
            .verify(&sources, &outcome.image)
            .expect("manifest verifies its own output");

        let module = talk_runtime::Module::decode_bytecode(&outcome.image).expect("image decodes");
        let mut io = CaptureIO::default();
        let result = talk_runtime::interp::run_export(
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
        let outcome = bootstrap(&sources, &["double".into()], &[]).expect("bootstrap succeeds");

        let mut edited = sources.clone();
        edited[0].1.push_str("\n// edited\n");
        let stale = outcome.manifest.verify(&edited, &outcome.image);
        assert!(
            stale.err().expect("edited source must fail").contains("sources"),
            "source edits must invalidate the manifest"
        );
    }

    /// The stage-2 differential harness (ADR 0043): the self-hosted
    /// lexer's `lex` validation export must reproduce the Rust lexer's
    /// dump-format token section byte-for-byte. The covered list grows
    /// file-by-file as the Talk lexer's surface grows.
    #[test]
    fn talk_lexer_matches_rust_lexer_on_covered_corpus() {
        let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"));
        let frontend_dir = root.join("frontend");
        let mut names: Vec<_> = std::fs::read_dir(&frontend_dir)
            .expect("frontend/ exists")
            .filter_map(|entry| entry.ok())
            .map(|entry| entry.path())
            .filter(|path| path.extension().is_some_and(|ext| ext == "tlk"))
            .collect();
        names.sort();
        let sources: Vec<(String, String)> = names
            .iter()
            .map(|path| {
                (
                    path.file_name().expect("name").to_string_lossy().into_owned(),
                    std::fs::read_to_string(path).expect("read frontend source"),
                )
            })
            .collect();

        let outcome = bootstrap(
            &sources,
            &["lex".into()],
            &["alloc".into(), "panic".into()],
        )
        .expect("frontend bootstraps");
        let module = talk_runtime::Module::decode_bytecode(&outcome.image).expect("image decodes");

        let covered = ["tests/parser/literals.tlk", "tests/parser/comments.tlk"];
        for path in covered {
            let source = std::fs::read_to_string(root.join(path)).expect("read corpus source");
            let mut io = CaptureIO::default();
            let run = talk_runtime::interp::run_export(
                &module,
                "lex",
                &[HostValue::String(source.clone().into_bytes())],
                crate::backend::string_shape(),
                Budgets::default(),
                &mut io,
            )
            .unwrap_or_else(|error| panic!("lex({path}) failed: {error}"));
            let talk_tokens = String::from_utf8(
                run.string_bytes(&run.value)
                    .expect("lex returns a string")
                    .to_vec(),
            )
            .expect("lex output is UTF-8");
            let rust_tokens = crate::parsing::dump::dump_tokens(&source);
            assert_eq!(talk_tokens, rust_tokens, "token divergence on {path}");
        }
    }

    #[test]
    fn bootstrap_surfaces_compile_errors() {
        let broken = vec![("Svc.tlk".into(), "pub func broken(".into())];
        let error = bootstrap(&broken, &["broken".into()], &[])
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
        let denied = bootstrap(&effectful, &["nap".into()], &[])
            .err()
            .expect("denied effect must fail");
        assert!(denied.contains("'io"), "{denied}");
    }
}
