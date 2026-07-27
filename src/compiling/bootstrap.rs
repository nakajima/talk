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
    /// The ABI descriptor (ADR 0043 §5), when the service declares a
    /// schema root.
    pub abi: Option<String>,
}

/// One compile of the source set to an encoded service image, plus the
/// ABI descriptor when a schema root is named.
fn compile_stage(
    sources: &[(String, String)],
    exports: &[String],
    allowed_effects: &[String],
    schema_root: Option<&str>,
) -> Result<(Vec<u8>, Option<String>), String> {
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
    let abi = schema_root
        .map(|root| crate::compiling::abi::describe(&typed.phase.program, root))
        .transpose()?;
    let executable = typed.compile_service(exports, allowed_effects)?;
    let image = executable
        .encode_bytecode()
        .map_err(|error| format!("bootstrap encode failed: {error:?}"))?;
    Ok((image, abi))
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
    let (stage1, abi1) = compile_stage(sources, exports, allowed_effects, schema_root)?;
    let (stage2, abi2) = compile_stage(sources, exports, allowed_effects, schema_root)?;
    if stage1 != stage2 || abi1 != abi2 {
        return Err(
            "bootstrap did not reach a fixed point: stage-1 and stage-2 artifacts differ".into(),
        );
    }
    let manifest = ArtifactManifest::compute(sources, &stage1, abi1.as_deref());
    Ok(BootstrapOutcome {
        image: stage1,
        manifest,
        abi: abi1,
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
            None,
        )
        .expect("bootstrap succeeds");

        outcome
            .manifest
            .verify(&sources, &outcome.image, None)
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
        let outcome = bootstrap(&sources, &["double".into()], &[], None).expect("bootstrap succeeds");

        let mut edited = sources.clone();
        edited[0].1.push_str("\n// edited\n");
        let stale = outcome.manifest.verify(&edited, &outcome.image, None);
        assert!(
            stale.err().expect("edited source must fail").contains("sources"),
            "source edits must invalidate the manifest"
        );
    }

    /// Run a `String -> String` validation export from the frontend
    /// image and return its output.
    fn run_string_export(module: &talk_runtime::Module, name: &str, source: &str) -> String {
        let mut io = CaptureIO::default();
        let run = talk_runtime::interp::run_export(
            module,
            name,
            &[HostValue::String(source.as_bytes().to_vec())],
            crate::backend::string_shape(),
            Budgets::default(),
            &mut io,
        )
        .unwrap_or_else(|error| panic!("{name} failed: {error}"));
        String::from_utf8(
            run.string_bytes(&run.value)
                .unwrap_or_else(|_| panic!("{name} returns a string"))
                .to_vec(),
        )
        .unwrap_or_else(|error| panic!("{name} output is UTF-8: {error}"))
    }

    /// The stage-2 differential harness (ADR 0043): each self-hosted
    /// validation export must reproduce the Rust frontend's dump format
    /// byte-for-byte. The lexer exports (`lex`, `trees`) cover the whole
    /// corpus; the parser exports cover the directories listed per
    /// category and grow as the Talk parser's surface grows.
    #[test]
    fn talk_frontend_matches_rust_frontend_on_covered_corpus() {
        let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"));
        let outcome = crate::compiling::frontend::regenerate(root).expect("frontend bootstraps");
        let module = talk_runtime::Module::decode_bytecode(&outcome.image).expect("image decodes");

        let mut covered: Vec<std::path::PathBuf> = Vec::new();
        for dir in [
            "tests/parser",
            "tests/parser/expr",
            "tests/parser/pattern",
            "tests/parser/type",
            "tests/parser/block",
            "tests/parser/tokentree",
            "tests/parser/lenient",
            "tests/parser/unicode",
            "core",
            "stdlib",
            "tests/examples",
            "examples",
        ] {
            for entry in std::fs::read_dir(root.join(dir)).expect("corpus dir") {
                let path = entry.expect("corpus entry").path();
                if path.extension().is_some_and(|ext| ext == "tlk") {
                    covered.push(path);
                }
            }
        }
        covered.sort();
        for path in covered {
            let path = path.display().to_string();
            let source = std::fs::read_to_string(&path).expect("read corpus source");
            let talk_tokens = run_string_export(&module, "lex", &source);
            let rust_tokens = crate::parsing::dump::dump_tokens(&source);
            assert_eq!(talk_tokens, rust_tokens, "token divergence on {path}");

            let talk_trees = run_string_export(&module, "trees", &source);
            let rust_trees = crate::parsing::dump::dump_token_trees(&source);
            assert_eq!(talk_trees, rust_trees, "tree divergence on {path}");
        }

        let parse_categories: [(&str, &str, fn(&str) -> String); 9] = [
            ("tests/parser", "parse", crate::parsing::dump::dump),
            ("tests/parser/unicode", "parse", crate::parsing::dump::dump),
            ("core", "parse", crate::parsing::dump::dump),
            ("stdlib", "parse", crate::parsing::dump::dump),
            (
                "tests/parser/lenient",
                "parse_lenient",
                crate::parsing::dump::dump_lenient,
            ),
            (
                "tests/parser/block",
                "parse_block_items",
                crate::parsing::dump::dump_block_items,
            ),
            ("tests/parser/expr", "parse_expr", crate::parsing::dump::dump_expr),
            (
                "tests/parser/pattern",
                "parse_pattern",
                crate::parsing::dump::dump_pattern,
            ),
            ("tests/parser/type", "parse_type", crate::parsing::dump::dump_type),
        ];
        for (dir, export, rust_dump) in parse_categories {
            let mut fixtures: Vec<std::path::PathBuf> = std::fs::read_dir(root.join(dir))
                .expect("parse corpus dir")
                .filter_map(|entry| entry.ok())
                .map(|entry| entry.path())
                .filter(|path| path.extension().is_some_and(|ext| ext == "tlk"))
                .collect();
            fixtures.sort();
            for path in fixtures {
                let path = path.display().to_string();
                let source = std::fs::read_to_string(&path).expect("read corpus source");
                let talk_dump = run_string_export(&module, export, &source);
                assert_eq!(
                    talk_dump,
                    rust_dump(&source),
                    "parse divergence on {path}"
                );
            }
        }

        // The strong staleness gate (ADR 0043 §3): the artifact this
        // compiler regenerates from the current sources must be the
        // checked-in one, byte for byte. The digest-only gate in
        // compiling::frontend catches source edits cheaply; this one
        // also catches compiler codegen drift.
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
