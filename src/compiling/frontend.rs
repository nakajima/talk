//! The self-hosted frontend's bootstrap profile (ADR 0043 §2–3): the
//! one owner of the frontend source set, service exports, allowed
//! effects, and checked-in artifact paths. The CLI's bare
//! `talk bootstrap` regenerates through this profile, the differential
//! harness compiles the same sources through it, and the compiler
//! loads the checked-in artifact through it — so none of them can
//! drift on what the frontend artifact is.

use crate::compiling::bootstrap::{bootstrap, BootstrapOutcome};
use crate::compiling::manifest::ArtifactManifest;
use std::path::{Path, PathBuf};

/// The frontend service exports (ADR 0043 §4): the category parse
/// operations, plus the lexer surfaces the differential harness
/// validates during migration. `parse_file_source` is the structured
/// result op — it returns the `ParseOutcome` value the ABI descriptor
/// describes, where the `parse` dump ops return rendered text.
pub const EXPORTS: [&str; 10] = [
    "lex",
    "trees",
    "parse",
    "parse_file_source",
    "parse_lenient",
    "parse_block_items",
    "parse_expr",
    "parse_pattern",
    "parse_type",
    "lex_tokens",
];

/// Effects the frontend may perform (ADR 0043 §7): deterministic
/// allocation and structured failure only — no IO, clock, or host
/// access.
pub const ALLOWED_EFFECTS: [&str; 2] = ["alloc", "panic"];

/// The root of the parse-result schema the ABI descriptor is generated
/// from (ADR 0043 §5).
pub const SCHEMA_ROOT: &str = "ParseOutcome";

pub fn source_dir(root: &Path) -> PathBuf {
    root.join("stdlib").join("syntax")
}

pub fn artifact_path(root: &Path) -> PathBuf {
    root.join("bootstrap").join("frontend.tbc")
}

pub fn manifest_path(root: &Path) -> PathBuf {
    root.join("bootstrap").join("frontend.manifest")
}

pub fn abi_path(root: &Path) -> PathBuf {
    root.join("bootstrap").join("frontend.abi")
}

/// The canonical frontend source set: every `.tlk` file in `stdlib/syntax/`,
/// sorted by name. Names participate in the manifest digest, so renames
/// invalidate the artifact exactly like edits.
pub fn sources(root: &Path) -> Result<Vec<(String, String)>, String> {
    let dir = source_dir(root);
    let mut paths: Vec<PathBuf> = std::fs::read_dir(&dir)
        .map_err(|err| format!("failed to read {}: {err}", dir.display()))?
        .filter_map(|entry| entry.ok())
        .map(|entry| entry.path())
        .filter(|path| path.extension().is_some_and(|ext| ext == "tlk"))
        .collect();
    paths.sort();
    if paths.is_empty() {
        return Err(format!("{} contains no .tlk sources", dir.display()));
    }
    let mut sources = Vec::new();
    for path in paths {
        let name = path
            .file_name()
            .map(|name| name.to_string_lossy().into_owned())
            .unwrap_or_default();
        let text = std::fs::read_to_string(&path)
            .map_err(|err| format!("failed to read {}: {err}", path.display()))?;
        sources.push((name, text));
    }
    Ok(sources)
}

fn export_strings() -> Vec<String> {
    EXPORTS.iter().map(|name| (*name).to_string()).collect()
}

fn effect_strings() -> Vec<String> {
    ALLOWED_EFFECTS.iter().map(|name| (*name).to_string()).collect()
}

/// Rebuild the frontend artifact from the on-disk sources, requiring
/// the stage-1/stage-2 fixed point.
pub fn regenerate(root: &Path) -> Result<BootstrapOutcome, String> {
    bootstrap(
        &sources(root)?,
        &export_strings(),
        &effect_strings(),
        Some(SCHEMA_ROOT),
    )
}

/// Load and validate the checked-in frontend artifact: the manifest
/// must match the on-disk sources, the artifact bytes, the ABI
/// descriptor, and this compiler's bytecode format, and the image must
/// decode. Fails closed on any mismatch — there is no fallback parser.
pub fn load(root: &Path) -> Result<talk_runtime::Module, String> {
    let artifact = artifact_path(root);
    let image = std::fs::read(&artifact)
        .map_err(|err| format!("failed to read {}: {err}", artifact.display()))?;
    let manifest_file = manifest_path(root);
    let manifest_text = std::fs::read_to_string(&manifest_file)
        .map_err(|err| format!("failed to read {}: {err}", manifest_file.display()))?;
    let abi_file = abi_path(root);
    let abi_text = std::fs::read_to_string(&abi_file)
        .map_err(|err| format!("failed to read {}: {err}", abi_file.display()))?;
    let manifest = ArtifactManifest::parse(&manifest_text)?;
    manifest.verify(&sources(root)?, &image, Some(&abi_text))?;
    talk_runtime::Module::decode_bytecode(&image)
        .map_err(|err| format!("frontend artifact failed to decode: {err:?}"))
}

/// The artifact triplet baked into this binary (ADR 0043 §2): the
/// compiler distribution IS the artifact — no filesystem needed at
/// runtime (wasm, installed binaries). `include_bytes!` tracks the
/// files, so a `talk bootstrap` regeneration reaches the binary on
/// the next cargo build.
const EMBEDDED_ARTIFACT: &[u8] = include_bytes!("../../bootstrap/frontend.tbc");
const EMBEDDED_MANIFEST: &str = include_str!("../../bootstrap/frontend.manifest");
pub(crate) const EMBEDDED_ABI: &str = include_str!("../../bootstrap/frontend.abi");

/// Load the embedded artifact: the manifest must tie the baked bytes,
/// the descriptor, and the bytecode format together. Deliberately no
/// disk-source comparison: the session parses ARBITRARY text with the
/// checked-in artifact — including edited frontend sources, which is
/// bootstrap's stage 0. Staleness between disk sources and checked-in
/// artifacts is the harness gates' job
/// (`checked_in_frontend_artifact_matches_sources` and the bootstrap
/// fixed point). Fails closed; there is no fallback parser.
fn load_embedded() -> Result<talk_runtime::Module, String> {
    crate::profile::init();
    profiling::scope!("frontend.load_embedded");
    let manifest = ArtifactManifest::parse(EMBEDDED_MANIFEST)?;
    manifest.verify_artifact(EMBEDDED_ARTIFACT, Some(EMBEDDED_ABI))?;
    talk_runtime::Module::decode_bytecode(EMBEDDED_ARTIFACT)
        .map_err(|err| format!("frontend artifact failed to decode: {err:?}"))
}

/// The immutable frontend program and ABI shared by every compiler thread.
struct FrontendSession {
    module: talk_runtime::Module,
    schema: crate::compiling::abi::AbiSchema,
}

impl FrontendSession {
    fn shared() -> Result<&'static Self, String> {
        static SESSION: std::sync::OnceLock<Result<FrontendSession, String>> =
            std::sync::OnceLock::new();
        SESSION
            .get_or_init(|| {
                profiling::scope!("frontend.initialize_session");
                Ok(Self {
                    module: load_embedded()?,
                    schema: crate::compiling::abi::parse_schema(EMBEDDED_ABI)?,
                })
            })
            .as_ref()
            .map_err(Clone::clone)
    }
}

/// An explicit parser session over a candidate artifact. Bootstrap
/// stage 2 parses with the stage-1 image (ADR 0043 §3): the fixed
/// point must prove the candidate parses its own sources, not that the
/// embedded artifact parses them twice.
pub struct ParserSession(FrontendSession);

impl ParserSession {
    /// Fail-closed: the image must decode and the descriptor parse.
    pub fn from_artifact(image: &[u8], abi: &str) -> Result<Self, String> {
        Ok(Self(FrontendSession {
            module: talk_runtime::Module::decode_bytecode(image)
                .map_err(|err| format!("candidate artifact failed to decode: {err:?}"))?,
            schema: crate::compiling::abi::parse_schema(abi)?,
        }))
    }

    /// Whether the artifact exposes the parser surface at all — a
    /// non-parser service bootstrap has no self-hosting fixed point to
    /// prove.
    pub fn exports_parser(&self) -> bool {
        self.0
            .module
            .exports
            .iter()
            .any(|(name, _)| name == "parse_file_source")
    }
}

fn resolve(session: Option<&ParserSession>) -> Result<&FrontendSession, String> {
    match session {
        Some(candidate) => Ok(&candidate.0),
        None => FrontendSession::shared(),
    }
}

/// Parse one source through the frontend artifact into the compiler's
/// own parse AST (ADR 0043 Stage 4): the strict whole-file entry.
/// Fails closed — there is no fallback parser.
pub fn parse_source(
    source: &str,
    file_id: crate::node_id::FileID,
) -> Result<crate::compiling::bridge::BridgedParse, String> {
    parse_source_in(None, source, file_id)
}

/// [`parse_source`] through an explicit session.
fn parse_source_in(
    parser: Option<&ParserSession>,
    source: &str,
    file_id: crate::node_id::FileID,
) -> Result<crate::compiling::bridge::BridgedParse, String> {
    crate::profile::init();
    profiling::scope!("frontend.parse_source");
    let session = resolve(parser)?;
    let mut io = talk_runtime::io::CaptureIO::default();
    let run = {
        profiling::scope!("frontend.execute");
        talk_runtime::interp::run_export(
            &session.module,
            "parse_file_source",
            &[talk_runtime::interp::HostValue::String(
                source.as_bytes().to_vec(),
            )],
            crate::backend::string_shape(),
            talk_runtime::interp::Budgets::default(),
            &mut io,
        )?
    };
    crate::compiling::bridge::adapt(&run, &session.schema, file_id)
}

/// Run one of the frontend's `String -> String` validation exports
/// (the dump surface) through the embedded session.
pub fn dump_export(name: &str, source: &str) -> Result<String, String> {
    crate::profile::init();
    profiling::scope!("frontend.dump_export");
    let session = FrontendSession::shared()?;
    let mut io = talk_runtime::io::CaptureIO::default();
    let run = {
        profiling::scope!("frontend.execute");
        talk_runtime::interp::run_export(
            &session.module,
            name,
            &[talk_runtime::interp::HostValue::String(
                source.as_bytes().to_vec(),
            )],
            crate::backend::string_shape(),
            talk_runtime::interp::Budgets::default(),
            &mut io,
        )?
    };
    let bytes = run
        .string_bytes(&run.value)
        .map_err(|error| format!("{name} did not return a string: {error}"))?;
    String::from_utf8(bytes.to_vec())
        .map_err(|error| format!("{name} output is not UTF-8: {error}"))
}

/// Lex one source through the frontend artifact (ADR 0043 Stage 5):
/// the token stream with comments included as LineComment tokens,
/// plus whether the scan completed without a lex error.
pub fn lex(source: &str) -> Result<(Vec<crate::parsing::lexing::token::Token>, bool), String> {
    crate::profile::init();
    profiling::scope!("frontend.lex");
    let session = FrontendSession::shared()?;
    let mut io = talk_runtime::io::CaptureIO::default();
    let run = {
        profiling::scope!("frontend.execute");
        talk_runtime::interp::run_export(
            &session.module,
            "lex_tokens",
            &[talk_runtime::interp::HostValue::String(
                source.as_bytes().to_vec(),
            )],
            crate::backend::string_shape(),
            talk_runtime::interp::Budgets::default(),
            &mut io,
        )?
    };
    crate::compiling::bridge::lex_tokens(&run, &session.schema)
}

/// One strict whole-file parse through the frontend artifact,
/// assembled into the compiler's parse AST (ADR 0043 Stage 4). A hard
/// parse failure or a bridge/loader error is the returned error;
/// recovery diagnostics come back as parsing diagnostics.
pub fn parse_ast(
    input: &str,
    file_id: crate::node_id::FileID,
    path: &str,
) -> Result<
    (
        crate::ast::AST<crate::ast::Parsed>,
        Vec<crate::common::diagnostic::AnyDiagnostic>,
    ),
    crate::parsing::parser_error::ParserError,
> {
    parse_ast_in(None, input, file_id, path)
}

/// [`parse_ast`] through an explicit session (bootstrap stage 2).
pub fn parse_ast_in(
    parser: Option<&ParserSession>,
    input: &str,
    file_id: crate::node_id::FileID,
    path: &str,
) -> Result<
    (
        crate::ast::AST<crate::ast::Parsed>,
        Vec<crate::common::diagnostic::AnyDiagnostic>,
    ),
    crate::parsing::parser_error::ParserError,
> {
    parse_ast_with_comments_in(parser, input, file_id, path)
        .map(|(ast, diagnostics, _)| (ast, diagnostics))
}

/// `parse_ast` plus the comment byte ranges the formatter reads.
pub fn parse_ast_with_comments(
    input: &str,
    file_id: crate::node_id::FileID,
    path: &str,
) -> Result<
    (
        crate::ast::AST<crate::ast::Parsed>,
        Vec<crate::common::diagnostic::AnyDiagnostic>,
        Vec<(u32, u32)>,
    ),
    crate::parsing::parser_error::ParserError,
> {
    parse_ast_with_comments_in(None, input, file_id, path)
}

fn parse_ast_with_comments_in(
    parser: Option<&ParserSession>,
    input: &str,
    file_id: crate::node_id::FileID,
    path: &str,
) -> Result<
    (
        crate::ast::AST<crate::ast::Parsed>,
        Vec<crate::common::diagnostic::AnyDiagnostic>,
        Vec<(u32, u32)>,
    ),
    crate::parsing::parser_error::ParserError,
> {
    use crate::parsing::parser_error::ParserError;
    let bridged = parse_source_in(parser, input, file_id).map_err(|error| ParserError::Frontend {
        code: "parser.frontend-bridge".into(),
        message: error,
        span: None,
        expected: None,
    })?;
    if let Some(failure) = bridged.failure {
        return Err(ParserError::Frontend {
            code: failure.code,
            message: failure.message,
            span: failure.span,
            expected: failure.expected,
        });
    }
    let diagnostics = bridged
        .diags
        .into_iter()
        .map(|fail| {
            crate::common::diagnostic::AnyDiagnostic::Parsing(crate::common::diagnostic::Diagnostic {
                id: crate::node_id::NodeID(file_id, 0),
                severity: crate::common::diagnostic::Severity::Error,
                kind: ParserError::Frontend {
                    code: fail.code,
                    message: fail.message,
                    span: fail.span,
                    expected: fail.expected,
                },
            })
        })
        .collect();
    let mut meta = bridged.meta;
    meta.path = std::path::PathBuf::from(path);
    let comments = bridged.comments;
    Ok((
        crate::ast::AST {
            path: path.to_string(),
            roots: bridged.roots,
            meta,
            phase: crate::ast::Parsed,
            node_ids: crate::common::id_generator::IDGenerator {
                last: bridged.next_node_id,
            },
            file_id,
            skip_core_prelude: false,
        },
        diagnostics,
        comments,
    ))
}

/// The lenient contract (the editor path, frozen from the reference):
/// a hard failure degrades to an EMPTY file AST carrying the failure
/// as a diagnostic; recoverable problems already come back as
/// diagnostics from the strict parse.
pub fn parse_ast_lenient(
    input: &str,
    file_id: crate::node_id::FileID,
    path: &str,
) -> (
    crate::ast::AST<crate::ast::Parsed>,
    Vec<crate::common::diagnostic::AnyDiagnostic>,
) {
    match parse_ast(input, file_id, path) {
        Ok(parsed) => parsed,
        Err(error) => (
            crate::ast::AST {
                path: path.to_string(),
                roots: vec![],
                meta: Default::default(),
                phase: crate::ast::Parsed,
                node_ids: Default::default(),
                file_id,
                skip_core_prelude: false,
            },
            vec![crate::common::diagnostic::AnyDiagnostic::Parsing(
                crate::common::diagnostic::Diagnostic {
                    id: crate::node_id::NodeID(file_id, 0),
                    severity: crate::common::diagnostic::Severity::Error,
                    kind: error,
                },
            )],
        ),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn repo_root() -> &'static Path {
        Path::new(env!("CARGO_MANIFEST_DIR"))
    }

    #[test]
    fn embedded_session_is_shared_across_threads() {
        fn assert_shareable<T: Send + Sync>() {}
        assert_shareable::<talk_runtime::Module>();

        let expected = FrontendSession::shared().expect("frontend session") as *const _ as usize;
        let threads: Vec<_> = (0..8)
            .map(|_| {
                std::thread::spawn(|| {
                    FrontendSession::shared().expect("frontend session") as *const _ as usize
                })
            })
            .collect();
        for thread in threads {
            assert_eq!(thread.join().expect("session thread"), expected);
        }
    }

    #[test]
    #[ignore = "run by scripts/frontend-vm-stats.sh"]
    fn write_vm_stats_profile() {
        use std::fmt::Write as _;

        let output = std::env::var_os("TALK_FRONTEND_VM_STATS_OUTPUT")
            .map(std::path::PathBuf::from)
            .expect("TALK_FRONTEND_VM_STATS_OUTPUT must name the report file");
        let root = repo_root();
        let corpus = sources(root).expect("frontend sources load");
        let bootstrap = regenerate(root).expect("frontend bootstraps");
        let module = talk_runtime::Module::decode_bytecode(&bootstrap.image)
            .expect("generated frontend artifact decodes");
        let mut stats = talk_runtime::VmStats::for_module(&module);

        for (name, source) in &corpus {
            let mut io = talk_runtime::io::CaptureIO::default();
            talk_runtime::interp::run_export_with_stats(
                &module,
                "parse_file_source",
                &[talk_runtime::interp::HostValue::String(
                    source.as_bytes().to_vec(),
                )],
                crate::backend::string_shape(),
                talk_runtime::interp::Budgets::default(),
                &mut io,
                &mut stats,
            )
            .unwrap_or_else(|error| panic!("frontend failed to parse {name}: {error}"));
        }

        let source_bytes: usize = corpus.iter().map(|(_, source)| source.len()).sum();
        let mut report = String::new();
        let _ = writeln!(
            report,
            "artifact_sha256: {}",
            bootstrap.manifest.artifact_digest
        );
        let _ = writeln!(report, "artifact_bytes: {}", bootstrap.image.len());
        let _ = writeln!(report, "workload: stdlib/syntax/*.tlk, sorted by filename");
        let _ = writeln!(report, "source_files: {}", corpus.len());
        let _ = writeln!(report, "source_bytes: {source_bytes}");
        for (name, source) in &corpus {
            let _ = writeln!(report, "source: {name} {}", source.len());
        }
        for (index, optimizations) in bootstrap.stage_optimizations.iter().enumerate() {
            let _ = writeln!(report, "\noptimization_stage_{}:", index + 1);
            let mut total = 0u64;
            for pass in &optimizations.passes {
                total += pass.applied;
                let _ = writeln!(report, "  {:<28} {}", pass.name, pass.applied);
            }
            let _ = writeln!(report, "  {:<28} {total}", "total");
        }
        let _ = writeln!(report);
        report.push_str(&stats.render());
        std::fs::write(&output, report)
            .unwrap_or_else(|error| panic!("failed to write {}: {error}", output.display()));
    }

    /// The fast staleness gate: the checked-in manifest must tie the
    /// checked-in artifact to the current frontend sources and this
    /// compiler's bytecode format. Editing a frontend source (or
    /// bumping the wire format) without regenerating fails here;
    /// regenerate with `talk bootstrap`.
    #[test]
    fn checked_in_frontend_artifact_matches_sources() {
        let root = repo_root();
        let image = std::fs::read(artifact_path(root)).expect(
            "bootstrap/frontend.tbc is missing; regenerate with `talk bootstrap`",
        );
        let manifest_text = std::fs::read_to_string(manifest_path(root)).expect(
            "bootstrap/frontend.manifest is missing; regenerate with `talk bootstrap`",
        );
        let abi_text = std::fs::read_to_string(abi_path(root)).expect(
            "bootstrap/frontend.abi is missing; regenerate with `talk bootstrap`",
        );
        let manifest = ArtifactManifest::parse(&manifest_text).expect("manifest parses");
        manifest
            .verify(
                &sources(root).expect("frontend sources"),
                &image,
                Some(&abi_text),
            )
            .expect("checked-in frontend artifact is stale; regenerate with `talk bootstrap`");
    }

    /// The loader end-to-end: the checked-in artifact decodes and its
    /// parse export answers.
    #[test]
    fn checked_in_frontend_artifact_loads_and_parses() {
        let module = load(repo_root()).expect("frontend artifact loads");
        let mut io = talk_runtime::io::CaptureIO::default();
        let run = talk_runtime::interp::run_export(
            &module,
            "parse",
            &[talk_runtime::interp::HostValue::String(
                b"let x = 1\n".to_vec(),
            )],
            crate::backend::string_shape(),
            talk_runtime::interp::Budgets::default(),
            &mut io,
        )
        .expect("parse export runs");
        let dump = String::from_utf8(
            run.string_bytes(&run.value)
                .expect("parse returns a string")
                .to_vec(),
        )
        .expect("dump is UTF-8");
        assert!(dump.contains("Decl::Let"), "unexpected dump:\n{dump}");
    }
}
