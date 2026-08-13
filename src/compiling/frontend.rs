//! The self-hosted frontend's bootstrap profile (ADR 0043 §2–3): the
//! one owner of the frontend source set, service exports, allowed
//! effects, and checked-in artifact paths. The CLI's bare
//! `talk bootstrap` regenerates through this profile, the differential
//! harness compiles the same sources through it, and the compiler
//! loads the checked-in artifact through it — so none of them can
//! drift on what the frontend artifact is.

#[cfg(feature = "native-c")]
use crate::compiling::bootstrap::{BootstrapOutcome, bootstrap};
use crate::compiling::manifest::ArtifactManifest;
use std::path::{Path, PathBuf};

/// The frontend service exports (ADR 0043 §4): the category parse
/// operations, plus the lexer surfaces the differential harness
/// validates during migration. `parse_file_source` is the structured
/// result op — it returns the `ParseOutcome` value the ABI descriptor
/// describes, where the `parse` dump ops return rendered text.
pub const EXPORTS: [&str; 14] = [
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
    // Structured category entries for macro expansion (ADR 0026): the
    // substituted token text of an expansion parses against the invocation
    // position's category.
    "parse_block_items_source",
    "parse_pattern_source",
    "parse_type_source",
    "parse_members_source",
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

pub fn c_path(root: &Path) -> PathBuf {
    root.join("bootstrap").join("frontend.c")
}

/// The external symbol prefix of the native frontend library
/// (ADR 0048). Export symbols follow the shared boundary mangling in
/// `talk_native_runtime::library` (underscores double: `parse_file_source`
/// becomes `talk_frontend_parse__file__source`).
pub const NATIVE_PREFIX: &str = "talk_frontend";

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

#[cfg(feature = "native-c")]
fn export_strings() -> Vec<String> {
    EXPORTS.iter().map(|name| (*name).to_string()).collect()
}

#[cfg(feature = "native-c")]
fn effect_strings() -> Vec<String> {
    ALLOWED_EFFECTS
        .iter()
        .map(|name| (*name).to_string())
        .collect()
}

/// Rebuild the frontend artifacts from the on-disk sources, requiring
/// the stage-1/stage-2 fixed point over the bytecode, the ABI, and the
/// native C translation unit (ADR 0048).
#[cfg(feature = "native-c")]
pub fn regenerate(root: &Path) -> Result<BootstrapOutcome, String> {
    bootstrap(
        &sources(root)?,
        &export_strings(),
        &effect_strings(),
        Some(SCHEMA_ROOT),
        Some(NATIVE_PREFIX),
    )
}

/// Load and validate the checked-in frontend artifact: the manifest
/// must match the on-disk sources, the artifact bytes, the ABI
/// descriptor, and this compiler's bytecode format, and the image must
/// decode. Fails closed on any mismatch — there is no fallback parser.
pub fn load(root: &Path) -> Result<talk_vm::Module, String> {
    let artifact = artifact_path(root);
    let image = std::fs::read(&artifact)
        .map_err(|err| format!("failed to read {}: {err}", artifact.display()))?;
    let manifest_file = manifest_path(root);
    let manifest_text = std::fs::read_to_string(&manifest_file)
        .map_err(|err| format!("failed to read {}: {err}", manifest_file.display()))?;
    let abi_file = abi_path(root);
    let abi_text = std::fs::read_to_string(&abi_file)
        .map_err(|err| format!("failed to read {}: {err}", abi_file.display()))?;
    let c_file = c_path(root);
    let c_text = std::fs::read_to_string(&c_file)
        .map_err(|err| format!("failed to read {}: {err}", c_file.display()))?;
    let manifest = ArtifactManifest::parse(&manifest_text)?;
    manifest.verify(&sources(root)?, &image, Some(&abi_text), Some(&c_text))?;
    talk_vm::Module::decode_bytecode(&image)
        .map_err(|err| format!("frontend artifact failed to decode: {err:?}"))
}

/// The artifact triplet baked into this binary (ADR 0043 §2): the
/// compiler distribution IS the artifact — no filesystem needed at
/// runtime (wasm, installed binaries). `include_bytes!` tracks the
/// files, so a `talk bootstrap` regeneration reaches the binary on
/// the next cargo build.
#[cfg(any(test, target_arch = "wasm32"))]
const EMBEDDED_ARTIFACT: &[u8] = include_bytes!("../../bootstrap/frontend.tbc");
#[cfg(any(test, target_arch = "wasm32"))]
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
#[cfg(any(test, target_arch = "wasm32"))]
fn load_embedded() -> Result<talk_vm::Module, String> {
    crate::profile::init();
    profiling::scope!("frontend.load_embedded");
    let manifest = ArtifactManifest::parse(EMBEDDED_MANIFEST)?;
    manifest.verify_artifact(EMBEDDED_ARTIFACT, Some(EMBEDDED_ABI))?;
    talk_vm::Module::decode_bytecode(EMBEDDED_ARTIFACT)
        .map_err(|err| format!("frontend artifact failed to decode: {err:?}"))
}

/// The immutable frontend program and ABI shared by every compiler thread.
struct FrontendSession {
    module: talk_vm::Module,
    schema: crate::compiling::abi::AbiSchema,
}

impl FrontendSession {
    #[cfg(any(test, target_arch = "wasm32"))]
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
            module: talk_vm::Module::decode_bytecode(image)
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

/// Parse one source through the frontend artifact into the compiler's
/// own parse AST (ADR 0043 Stage 4): the strict whole-file entry.
/// Fails closed — there is no fallback parser.
pub fn parse_source(
    source: &str,
    file_id: crate::node_id::FileID,
) -> Result<crate::compiling::bridge::BridgedParse, String> {
    parse_source_in(None, source, file_id)
}

/// The parse-result schema alone, for the native production path — no
/// bytecode is decoded or executed to parse (ADR 0048).
#[cfg(not(target_arch = "wasm32"))]
fn shared_schema() -> Result<&'static crate::compiling::abi::AbiSchema, String> {
    static SCHEMA: std::sync::OnceLock<Result<crate::compiling::abi::AbiSchema, String>> =
        std::sync::OnceLock::new();
    SCHEMA
        .get_or_init(|| crate::compiling::abi::parse_schema(EMBEDDED_ABI))
        .as_ref()
        .map_err(Clone::clone)
}

/// [`parse_source`] through an explicit session. Production parsing
/// executes the native frontend (ADR 0048); a candidate session —
/// bootstrap stage 2 proving the stage-1 artifact parses its own
/// sources — executes as bytecode.
fn parse_source_in(
    parser: Option<&ParserSession>,
    source: &str,
    file_id: crate::node_id::FileID,
) -> Result<crate::compiling::bridge::BridgedParse, String> {
    crate::profile::init();
    profiling::scope!("frontend.parse_source");
    match parser {
        Some(candidate) => parse_source_vm(&candidate.0, source, file_id),
        #[cfg(not(target_arch = "wasm32"))]
        None => {
            let schema = shared_schema()?;
            crate::compiling::native_frontend::run_export(
                "parse_file_source",
                &[source.as_bytes()],
                |run| {
                    crate::compiling::bridge::adapt(
                        crate::compiling::bridge::FrontendRun::Native(run),
                        schema,
                        file_id,
                    )
                },
            )
        }
        // wasm32 executes the same verified frontend program as
        // bytecode: its toolchain cannot build the native artifact
        // (ADR 0048 wasm carve-out).
        #[cfg(target_arch = "wasm32")]
        None => parse_source_vm(FrontendSession::shared()?, source, file_id),
    }
}

/// The canonical ABI tag for a TokenKind variant, read from the frontend
/// schema so Rust never hardcodes the enum's ordering.
pub fn token_kind_tag(variant: &str) -> Result<u32, String> {
    #[cfg(not(target_arch = "wasm32"))]
    let schema = shared_schema()?;
    #[cfg(target_arch = "wasm32")]
    let schema = &FrontendSession::shared()?.schema;
    let Some(crate::compiling::abi::AbiTypeKind::Enum(variants)) =
        schema.types.get("TokenKind").map(|ty| &ty.kind)
    else {
        return Err("schema has no TokenKind".into());
    };
    variants
        .iter()
        .position(|(name, _)| name == variant)
        .map(|index| index as u32)
        .ok_or_else(|| format!("schema TokenKind has no variant `{variant}`"))
}

/// One structured category parse through the frontend: the substituted
/// token text of a macro expansion, parsed as block items, a pattern, or a
/// type (`export` is one of `parse_block_items_source`,
/// `parse_pattern_source`, or `parse_type_source`).
pub fn parse_category_source(
    export: &str,
    source: &str,
    file_id: crate::node_id::FileID,
) -> Result<crate::compiling::bridge::BridgedParse, String> {
    crate::profile::init();
    #[cfg(not(target_arch = "wasm32"))]
    {
        let schema = shared_schema()?;
        crate::compiling::native_frontend::run_export(export, &[source.as_bytes()], |run| {
            crate::compiling::bridge::adapt(
                crate::compiling::bridge::FrontendRun::Native(run),
                schema,
                file_id,
            )
        })
    }
    #[cfg(target_arch = "wasm32")]
    {
        let session = FrontendSession::shared()?;
        let mut io = talk_vm::io::CaptureIO::default();
        let run = talk_vm::interp::run_export(
            &session.module,
            export,
            &[talk_vm::interp::HostValue::String(
                source.as_bytes().to_vec(),
            )],
            crate::compiling::mir::string_shape(),
            talk_vm::interp::Budgets::default(),
            &mut io,
        )?;
        crate::compiling::bridge::adapt(
            crate::compiling::bridge::FrontendRun::Vm(&run),
            &session.schema,
            file_id,
        )
    }
}

/// One parse through a bytecode frontend session: bootstrap stage 2's
/// candidate proof on every target, and the production path on wasm32.
fn parse_source_vm(
    session: &FrontendSession,
    source: &str,
    file_id: crate::node_id::FileID,
) -> Result<crate::compiling::bridge::BridgedParse, String> {
    let mut io = talk_vm::io::CaptureIO::default();
    let run = {
        profiling::scope!("frontend.execute");
        talk_vm::interp::run_export(
            &session.module,
            "parse_file_source",
            &[talk_vm::interp::HostValue::String(
                source.as_bytes().to_vec(),
            )],
            crate::compiling::mir::string_shape(),
            talk_vm::interp::Budgets::default(),
            &mut io,
        )?
    };
    crate::compiling::bridge::adapt(
        crate::compiling::bridge::FrontendRun::Vm(&run),
        &session.schema,
        file_id,
    )
}

/// Run one of the frontend's `String -> String` validation exports
/// (the dump surface) through the native frontend.
pub fn dump_export(name: &str, source: &str) -> Result<String, String> {
    crate::profile::init();
    profiling::scope!("frontend.dump_export");
    #[cfg(not(target_arch = "wasm32"))]
    {
        crate::compiling::native_frontend::run_export(name, &[source.as_bytes()], |run| {
            let bytes = run
                .string_bytes(run.value)
                .map_err(|error| format!("{name} did not return a string: {error}"))?;
            String::from_utf8(bytes.to_vec())
                .map_err(|error| format!("{name} output is not UTF-8: {error}"))
        })
    }
    #[cfg(target_arch = "wasm32")]
    {
        let session = FrontendSession::shared()?;
        let mut io = talk_vm::io::CaptureIO::default();
        let run = talk_vm::interp::run_export(
            &session.module,
            name,
            &[talk_vm::interp::HostValue::String(
                source.as_bytes().to_vec(),
            )],
            crate::compiling::mir::string_shape(),
            talk_vm::interp::Budgets::default(),
            &mut io,
        )?;
        let bytes = run
            .string_bytes(&run.value)
            .map_err(|error| format!("{name} did not return a string: {error}"))?;
        String::from_utf8(bytes.to_vec())
            .map_err(|error| format!("{name} output is not UTF-8: {error}"))
    }
}

/// Lex one source through the native frontend (ADR 0043 Stage 5, ADR
/// 0048): the token stream with comments included as LineComment
/// tokens, plus whether the scan completed without a lex error.
pub fn lex(source: &str) -> Result<(Vec<crate::parsing::lexing::token::Token>, bool), String> {
    crate::profile::init();
    profiling::scope!("frontend.lex");
    #[cfg(not(target_arch = "wasm32"))]
    {
        let schema = shared_schema()?;
        crate::compiling::native_frontend::run_export("lex_tokens", &[source.as_bytes()], |run| {
            crate::compiling::bridge::lex_tokens(
                crate::compiling::bridge::FrontendRun::Native(run),
                schema,
            )
        })
    }
    #[cfg(target_arch = "wasm32")]
    {
        let session = FrontendSession::shared()?;
        let mut io = talk_vm::io::CaptureIO::default();
        let run = talk_vm::interp::run_export(
            &session.module,
            "lex_tokens",
            &[talk_vm::interp::HostValue::String(
                source.as_bytes().to_vec(),
            )],
            crate::compiling::mir::string_shape(),
            talk_vm::interp::Budgets::default(),
            &mut io,
        )?;
        crate::compiling::bridge::lex_tokens(
            crate::compiling::bridge::FrontendRun::Vm(&run),
            &session.schema,
        )
    }
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
    let bridged =
        parse_source_in(parser, input, file_id).map_err(|error| ParserError::Frontend {
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
            crate::common::diagnostic::AnyDiagnostic::Parsing(
                crate::common::diagnostic::Diagnostic {
                    id: crate::node_id::NodeID(file_id, 0),
                    severity: crate::common::diagnostic::Severity::Error,
                    kind: ParserError::Frontend {
                        code: fail.code,
                        message: fail.message,
                        span: fail.span,
                        expected: fail.expected,
                    },
                },
            )
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
            syntax: Default::default(),
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
                syntax: Default::default(),
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
    fn embedded_frontend_classifies_external_package_imports() {
        let session = ParserSession::from_artifact(EMBEDDED_ARTIFACT, EMBEDDED_ABI)
            .expect("embedded parser session");
        let (ast, diagnostics) = parse_ast_in(
            Some(&session),
            "use net::{ TcpStream }\n",
            crate::node_id::FileID(0),
            "main.tlk",
        )
        .expect("package import parses");
        assert!(diagnostics.is_empty());
        let crate::node::Node::Decl(decl) = &ast.roots[0] else {
            panic!("expected import declaration");
        };
        let crate::node_kinds::decl::DeclKind::Import(import) = &decl.kind else {
            panic!("expected import declaration");
        };
        assert_eq!(
            import.path,
            crate::node_kinds::decl::ImportPath::Package("net".to_string())
        );
    }

    #[test]
    fn embedded_frontend_classifies_recursive_glob_imports() {
        let session = ParserSession::from_artifact(EMBEDDED_ARTIFACT, EMBEDDED_ABI)
            .expect("embedded parser session");
        let (ast, diagnostics) = parse_ast_in(
            Some(&session),
            "use package::foo::*\n",
            crate::node_id::FileID(0),
            "main.tlk",
        )
        .expect("glob import parses");
        assert!(diagnostics.is_empty());
        let crate::node::Node::Decl(decl) = &ast.roots[0] else {
            panic!("expected import declaration");
        };
        let crate::node_kinds::decl::DeclKind::Import(import) = &decl.kind else {
            panic!("expected import declaration");
        };
        assert_eq!(
            import.path,
            crate::node_kinds::decl::ImportPath::Local("package::foo".to_string())
        );
        assert_eq!(
            import.symbols,
            crate::node_kinds::decl::ImportedSymbols::Glob
        );
    }

    #[test]
    fn embedded_session_is_shared_across_threads() {
        fn assert_shareable<T: Send + Sync>() {}
        assert_shareable::<talk_vm::Module>();

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
        let module = talk_vm::Module::decode_bytecode(&bootstrap.image)
            .expect("generated frontend artifact decodes");
        let mut stats = talk_vm::VmStats::for_module(&module);

        for (name, source) in &corpus {
            let mut io = talk_vm::io::CaptureIO::default();
            talk_vm::interp::run_export_with_stats(
                &module,
                "parse_file_source",
                &[talk_vm::interp::HostValue::String(
                    source.as_bytes().to_vec(),
                )],
                crate::compiling::mir::string_shape(),
                talk_vm::interp::Budgets::default(),
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

    /// ADR 0048 acceptance: the native frontend and the bootstrap
    /// bytecode agree, including on malformed and empty inputs, and a
    /// native failure comes back as an error rather than terminating
    /// this process.
    #[test]
    fn native_and_bytecode_frontends_agree() {
        let session = FrontendSession::shared().expect("embedded session");
        let inputs: &[&str] = &[
            "",
            "let x = 1\n",
            "pub func f(x: Int) -> Int {\n\tx * 2\n}\nprint(f(x: 21))\n",
            "func broken(\n",
            "let \u{fffd} = \"\u{1F600} not ascii\"\n",
            "match x { case",
        ];
        for input in inputs {
            let native = dump_export("parse", input);
            let mut io = talk_vm::io::CaptureIO::default();
            let bytecode = talk_vm::interp::run_export(
                &session.module,
                "parse",
                &[talk_vm::interp::HostValue::String(
                    input.as_bytes().to_vec(),
                )],
                crate::compiling::mir::string_shape(),
                talk_vm::interp::Budgets::default(),
                &mut io,
            )
            .and_then(|run| {
                let bytes = run.string_bytes(&run.value)?.to_vec();
                String::from_utf8(bytes).map_err(|error| error.to_string())
            });
            match (&native, &bytecode) {
                (Ok(native), Ok(bytecode)) => {
                    assert_eq!(native, bytecode, "dump diverged for {input:?}")
                }
                (Err(_), Err(_)) => {}
                _ => panic!("one path failed for {input:?}: native {native:?} vs vm {bytecode:?}"),
            }
        }
    }

    /// The fast staleness gate: the checked-in manifest must tie the
    /// checked-in artifact to the current frontend sources and this
    /// compiler's bytecode format. Editing a frontend source (or
    /// bumping the wire format) without regenerating fails here;
    /// regenerate with `talk bootstrap`.
    #[test]
    fn checked_in_frontend_artifact_matches_sources() {
        let root = repo_root();
        let image = std::fs::read(artifact_path(root))
            .expect("bootstrap/frontend.tbc is missing; regenerate with `talk bootstrap`");
        let manifest_text = std::fs::read_to_string(manifest_path(root))
            .expect("bootstrap/frontend.manifest is missing; regenerate with `talk bootstrap`");
        let abi_text = std::fs::read_to_string(abi_path(root))
            .expect("bootstrap/frontend.abi is missing; regenerate with `talk bootstrap`");
        let c_text = std::fs::read_to_string(c_path(root))
            .expect("bootstrap/frontend.c is missing; regenerate with `talk bootstrap`");
        let manifest = ArtifactManifest::parse(&manifest_text).expect("manifest parses");
        manifest
            .verify(
                &sources(root).expect("frontend sources"),
                &image,
                Some(&abi_text),
                Some(&c_text),
            )
            .expect("checked-in frontend artifact is stale; regenerate with `talk bootstrap`");
    }

    /// The loader end-to-end: the checked-in artifact decodes and its
    /// parse export answers.
    #[test]
    fn checked_in_frontend_artifact_loads_and_parses() {
        let module = load(repo_root()).expect("frontend artifact loads");
        let mut io = talk_vm::io::CaptureIO::default();
        let run = talk_vm::interp::run_export(
            &module,
            "parse",
            &[talk_vm::interp::HostValue::String(b"let x = 1\n".to_vec())],
            crate::compiling::mir::string_shape(),
            talk_vm::interp::Budgets::default(),
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

/// Format a source string at the default width, via the self-hosted
/// parser. The parse-free half lives in `parsing::formatter`
/// (ADR 0057 slice 3).
pub fn format_string(string: &str) -> String {
    format_string_with_width(string, 80)
}

/// Format a source string at `width`, via the self-hosted parser.
pub fn format_string_with_width(string: &str, width: usize) -> String {
    match parse_ast_with_comments(string, crate::node_id::FileID(0), "") {
        Ok((ast, _diagnostics, comments)) => {
            crate::parsing::formatter::format_parsed(&ast, width, &comments, string)
        }
        Err(_err) => string.to_string(),
    }
}

/// Highlight a source string, via the self-hosted lexer and parser (a
/// failed parse degrades to lexed tokens only).
pub fn highlight(source: &str) -> Vec<crate::parsing::highlighter::HighlightToken> {
    let ast = parse_ast(source, crate::node_id::FileID(0), "-")
        .ok()
        .map(|(ast, _)| ast);
    highlight_with_ast(source, ast.as_ref())
}

/// Highlight with a parse the caller already computed (the LSP's
/// analysis worker reuses the workspace build's cached parse instead of
/// re-parsing the document for tokens).
pub fn highlight_with_ast(
    source: &str,
    ast: Option<&crate::ast::AST<crate::parsing::ast::Parsed>>,
) -> Vec<crate::parsing::highlighter::HighlightToken> {
    // The frontend's lexing surface (ADR 0043 Stage 5): the token
    // stream with comments included as LineComment tokens.
    let lexed = lex(source).map(|(tokens, _)| tokens).unwrap_or_default();
    crate::parsing::highlighter::Higlighter::new(source).highlight_from(&lexed, ast)
}

/// Highlight a source string to HTML, via the self-hosted frontend.
pub fn highlight_html(source: &str) -> String {
    let mut tokens = highlight(source);
    tokens.sort_by(|a, b| a.start.cmp(&b.start).then_with(|| b.end.cmp(&a.end)));
    crate::parsing::highlighter::render_html_with_tokens(source, &tokens)
}
