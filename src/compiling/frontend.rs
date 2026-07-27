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
pub const EXPORTS: [&str; 9] = [
    "lex",
    "trees",
    "parse",
    "parse_file_source",
    "parse_lenient",
    "parse_block_items",
    "parse_expr",
    "parse_pattern",
    "parse_type",
];

/// Effects the frontend may perform (ADR 0043 §7): deterministic
/// allocation and structured failure only — no IO, clock, or host
/// access.
pub const ALLOWED_EFFECTS: [&str; 2] = ["alloc", "panic"];

/// The root of the parse-result schema the ABI descriptor is generated
/// from (ADR 0043 §5).
pub const SCHEMA_ROOT: &str = "ParseOutcome";

pub fn source_dir(root: &Path) -> PathBuf {
    root.join("frontend")
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

/// The canonical frontend source set: every `.tlk` file in `frontend/`,
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

#[cfg(test)]
mod tests {
    use super::*;

    fn repo_root() -> &'static Path {
        Path::new(env!("CARGO_MANIFEST_DIR"))
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
