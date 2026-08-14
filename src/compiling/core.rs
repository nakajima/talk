use std::{
    path::PathBuf,
    sync::{Arc, OnceLock},
};

#[cfg(target_family = "wasm")]
use flate2::read::GzDecoder;
#[cfg(not(target_family = "wasm"))]
use flate2::{Compression, write::GzEncoder};
#[cfg(not(target_family = "wasm"))]
use std::io::Write;

use crate::compiling::module::Module;
#[cfg(not(target_family = "wasm"))]
use crate::compiling::{
    driver::{CompilationMode, Driver, DriverConfig, Source},
    module::ModuleId,
};

const TALK_CORE_PATH_ENV: &str = "TALK_CORE_PATH";

pub fn path_override() -> Option<PathBuf> {
    std::env::var_os(TALK_CORE_PATH_ENV)
        .filter(|path| !path.is_empty())
        .map(|path| {
            let path = PathBuf::from(path);
            path.canonicalize().unwrap_or(path)
        })
}

struct CoreArtifacts {
    module: Arc<Module>,
    typed: Arc<crate::compiling::typed_program::TypedProgram>,
}

static CORE: OnceLock<CoreArtifacts> = OnceLock::new();

pub fn compile() -> Arc<Module> {
    CORE.get_or_init(initialize).module.clone()
}

/// The typed bodies behind the core interface. The backend compiles the
/// reachable source graph as one unit, so core callables supply their
/// bodies from here.
pub(crate) fn typed_program() -> Arc<crate::compiling::typed_program::TypedProgram> {
    CORE.get_or_init(initialize).typed.clone()
}

#[cfg(not(target_family = "wasm"))]
pub fn artifact_bytes() -> Result<Vec<u8>, String> {
    let artifacts = CORE.get_or_init(initialize);
    let payload = bincode::serialize(&(artifacts.module.as_ref(), artifacts.typed.as_ref()))
        .map_err(|error| format!("failed to serialize core artifact: {error}"))?;
    let mut encoder = GzEncoder::new(Vec::new(), Compression::best());
    encoder
        .write_all(&payload)
        .map_err(|error| format!("failed to compress core artifact: {error}"))?;
    encoder
        .finish()
        .map_err(|error| format!("failed to finish core artifact: {error}"))
}

#[cfg(not(target_family = "wasm"))]
pub fn artifact_manifest(bytes: &[u8]) -> Result<String, String> {
    let compiler_stamp = compiler_stamp().ok_or("compiler stamp is unavailable")?;
    Ok(format!(
        "format_version: {ARTIFACT_FORMAT_VERSION}\ncompiler_stamp: {compiler_stamp}\nartifact_digest: {}\n",
        crate::compiling::manifest::artifact_digest(bytes),
    ))
}

pub use crate::front::module::CORE_SOURCE_NAMES;

pub const ARTIFACT_FORMAT_VERSION: u32 = 1;
pub const ARTIFACT_PATH: &str = "bootstrap/core.bin.gz";
pub const ARTIFACT_MANIFEST_PATH: &str = "bootstrap/core.manifest";

/// All core source strings, in a fixed order. Browser builds consume the
/// checked-in compiled artifact and deliberately carry no core source text.
#[cfg(not(target_family = "wasm"))]
pub fn core_sources() -> Vec<(&'static str, &'static str)> {
    vec![
        ("Ownership.tlk", include_str!("../../core/Ownership.tlk")),
        ("Optional.tlk", include_str!("../../core/Optional.tlk")),
        ("Result.tlk", include_str!("../../core/Result.tlk")),
        ("Operators.tlk", include_str!("../../core/Operators.tlk")),
        ("Convert.tlk", include_str!("../../core/Convert.tlk")),
        ("String.tlk", include_str!("../../core/String.tlk")),
        ("Memory.tlk", include_str!("../../core/Memory.tlk")),
        (
            "UnicodeData.tlk",
            include_str!("../../core/UnicodeData.tlk"),
        ),
        (
            "TextUnicodeData.tlk",
            include_str!("../../core/TextUnicodeData.tlk"),
        ),
        ("Unicode.tlk", include_str!("../../core/Unicode.tlk")),
        ("Array.tlk", include_str!("../../core/Array.tlk")),
        (
            "InlineArray.tlk",
            include_str!("../../core/InlineArray.tlk"),
        ),
        ("Iterable.tlk", include_str!("../../core/Iterable.tlk")),
        ("Async.tlk", include_str!("../../core/Async.tlk")),
        ("IO.tlk", include_str!("../../core/IO.tlk")),
        ("Showable.tlk", include_str!("../../core/Showable.tlk")),
        ("Range.tlk", include_str!("../../core/Range.tlk")),
        ("Host.tlk", include_str!("../../core/Host.tlk")),
        (
            "StringBuilder.tlk",
            include_str!("../../core/StringBuilder.tlk"),
        ),
        ("Text.tlk", include_str!("../../core/Text.tlk")),
    ]
}

#[cfg(target_family = "wasm")]
pub fn core_sources() -> Vec<(&'static str, &'static str)> {
    Vec::new()
}

#[cfg(not(target_family = "wasm"))]
fn compilation_sources() -> Vec<Source> {
    if let Some(core_dir) = path_override() {
        assert!(
            core_dir.is_dir(),
            "{TALK_CORE_PATH_ENV} must point to a directory: {}",
            core_dir.display()
        );

        return CORE_SOURCE_NAMES
            .iter()
            .map(|name| Source::from(core_dir.join(name)))
            .collect();
    }

    core_sources()
        .into_iter()
        .map(|(name, content)| Source::in_memory(name.into(), content))
        .collect()
}

#[cfg(not(target_family = "wasm"))]
fn initialize() -> CoreArtifacts {
    if let Some(cached) = load_cached() {
        return cached;
    }
    compile_from_sources()
}

#[cfg(target_family = "wasm")]
fn initialize() -> CoreArtifacts {
    let compressed = include_bytes!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/bootstrap/core.bin.gz"
    ));
    let decoder = GzDecoder::new(compressed.as_slice());
    let (module, typed): (Module, crate::compiling::typed_program::TypedProgram) =
        bincode::deserialize_from(decoder)
            .unwrap_or_else(|error| panic!("invalid embedded core artifact: {error}"));
    CoreArtifacts {
        module: Arc::new(module),
        typed: Arc::new(typed),
    }
}

#[cfg(not(target_family = "wasm"))]
fn compile_from_sources() -> CoreArtifacts {
    let _s = tracing::trace_span!("compile_prelude", prelude = true).entered();
    let mut config = DriverConfig::new("Core");
    config.module_id = ModuleId::Core;
    config.mode = CompilationMode::Library;
    let driver = Driver::new_bare(compilation_sources(), config);

    #[allow(clippy::unwrap_used)]
    let typed = driver
        .parse()
        .unwrap()
        .resolve_names()
        .unwrap()
        .type_check();

    assert!(
        !typed.has_errors(),
        "Core module compiled with errors: {:#?}",
        typed.diagnostics()
    );

    let program = typed.phase.program.clone();
    let module = Arc::new(typed.module("Core"));
    store_cached(&module, &program);
    CoreArtifacts {
        module,
        typed: Arc::new(program),
    }
}

// ===== The compiled-core disk cache =====
//
// Core's sources are fixed per checkout, so its parse/resolve/type
// products are a pure function of (sources, compiler). The cache key
// hashes the sources plus this binary's identity (mtime and length of
// the running executable), so ANY rebuild of the compiler invalidates
// it — the historical core.bin trap was hashing sources only, which
// kept stale caches across lowerer changes. A `TALK_CORE_PATH`
// override hashes the on-disk sources instead of the embedded ones.

/// This compiler's content identity for cache keys (CLEAN-05): a hash
/// of the frontend-relevant compiler sources and the bootstrap
/// frontend artifact, generated at build time. Unlike the executable's
/// mtime and length, relinking after an unrelated change (editor, CLI,
/// MIR, VM) does not invalidate compile caches.
pub(crate) fn compiler_stamp() -> Option<&'static str> {
    #[cfg(target_family = "wasm")]
    {
        None
    }

    #[cfg(not(target_family = "wasm"))]
    {
        Some(include_str!(concat!(
            env!("OUT_DIR"),
            "/compiler_stamp.txt"
        )))
    }
}

#[cfg(not(target_family = "wasm"))]
fn cache_key() -> Option<[u8; 32]> {
    // The bundled source set is fixed for the process: hash it once.
    // An override directory can change between runs, so its key stays
    // dynamic.
    static BUNDLED_KEY: OnceLock<Option<[u8; 32]>> = OnceLock::new();
    if path_override().is_none() {
        return *BUNDLED_KEY.get_or_init(cache_key_dynamic);
    }
    cache_key_dynamic()
}

#[cfg(not(target_family = "wasm"))]
fn cache_key_dynamic() -> Option<[u8; 32]> {
    let sources: Vec<(String, String)> = if let Some(core_dir) = path_override() {
        CORE_SOURCE_NAMES
            .iter()
            .map(|name| {
                std::fs::read_to_string(core_dir.join(name))
                    .ok()
                    .map(|content| (name.to_string(), content))
            })
            .collect::<Option<Vec<_>>>()?
    } else {
        core_sources()
            .into_iter()
            .map(|(name, content)| (name.to_string(), content.to_string()))
            .collect()
    };
    let refs: Vec<(&str, &str)> = sources
        .iter()
        .map(|(name, content)| (name.as_str(), content.as_str()))
        .collect();
    super::cache::key("core", &refs, compiler_stamp())
}

#[cfg(not(target_family = "wasm"))]
fn load_cached() -> Option<CoreArtifacts> {
    load_cached_in(&super::cache::cache_root()?)
}

#[cfg(not(target_family = "wasm"))]
fn load_cached_in(root: &std::path::Path) -> Option<CoreArtifacts> {
    let key = cache_key()?;
    let payload = super::cache::load_in(root, "core", &key)?;
    let (module, typed): (Module, crate::compiling::typed_program::TypedProgram) =
        bincode::deserialize(&payload).ok()?;
    Some(CoreArtifacts {
        module: Arc::new(module),
        typed: Arc::new(typed),
    })
}

#[cfg(not(target_family = "wasm"))]
fn store_cached(module: &Module, typed: &crate::compiling::typed_program::TypedProgram) {
    let Some(root) = super::cache::cache_root() else {
        return;
    };
    store_cached_in(&root, module, typed);
}

#[cfg(not(target_family = "wasm"))]
fn store_cached_in(
    root: &std::path::Path,
    module: &Module,
    typed: &crate::compiling::typed_program::TypedProgram,
) {
    let Some(key) = cache_key() else { return };
    let payload = match bincode::serialize(&(module, typed)) {
        Ok(payload) => payload,
        Err(error) => {
            tracing::warn!("core cache serialize failed: {error}");
            return;
        }
    };
    super::cache::store_in(root, "core", &key, &payload);
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::name_resolution::symbol::Symbol;

    /// The disk cache round trip: a stored core deserializes into the
    /// same interface and typed products the compile produced. Runs
    /// against an injected temporary root (CLEAN-05) — never the user
    /// cache.
    #[test]
    fn core_cache_round_trips() {
        let artifacts = CORE.get_or_init(initialize);
        let root =
            std::env::temp_dir().join(format!("talk-core-cache-test-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&root);
        store_cached_in(&root, &artifacts.module, &artifacts.typed);
        let cached = load_cached_in(&root).expect("cache loads under the same key");
        std::fs::remove_dir_all(&root).ok();
        assert_eq!(cached.module.name, artifacts.module.name);
        assert_eq!(cached.module.exports.len(), artifacts.module.exports.len());
        assert_eq!(
            cached.module.types.schemes.len(),
            artifacts.module.types.schemes.len()
        );
        assert_eq!(
            cached.typed.symbol_names().len(),
            artifacts.typed.symbol_names().len()
        );
    }

    #[test]
    fn checked_in_artifact_matches_compiled_core() {
        let bytes = artifact_bytes().expect("serialize core artifact");
        let manifest = artifact_manifest(&bytes).expect("render core manifest");
        assert_eq!(
            bytes,
            std::fs::read(ARTIFACT_PATH).expect("read checked-in core artifact")
        );
        assert_eq!(
            manifest,
            std::fs::read_to_string(ARTIFACT_MANIFEST_PATH).expect("read checked-in core manifest")
        );
    }

    #[test]
    fn core_resolves_without_errors() {
        // compile_from_sources() asserts there are no error diagnostics.
        let module = compile_from_sources().module;
        assert_eq!(module.name, "Core");
        assert!(!module.exports.is_empty());
        assert!(!module.types.schemes.is_empty());
    }

    #[test]
    fn core_exports_use_well_known_symbols() {
        let module = compile_from_sources().module;

        assert_eq!(
            module
                .exports
                .get("String")
                .and_then(|set| set.first().copied()),
            Some(Symbol::String)
        );
        assert_eq!(
            module
                .exports
                .get("Array")
                .and_then(|set| set.first().copied()),
            Some(Symbol::Array)
        );
        assert_eq!(
            module
                .exports
                .get("InlineArray")
                .and_then(|set| set.first().copied()),
            Some(Symbol::InlineArray)
        );
        assert_eq!(
            module
                .exports
                .get("Storage")
                .and_then(|set| set.first().copied()),
            Some(Symbol::Storage)
        );
        assert_eq!(
            module
                .exports
                .get("Character")
                .and_then(|set| set.first().copied()),
            Some(Symbol::Character)
        );
        assert_eq!(
            module
                .exports
                .get("Borrowed")
                .and_then(|set| set.first().copied()),
            Some(Symbol::Borrowed)
        );
        assert_eq!(
            module
                .exports
                .get("Owner")
                .and_then(|set| set.first().copied()),
            Some(Symbol::Owner)
        );

        let catalog = &module.types.catalog;
        assert!(catalog.structs.contains_key(&Symbol::String));
        assert!(catalog.structs.contains_key(&Symbol::Array));
        assert!(catalog.structs.contains_key(&Symbol::InlineArray));
        assert!(catalog.structs.contains_key(&Symbol::Storage));
        assert!(catalog.structs.contains_key(&Symbol::Character));
        assert!(catalog.protocols.contains_key(&Symbol::Borrowed));
        assert!(catalog.protocols.contains_key(&Symbol::Owner));
    }

    #[test]
    fn core_iterator_into_array_conformance_is_exported() {
        let module = compile_from_sources().module;
        let array_into_iterator = module.exports["ArrayIntoIterator"][0];
        let into = module.exports["Into"][0];
        let target = crate::types::ty::ProtocolRef {
            protocol: into,
            args: vec![crate::types::ty::Ty::Nominal(
                Symbol::Array,
                vec![crate::types::ty::Ty::Nominal(Symbol::Int, vec![])],
            )],
        };
        let catalog = &module.types.catalog;
        let matches = catalog.matching_conformances(
            array_into_iterator,
            &[crate::types::ty::Ty::Nominal(Symbol::Int, vec![])],
            &target,
        );
        assert_eq!(matches.len(), 1);
    }
}
