use std::{
    path::PathBuf,
    sync::{Arc, OnceLock},
};

use crate::compiling::{
    driver::{CompilationMode, Driver, DriverConfig, Source},
    module::{Module, ModuleId},
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
    CORE.get_or_init(_compile).module.clone()
}

/// The typed bodies behind the core interface. The backend compiles the
/// reachable source graph as one unit, so core callables supply their
/// bodies from here.
pub(crate) fn typed_program() -> Arc<crate::compiling::typed_program::TypedProgram> {
    CORE.get_or_init(_compile).typed.clone()
}

/// The filenames of all core source files.
pub const CORE_SOURCE_NAMES: &[&str] = &[
    "Ownership.tlk",
    "Optional.tlk",
    "Result.tlk",
    "Operators.tlk",
    "Convert.tlk",
    "String.tlk",
    "Memory.tlk",
    "UnicodeData.tlk",
    "Unicode.tlk",
    "Array.tlk",
    "InlineArray.tlk",
    "Dict.tlk",
    "Iterable.tlk",
    "Async.tlk",
    "IO.tlk",
    "Net.tlk",
    "Rawfile.tlk",
    "Showable.tlk",
    "Http.tlk",
    "OS.tlk",
    "Range.tlk",
    "Host.tlk",
];

/// All core source strings, in a fixed order.
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
        ("Unicode.tlk", include_str!("../../core/Unicode.tlk")),
        ("Array.tlk", include_str!("../../core/Array.tlk")),
        (
            "InlineArray.tlk",
            include_str!("../../core/InlineArray.tlk"),
        ),
        ("Dict.tlk", include_str!("../../core/Dict.tlk")),
        ("Iterable.tlk", include_str!("../../core/Iterable.tlk")),
        ("Async.tlk", include_str!("../../core/Async.tlk")),
        ("IO.tlk", include_str!("../../core/IO.tlk")),
        ("Net.tlk", include_str!("../../core/Net.tlk")),
        ("Rawfile.tlk", include_str!("../../core/Rawfile.tlk")),
        ("Showable.tlk", include_str!("../../core/Showable.tlk")),
        ("Http.tlk", include_str!("../../core/Http.tlk")),
        ("OS.tlk", include_str!("../../core/OS.tlk")),
        ("Range.tlk", include_str!("../../core/Range.tlk")),
        ("Host.tlk", include_str!("../../core/Host.tlk")),
    ]
}

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

fn _compile() -> CoreArtifacts {
    if let Some(cached) = load_cached() {
        return cached;
    }
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

/// This binary's identity (modification stamp and length): any rebuild
/// of the compiler invalidates compile caches keyed with it.
pub(crate) fn exe_fingerprint() -> Option<(u128, u64)> {
    let exe = std::env::current_exe().ok()?;
    let meta = std::fs::metadata(&exe).ok()?;
    let stamp = meta
        .modified()
        .ok()?
        .duration_since(std::time::UNIX_EPOCH)
        .ok()?
        .as_nanos();
    Some((stamp, meta.len()))
}

fn cache_key() -> Option<[u8; 32]> {
    use sha2::{Digest, Sha256};
    let mut hasher = Sha256::new();
    if let Some(core_dir) = path_override() {
        for name in CORE_SOURCE_NAMES {
            let content = std::fs::read(core_dir.join(name)).ok()?;
            hasher.update(name.as_bytes());
            hasher.update(&content);
        }
    } else {
        for (name, content) in core_sources() {
            hasher.update(name.as_bytes());
            hasher.update(content.as_bytes());
        }
    }
    let (stamp, len) = exe_fingerprint()?;
    hasher.update(stamp.to_le_bytes());
    hasher.update(len.to_le_bytes());
    Some(hasher.finalize().into())
}

fn cache_path() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("target/.talk-cache/core.bin")
}

fn load_cached() -> Option<CoreArtifacts> {
    let key = cache_key()?;
    let data = std::fs::read(cache_path()).ok()?;
    let (stored, payload) = data.split_at_checked(32)?;
    if stored != key {
        return None;
    }
    let (module, typed): (Module, crate::compiling::typed_program::TypedProgram) =
        bincode::deserialize(payload).ok()?;
    Some(CoreArtifacts {
        module: Arc::new(module),
        typed: Arc::new(typed),
    })
}

fn store_cached(module: &Module, typed: &crate::compiling::typed_program::TypedProgram) {
    let Some(key) = cache_key() else { return };
    let payload = match bincode::serialize(&(module, typed)) {
        Ok(payload) => payload,
        Err(error) => {
            tracing::warn!("core cache serialize failed: {error}");
            return;
        }
    };
    let path = cache_path();
    if let Some(parent) = path.parent()
        && std::fs::create_dir_all(parent).is_err()
    {
        return;
    }
    let mut bytes = key.to_vec();
    bytes.extend_from_slice(&payload);
    // Concurrent processes all compute identical bytes: write to a
    // process-unique sibling and rename atomically.
    let tmp = path.with_extension(format!("bin.{}", std::process::id()));
    if std::fs::write(&tmp, &bytes).is_ok() {
        let _ = std::fs::rename(&tmp, &path);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::name_resolution::symbol::Symbol;

    /// The disk cache round trip: a stored core deserializes into the
    /// same interface and typed products the compile produced.
    #[test]
    fn core_cache_round_trips() {
        let artifacts = CORE.get_or_init(_compile);
        store_cached(&artifacts.module, &artifacts.typed);
        let cached = load_cached().expect("cache loads under the same key");
        assert_eq!(cached.module.name, artifacts.module.name);
        assert_eq!(cached.module.exports.len(), artifacts.module.exports.len());
        assert_eq!(
            cached.module.types.schemes.len(),
            artifacts.module.types.schemes.len()
        );
        assert_eq!(
            cached.typed.resolved_names().symbol_names.len(),
            artifacts.typed.resolved_names().symbol_names.len()
        );
    }

    #[test]
    fn core_resolves_without_errors() {
        // _compile() asserts there are no error diagnostics.
        let module = _compile().module;
        assert_eq!(module.name, "Core");
        assert!(!module.exports.is_empty());
        assert!(!module.types.schemes.is_empty());
    }

    #[test]
    fn core_exports_use_well_known_symbols() {
        let module = _compile().module;

        assert_eq!(module.exports.get("String").and_then(|set| set.first().copied()), Some(Symbol::String));
        assert_eq!(module.exports.get("Array").and_then(|set| set.first().copied()), Some(Symbol::Array));
        assert_eq!(
            module.exports.get("InlineArray").and_then(|set| set.first().copied()),
            Some(Symbol::InlineArray)
        );
        assert_eq!(
            module.exports.get("Storage").and_then(|set| set.first().copied()),
            Some(Symbol::Storage)
        );
        assert_eq!(
            module.exports.get("Character").and_then(|set| set.first().copied()),
            Some(Symbol::Character)
        );
        assert_eq!(
            module.exports.get("Borrowed").and_then(|set| set.first().copied()),
            Some(Symbol::Borrowed)
        );
        assert_eq!(module.exports.get("Owner").and_then(|set| set.first().copied()), Some(Symbol::Owner));

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
        let module = _compile().module;
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
