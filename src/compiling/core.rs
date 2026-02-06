use std::sync::Arc;

use lazy_static::lazy_static;
use sha2::{Digest, Sha256};

use crate::compiling::{
    driver::{CompilationMode, Driver, DriverConfig, Source},
    module::{Module, ModuleId},
};

lazy_static! {
    static ref CORE_MODULE: Arc<Module> = Arc::new(load_or_compile());
}

pub fn compile() -> Arc<Module> {
    CORE_MODULE.clone()
}

/// All core source strings, in a fixed order for hashing.
fn core_sources() -> Vec<(&'static str, &'static str)> {
    vec![
        ("Optional.tlk", include_str!("../../core/Optional.tlk")),
        ("Operators.tlk", include_str!("../../core/Operators.tlk")),
        ("String.tlk", include_str!("../../core/String.tlk")),
        ("Memory.tlk", include_str!("../../core/Memory.tlk")),
        ("Array.tlk", include_str!("../../core/Array.tlk")),
        ("Iterable.tlk", include_str!("../../core/Iterable.tlk")),
        ("Generator.tlk", include_str!("../../core/Generator.tlk")),
        ("Async.tlk", include_str!("../../core/Async.tlk")),
        ("IO.tlk", include_str!("../../core/IO.tlk")),
        ("File.tlk", include_str!("../../core/File.tlk")),
    ]
}

fn source_hash() -> [u8; 32] {
    let mut hasher = Sha256::new();
    for (name, content) in core_sources() {
        hasher.update(name.as_bytes());
        hasher.update(content.as_bytes());
    }
    hasher.finalize().into()
}

fn cache_path() -> std::path::PathBuf {
    std::path::PathBuf::from("target/.talk-cache/core.bin")
}

fn load_cached() -> Option<Module> {
    let path = cache_path();
    let data = std::fs::read(&path).ok()?;
    // First 32 bytes are the source hash
    if data.len() < 32 {
        return None;
    }
    let (stored_hash, payload) = data.split_at(32);
    let expected = source_hash();
    if stored_hash != expected {
        tracing::debug!("core cache hash mismatch, recompiling");
        return None;
    }
    match bincode::deserialize::<Module>(payload) {
        Ok(module) => {
            tracing::debug!("loaded core module from cache");
            Some(module)
        }
        Err(e) => {
            tracing::debug!("core cache deserialization failed: {e}, recompiling");
            None
        }
    }
}

fn save_cached(module: &Module) {
    let path = cache_path();
    if let Some(parent) = path.parent() {
        let _ = std::fs::create_dir_all(parent);
    }
    let hash = source_hash();
    let payload = match bincode::serialize(module) {
        Ok(p) => p,
        Err(e) => {
            tracing::debug!("core cache serialization failed: {e}");
            return;
        }
    };
    let mut data = Vec::with_capacity(32 + payload.len());
    data.extend_from_slice(&hash);
    data.extend_from_slice(&payload);
    if let Err(e) = std::fs::write(&path, &data) {
        tracing::debug!("core cache write failed: {e}");
    } else {
        tracing::debug!("saved core module to cache");
    }
}

fn load_or_compile() -> Module {
    if let Some(module) = load_cached() {
        return module;
    }

    let module = _compile();
    save_cached(&module);
    module
}

fn _compile() -> Module {
    let _s = tracing::trace_span!("compile_prelude", prelude = true).entered();
    let mut config = DriverConfig::new("Core");
    config.module_id = ModuleId::Core;
    config.mode = CompilationMode::Library;
    let sources = core_sources()
        .into_iter()
        .map(|(name, content)| Source::in_memory(name.into(), content))
        .collect();
    let driver = Driver::new_bare(sources, config);

    #[allow(clippy::unwrap_used)]
    let module = driver
        .parse()
        .unwrap()
        .resolve_names()
        .unwrap()
        .typecheck()
        .unwrap()
        .lower()
        .unwrap()
        .module("Core");

    module
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn core_module_roundtrips_through_cache() {
        // Compile from scratch
        let original = _compile();

        // Serialize and deserialize
        let payload = bincode::serialize(&original).expect("serialization failed");
        let deserialized: Module = bincode::deserialize(&payload).expect("deserialization failed");

        // The deserialized module should match the original
        assert_eq!(original.name, deserialized.name);
        assert_eq!(original.id, deserialized.id);
        assert_eq!(original.exports.len(), deserialized.exports.len());
        assert_eq!(
            original.program.functions.len(),
            deserialized.program.functions.len()
        );
        assert_eq!(
            original.types.types_by_symbol.len(),
            deserialized.types.types_by_symbol.len()
        );
    }

    #[test]
    fn source_hash_is_deterministic() {
        let h1 = source_hash();
        let h2 = source_hash();
        assert_eq!(h1, h2);
    }
}
