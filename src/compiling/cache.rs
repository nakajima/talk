//! The compiled-artifact disk cache shared by core, stdlib, and syntax.
//!
//! Products are a pure function of (sources, compiler), so the cache
//! keys on the source contents plus this binary's identity and lives in
//! the user's cache directory — it survives across checkouts and works
//! for distributed binaries. Key-stamped filenames let several compiler
//! builds coexist; a store removes the stem's stale entries.

use std::path::PathBuf;

/// The cache root: `$XDG_CACHE_HOME/talk`, else `$HOME/.cache/talk`.
/// `None` disables the cache (no home, wasm).
pub fn cache_root() -> Option<PathBuf> {
    #[cfg(target_family = "wasm")]
    {
        None
    }
    #[cfg(not(target_family = "wasm"))]
    {
        if let Some(dir) = std::env::var_os("XDG_CACHE_HOME") {
            if !dir.is_empty() {
                return Some(PathBuf::from(dir).join("talk"));
            }
        }
        std::env::var_os("HOME")
            .filter(|dir| !dir.is_empty())
            .map(|home| PathBuf::from(home).join(".cache").join("talk"))
    }
}

/// Key a product on its source inputs and the executing binary's
/// identity. `read_source` yields each input's (path, content).
pub fn key(
    sources: &[(&str, &str)],
    exe_fingerprint: Option<(u128, u64)>,
) -> Option<[u8; 32]> {
    use sha2::{Digest, Sha256};
    let mut hasher = Sha256::new();
    for (path, content) in sources {
        hasher.update(path.as_bytes());
        hasher.update(content.as_bytes());
    }
    let (stamp, len) = exe_fingerprint?;
    hasher.update(stamp.to_le_bytes());
    hasher.update(len.to_le_bytes());
    Some(hasher.finalize().into())
}

fn stamped_path(stem: &str, key: &[u8; 32]) -> Option<PathBuf> {
    let short: String = key[..8].iter().map(|byte| format!("{byte:02x}")).collect();
    Some(cache_root()?.join(format!("{stem}-{short}.bin")))
}

/// Read a cached payload for `stem` under `key`. The full key is stored
/// at the payload's head and must match.
pub fn load(stem: &str, key: &[u8; 32]) -> Option<Vec<u8>> {
    let path = stamped_path(stem, key)?;
    let data = std::fs::read(path).ok()?;
    let (stored, payload) = data.split_at_checked(32)?;
    if stored != key {
        return None;
    }
    Some(payload.to_vec())
}

/// Store a payload for `stem` under `key`, replacing the stem's stale
/// entries. Concurrent processes compute identical bytes: write to a
/// process-unique sibling and rename atomically.
pub fn store(stem: &str, key: &[u8; 32], payload: &[u8]) {
    let Some(path) = stamped_path(stem, key) else { return };
    if let Some(parent) = path.parent()
        && std::fs::create_dir_all(parent).is_err()
    {
        return;
    }
    let mut bytes = key.to_vec();
    bytes.extend_from_slice(payload);
    let tmp = path.with_extension(format!("bin.{}", std::process::id()));
    if std::fs::write(&tmp, &bytes).is_err() {
        return;
    }
    if std::fs::rename(&tmp, &path).is_err() {
        let _ = std::fs::remove_file(&tmp);
        return;
    }
    if let Some(parent) = path.parent()
        && let Ok(entries) = std::fs::read_dir(parent)
    {
        let file_stem = stem.rsplit('/').next().unwrap_or(stem);
        let prefix = format!("{file_stem}-");
        for entry in entries.flatten() {
            let name = entry.file_name();
            let name = name.to_string_lossy();
            if name.starts_with(&prefix) && name.ends_with(".bin") && entry.path() != path {
                let _ = std::fs::remove_file(entry.path());
            }
        }
    }
}
