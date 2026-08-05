//! The compiled-artifact disk cache shared by core, stdlib, and syntax.
//!
//! Products are a pure function of (sources, compiler), so the cache
//! keys on the source contents plus the compiler's content identity
//! (build.rs's stamp of the frontend-relevant sources) and lives in the
//! user's cache directory — it survives across checkouts and works for
//! distributed binaries. Key-stamped filenames let several compiler
//! builds coexist; a store keeps the newest few stamps per stem and
//! removes older ones.

use std::path::{Path, PathBuf};

/// The serialization format version: folded into every key, so a
/// payload layout change invalidates by construction. Bump it when the
/// persisted product shapes or the key scheme change.
pub const FORMAT_VERSION: u64 = 1;

/// How many stamped versions of one stem to retain. Compiler builds
/// coexist across checkouts; older stamps are cleaned on store.
const RETAIN_STAMPS: usize = 4;

/// The cache root: `$XDG_CACHE_HOME/talk`, else `$HOME/.cache/talk`.
/// `None` disables the cache (no home, wasm). Tests inject their own
/// root through `load_in`/`store_in` instead of touching this.
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

/// Key a product on its source inputs and the compiler's content
/// identity. Every input is length-prefixed and domain-separated, so
/// distinct input sequences never share a byte stream (CLEAN-05).
pub fn key(stem: &str, sources: &[(&str, &str)], compiler_stamp: Option<&str>) -> Option<[u8; 32]> {
    use sha2::{Digest, Sha256};

    let mut hasher = Sha256::new();
    hasher.update(b"talk-cache\0");
    hasher.update(FORMAT_VERSION.to_le_bytes());
    frame(&mut hasher, stem.as_bytes());
    for (path, content) in sources {
        frame(&mut hasher, path.as_bytes());
        frame(&mut hasher, content.as_bytes());
    }
    frame(&mut hasher, compiler_stamp?.as_bytes());
    Some(hasher.finalize().into())
}

fn frame(hasher: &mut sha2::Sha256, bytes: &[u8]) {
    use sha2::Digest as _;
    hasher.update((bytes.len() as u64).to_le_bytes());
    hasher.update(bytes);
}

fn stamped_path(root: &Path, stem: &str, key: &[u8; 32]) -> PathBuf {
    let short: String = key[..8].iter().map(|byte| format!("{byte:02x}")).collect();
    root.join(format!("{stem}-{short}.bin"))
}

/// Read a cached payload for `stem` under `key` from the default cache
/// root. The full key is stored at the payload's head and must match.
pub fn load(stem: &str, key: &[u8; 32]) -> Option<Vec<u8>> {
    load_in(&cache_root()?, stem, key)
}

/// Read a cached payload from an explicit cache root.
pub fn load_in(root: &Path, stem: &str, key: &[u8; 32]) -> Option<Vec<u8>> {
    let path = stamped_path(root, stem, key);
    let data = std::fs::read(path).ok()?;
    let (stored, payload) = data.split_at_checked(32)?;
    if stored != key {
        return None;
    }
    Some(payload.to_vec())
}

/// Store a payload for `stem` under `key` in the default cache root.
/// Concurrent processes compute identical bytes: write to a
/// process-unique sibling and rename atomically.
pub fn store(stem: &str, key: &[u8; 32], payload: &[u8]) {
    let Some(root) = cache_root() else {
        return;
    };
    store_in(&root, stem, key, payload);
}

/// Store a payload in an explicit cache root, then bound the stem's
/// retained stamps to the newest few (CLEAN-05: several compiler
/// builds' caches coexist instead of every store deleting its
/// siblings).
pub fn store_in(root: &Path, stem: &str, key: &[u8; 32], payload: &[u8]) {
    let path = stamped_path(root, stem, key);
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
    prune_stamps(root, stem, &path);
}

/// Keep the newest `RETAIN_STAMPS` stamped files for `stem` (by
/// modification time, the just-written one first), remove the rest.
fn prune_stamps(root: &Path, stem: &str, _written: &Path) {
    let dir = match root.join(stem).parent().map(|path| path.to_path_buf()) {
        Some(dir) => dir,
        None => return,
    };
    let file_stem = stem.rsplit('/').next().unwrap_or(stem);
    let prefix = format!("{file_stem}-");
    let Ok(entries) = std::fs::read_dir(dir) else {
        return;
    };
    let mut stamped: Vec<(std::time::SystemTime, PathBuf)> = entries
        .flatten()
        .filter_map(|entry| {
            let name = entry.file_name();
            let name = name.to_string_lossy();
            if !name.starts_with(&prefix) || !name.ends_with(".bin") {
                return None;
            }
            let modified = entry.metadata().ok()?.modified().ok()?;
            Some((modified, entry.path()))
        })
        .collect();
    stamped.sort_by(|a, b| b.0.cmp(&a.0));
    for (_, path) in stamped.into_iter().skip(RETAIN_STAMPS) {
        let _ = std::fs::remove_file(path);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn distinct_input_sequences_never_collide() {
        // Unframed concatenation hashed ("ab", "c") and ("a", "bc")
        // identically; framing separates them.
        let left = key("stem", &[("ab", "c")], Some("stamp")).expect("key");
        let right = key("stem", &[("a", "bc")], Some("stamp")).expect("key");
        assert_ne!(left, right);
        // The stem and format version are key inputs too.
        let other_stem = key("other", &[("ab", "c")], Some("stamp")).expect("key");
        assert_ne!(left, other_stem);
    }

    #[test]
    fn round_trip_uses_the_injected_root() {
        let root = std::env::temp_dir().join(format!("talk-cache-test-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&root);
        let first = key("thing", &[("a.tlk", "let a = 1")], Some("stamp")).expect("key");
        store_in(&root, "thing", &first, b"payload");
        assert_eq!(load_in(&root, "thing", &first).as_deref(), Some(b"payload".as_slice()));
        // A different key does not read the entry.
        let second = key("thing", &[("a.tlk", "let a = 2")], Some("stamp")).expect("key");
        assert!(load_in(&root, "thing", &second).is_none());
        std::fs::remove_dir_all(&root).ok();
    }

    #[test]
    fn stores_retain_bounded_stamps() {
        let root = std::env::temp_dir().join(format!("talk-cache-prune-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&root);
        for index in 0..(RETAIN_STAMPS + 3) {
            let stamp = format!("stamp{index}");
            let key = key("thing", &[("a.tlk", "let a = 1")], Some(&stamp)).expect("key");
            store_in(&root, "thing", &key, b"payload");
            // Keep mtimes ordered on filesystems with coarse stamps.
            std::thread::sleep(std::time::Duration::from_millis(5));
        }
        let retained = std::fs::read_dir(&root)
            .expect("cache dir")
            .flatten()
            .filter(|entry| entry.file_name().to_string_lossy().ends_with(".bin"))
            .count();
        assert_eq!(retained, RETAIN_STAMPS, "old stamps are pruned, newest kept");
        std::fs::remove_dir_all(&root).ok();
    }
}
