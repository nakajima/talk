//! Package-aware source discovery shared by `talk check` and the LSP.

use std::path::{Path, PathBuf};

use ignore::WalkBuilder;

/// The `.tlk` files that make up the program rooted at `root`. A
/// package manifest scopes the program: only the manifest and files
/// under its build targets' source directories compile together, the
/// same set `talk test` and `talk run` use. Stray .tlk files elsewhere
/// under the folder (scratch, stale copies) are not part of the
/// program, and their diagnostics must not gate the real ones.
pub fn workspace_source_files(root: &Path) -> Vec<PathBuf> {
    let source_roots: Option<Vec<PathBuf>> = crate::compiling::package::PackageManifest::read(root)
        .ok()
        .map(|manifest| {
            manifest
                .builds
                .iter()
                .filter_map(|artifact| match artifact {
                    crate::compiling::package::PackageArtifact::Library { from }
                    | crate::compiling::package::PackageArtifact::Binary { from, .. } => {
                        root.join(from).parent().map(std::path::Path::to_path_buf)
                    }
                })
                .collect()
        });
    let in_scope = |path: &Path| match &source_roots {
        Some(roots) => {
            path.parent() == Some(root)
                && path.file_name().and_then(|n| n.to_str()) == Some("package.tlk")
                || roots.iter().any(|src| path.starts_with(src))
        }
        None => true,
    };

    let mut result = Vec::new();

    for entry in WalkBuilder::new(root).build() {
        let Ok(entry) = entry else {
            continue;
        };

        if !entry.file_type().is_some_and(|t| t.is_file()) {
            continue;
        }

        let path = entry.path();
        if path.extension().and_then(|e| e.to_str()) == Some("tlk") && in_scope(path) {
            result.push(path.to_path_buf());
        }
    }

    result
}
