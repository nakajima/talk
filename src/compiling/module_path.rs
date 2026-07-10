use std::path::{Path, PathBuf};

/// Maps source-level local module paths to their source files.
#[derive(Clone, Debug)]
pub struct LocalModulePaths {
    source_root: PathBuf,
}

impl LocalModulePaths {
    pub fn new(source_root: impl Into<PathBuf>) -> Self {
        Self {
            source_root: source_root.into(),
        }
    }

    pub fn source_root(&self) -> &Path {
        &self.source_root
    }

    pub fn is_local(path: &str) -> bool {
        matches!(path.split("::").next(), Some("package" | "self" | "super"))
    }

    /// Resolves a `package`, `self`, or `super` path to a `.tlk` source file.
    pub fn resolve(&self, source_path: &str, module_path: &str) -> Option<PathBuf> {
        let mut segments = module_path.split("::");
        let anchor = segments.next()?;
        let mut tail: Vec<&str> = segments.collect();
        if tail.iter().any(|segment| segment.is_empty()) {
            return None;
        }

        let source = Path::new(source_path);
        let mut target = match anchor {
            "package" => self.source_root.clone(),
            "self" | "super" => {
                let source_relative =
                    source.strip_prefix(&self.source_root).ok().or_else(|| {
                        (self.source_root.as_os_str().is_empty()
                            || self.source_root == Path::new("."))
                        .then_some(source)
                    })?;
                let mut current_module = source_relative.with_extension("");

                if anchor == "super" {
                    while tail.first() == Some(&"super") {
                        tail.remove(0);
                        if !current_module.pop() {
                            return None;
                        }
                    }
                    if !current_module.pop() {
                        return None;
                    }
                }

                self.source_root.join(current_module)
            }
            _ => return None,
        };

        if tail.is_empty() {
            return None;
        }
        for segment in tail {
            target.push(segment);
        }
        target.set_extension("tlk");
        Some(target)
    }

    pub fn infer_source_root(paths: impl IntoIterator<Item = PathBuf>) -> Option<PathBuf> {
        paths
            .into_iter()
            .filter_map(|path| path.parent().map(Path::to_path_buf))
            .reduce(|root, path| common_ancestor(&root, &path))
    }
}

fn common_ancestor(left: &Path, right: &Path) -> PathBuf {
    let mut common = PathBuf::new();
    for (left_component, right_component) in left.components().zip(right.components()) {
        if left_component != right_component {
            break;
        }
        common.push(left_component.as_os_str());
    }
    common
}
