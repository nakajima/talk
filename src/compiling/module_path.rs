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
        let mut target = self.resolve_base(source_path, module_path)?;
        target.set_extension("tlk");
        Some(target)
    }

    /// Resolves a module path to its extensionless filesystem base:
    /// `<base>.tlk` names the module file and `<base>/` its submodule
    /// directory. Glob imports (`use package::foo::*`) match both.
    pub fn resolve_base(&self, source_path: &str, module_path: &str) -> Option<PathBuf> {
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
                // `self`/`super` are relative to the importing file. When
                // the file lives under the source root, anchor there (the
                // usual case); when it lives outside it (a package test
                // under tests/ while `package::` anchors at src/), anchor
                // at the file's own directory.
                let (base, mut current_module) = match source.strip_prefix(&self.source_root) {
                    Ok(source_relative) => {
                        (self.source_root.clone(), source_relative.with_extension(""))
                    }
                    Err(_)
                        if self.source_root.as_os_str().is_empty()
                            || self.source_root == Path::new(".") =>
                    {
                        (self.source_root.clone(), source.with_extension(""))
                    }
                    Err(_) => (
                        source.parent()?.to_path_buf(),
                        PathBuf::from(source.file_stem()?),
                    ),
                };

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

                base.join(current_module)
            }
            _ => return None,
        };

        if tail.is_empty() {
            return None;
        }
        for segment in tail {
            target.push(segment);
        }
        Some(target)
    }

    /// Expands a glob import base to its member source files: `<base>.tlk`
    /// when it exists plus every `.tlk` file under the `<base>/`
    /// directory, recursively. The result is sorted so discovery order
    /// is deterministic.
    pub fn expand_glob(base: &Path) -> Vec<PathBuf> {
        let mut members = Vec::new();
        let module_file = base.with_extension("tlk");
        if module_file.is_file() {
            members.push(module_file);
        }
        if base.is_dir() {
            Self::walk_glob_dir(base, &mut members);
        }
        members.sort();
        members
    }

    fn walk_glob_dir(dir: &Path, members: &mut Vec<PathBuf>) {
        let Ok(entries) = std::fs::read_dir(dir) else {
            return;
        };
        for entry in entries.flatten() {
            let path = entry.path();
            let Ok(file_type) = entry.file_type() else {
                continue;
            };
            if file_type.is_dir() {
                Self::walk_glob_dir(&path, members);
            } else if path.extension().and_then(|ext| ext.to_str()) == Some("tlk") {
                members.push(path);
            }
        }
    }

    /// Whether `path` belongs to the glob import rooted at `base`: the
    /// module file itself or a `.tlk` file under the module directory.
    /// Mirrors `expand_glob` for sources that never touch disk.
    pub fn glob_member(base: &Path, path: &Path) -> bool {
        let is_module_file = path == base.with_extension("tlk");
        let is_tree_member = path.extension().and_then(|ext| ext.to_str()) == Some("tlk")
            && path.starts_with(base);
        is_module_file || is_tree_member
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
