//! The one path from a command's file arguments to a compile.
//!
//! Every CLI command that compiles user input resolves it here first,
//! so a file inside a package always compiles against the locked
//! dependency graph -- no command can wire up its own driver and
//! silently lose the package context.

use std::path::{Path, PathBuf};
use std::sync::Arc;

use super::driver::{Driver, DriverConfig, Source, Typed};
use super::package::{PackageError, PackageProject, typecheck_driver};

const STDIN_NAME: &str = "<stdin>";
const OFFLINE_NEEDS_PACKAGE: &str = "--offline requires package execution";

/// What a command's file arguments mean, resolved the same way for
/// every command: `check`, `run`, and `build` all follow these rules.
pub enum CompileInvocation {
    /// Explicit sources inside a package: the fused compile against
    /// the locked dependency graph -- exactly what `talk check`
    /// diagnoses.
    PackageSources {
        project: PackageProject,
        sources: Vec<Source>,
    },
    /// The package itself -- no filenames inside one, or its root
    /// directory as the argument: the manifest's binary target.
    PackageTarget { project: PackageProject },
    /// No enclosing package: stdin and loose files compile bare.
    Loose { sources: Vec<Source> },
}

impl CompileInvocation {
    /// Resolve file arguments against the filesystem. `current_dir`
    /// anchors the no-filename form; `stdin` supplies the text for `-`
    /// (and the empty form outside a package) and is read at most
    /// once. Stdin stays dependency-free, so any `-` keeps the whole
    /// invocation loose.
    pub fn resolve(
        current_dir: impl AsRef<Path>,
        filenames: &[String],
        offline: bool,
        mut stdin: impl FnMut() -> String,
    ) -> Result<Self, PackageError> {
        if filenames.is_empty() {
            return match PackageProject::enclosing_root(current_dir) {
                Some(root) => Ok(Self::PackageTarget {
                    project: PackageProject::open_at(root, offline)?,
                }),
                None if offline => Err(PackageError::Resolution(OFFLINE_NEEDS_PACKAGE.into())),
                None => Ok(Self::Loose {
                    sources: vec![Source::in_memory(PathBuf::from(STDIN_NAME), stdin())],
                }),
            };
        }
        if filenames.iter().any(|filename| filename == "-") {
            if offline {
                return Err(PackageError::Resolution(OFFLINE_NEEDS_PACKAGE.into()));
            }
            let text: Arc<str> = stdin().into();
            return Ok(Self::Loose {
                sources: filenames
                    .iter()
                    .map(|filename| {
                        if filename == "-" {
                            Source::in_memory(PathBuf::from(STDIN_NAME), text.clone())
                        } else {
                            Source::from(PathBuf::from(filename))
                        }
                    })
                    .collect(),
            });
        }
        if let [path] = filenames
            && PackageProject::exists_at(Path::new(path))
        {
            return Ok(Self::PackageTarget {
                project: PackageProject::open_at(Path::new(path), offline)?,
            });
        }
        let sources = filenames
            .iter()
            .map(|filename| Source::from(PathBuf::from(filename)))
            .collect();
        match filenames
            .first()
            .and_then(|filename| PackageProject::enclosing_root(filename))
        {
            Some(root) => Ok(Self::PackageSources {
                project: PackageProject::open_at(root, offline)?,
                sources,
            }),
            None if offline => Err(PackageError::Resolution(OFFLINE_NEEDS_PACKAGE.into())),
            None => Ok(Self::Loose { sources }),
        }
    }

    /// Whether the invocation compiles as a package.
    pub fn is_package(&self) -> bool {
        !matches!(self, Self::Loose { .. })
    }

    /// Typecheck the invocation. Package variants compile against the
    /// locked graph, and every failure arrives as source-annotated
    /// diagnostics. `bin` selects a package binary target and is an
    /// error anywhere it cannot mean one.
    pub fn typecheck(self, bin: Option<&str>) -> Result<Driver<Typed>, PackageError> {
        if bin.is_some() && !matches!(self, Self::PackageTarget { .. }) {
            return Err(PackageError::Resolution(
                "--bin selects a package binary; pass the package root instead of source files"
                    .into(),
            ));
        }
        match self {
            Self::PackageTarget { project } => project.typecheck_binary(bin),
            Self::PackageSources { project, sources } => project.typecheck_sources(sources),
            Self::Loose { sources } => {
                typecheck_driver(Driver::new(sources, DriverConfig::new("Main")))
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs;
    use std::sync::atomic::{AtomicUsize, Ordering};

    static TEMP_COUNTER: AtomicUsize = AtomicUsize::new(0);

    fn temp_dir(label: &str) -> PathBuf {
        let dir = std::env::temp_dir().join(format!(
            "talk-invocation-{label}-{}-{}",
            std::process::id(),
            TEMP_COUNTER.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir_all(&dir).expect("create temp dir");
        dir
    }

    fn no_stdin() -> String {
        panic!("stdin must not be read");
    }

    /// A root package whose binary imports a locked path dependency.
    fn package_with_dependency(dir: &Path) -> PathBuf {
        let dependency = dir.join("dependency");
        let root = dir.join("root");
        fs::create_dir_all(dependency.join("src")).expect("create dependency source");
        fs::create_dir_all(root.join("src")).expect("create root source");
        fs::write(
            dependency.join("package.tlk"),
            "Package(name: \"local-lib\", version: \"0.1.0\", description: \"\", builds: [.lib(from: \"src/lib.tlk\")], dependencies: [])",
        )
        .expect("write dependency manifest");
        fs::write(
            dependency.join("src/lib.tlk"),
            "pub func answer() -> Int { 42 }",
        )
        .expect("write dependency source");
        fs::write(
            root.join("package.tlk"),
            "Package(name: \"root\", version: \"0.1.0\", description: \"\", builds: [.bin(named: \"main\", from: \"src/main.tlk\")], dependencies: [.path(package: \"local-lib\", path: \"../dependency\")])",
        )
        .expect("write root manifest");
        fs::write(
            root.join("src/main.tlk"),
            "use local_lib::{ answer }\nprint(answer())\n",
        )
        .expect("write root source");
        PackageProject::install_at(&root, true, false).expect("install path dependency");
        root
    }

    #[test]
    fn explicit_package_sources_compile_against_the_locked_graph() {
        let dir = temp_dir("explicit");
        let root = package_with_dependency(&dir);
        let file = root.join("src/main.tlk").to_string_lossy().into_owned();
        let invocation =
            CompileInvocation::resolve(&dir, &[file], false, no_stdin).expect("resolve");
        assert!(matches!(
            invocation,
            CompileInvocation::PackageSources { .. }
        ));
        invocation
            .typecheck(None)
            .expect("dependency imports resolve");
        fs::remove_dir_all(dir).expect("remove temp dir");
    }

    #[test]
    fn a_package_root_argument_selects_the_manifest_binary() {
        let dir = temp_dir("root-arg");
        let root = package_with_dependency(&dir);
        let argument = root.to_string_lossy().into_owned();
        let invocation =
            CompileInvocation::resolve(&dir, &[argument], false, no_stdin).expect("resolve");
        assert!(matches!(invocation, CompileInvocation::PackageTarget { .. }));
        invocation.typecheck(None).expect("binary target compiles");
        fs::remove_dir_all(dir).expect("remove temp dir");
    }

    #[test]
    fn no_filenames_inside_a_package_select_its_binary() {
        let dir = temp_dir("walk-up");
        let root = package_with_dependency(&dir);
        let invocation = CompileInvocation::resolve(root.join("src"), &[], false, no_stdin)
            .expect("resolve walks up to the package root");
        assert!(matches!(invocation, CompileInvocation::PackageTarget { .. }));
        fs::remove_dir_all(dir).expect("remove temp dir");
    }

    #[test]
    fn loose_files_outside_a_package_compile_bare() {
        let dir = temp_dir("loose");
        let file = dir.join("script.tlk");
        fs::write(&file, "print(40 + 2)\n").expect("write script");
        let invocation = CompileInvocation::resolve(
            &dir,
            &[file.to_string_lossy().into_owned()],
            false,
            no_stdin,
        )
        .expect("resolve");
        assert!(matches!(invocation, CompileInvocation::Loose { .. }));
        invocation.typecheck(None).expect("bare compile succeeds");
        fs::remove_dir_all(dir).expect("remove temp dir");
    }

    #[test]
    fn stdin_stays_dependency_free_even_inside_a_package() {
        let dir = temp_dir("stdin");
        let root = package_with_dependency(&dir);
        let invocation =
            CompileInvocation::resolve(&root, &["-".into()], false, || "print(1)\n".to_string())
                .expect("resolve");
        assert!(matches!(invocation, CompileInvocation::Loose { .. }));
        invocation.typecheck(None).expect("stdin compiles bare");
        fs::remove_dir_all(dir).expect("remove temp dir");
    }

    #[test]
    fn offline_without_a_package_is_rejected_before_reading_stdin() {
        let dir = temp_dir("offline");
        let Err(error) = CompileInvocation::resolve(&dir, &[], true, no_stdin) else {
            panic!("offline needs a package");
        };
        assert!(error.to_string().contains("--offline"));
        fs::remove_dir_all(dir).expect("remove temp dir");
    }

    #[test]
    fn compile_errors_surface_as_source_diagnostics() {
        let dir = temp_dir("diagnostics");
        let root = package_with_dependency(&dir);
        let broken = root.join("src/broken.tlk");
        fs::write(&broken, "func broken() -> Int {\n\t\"nope\"\n}\n").expect("write broken");
        let invocation = CompileInvocation::resolve(
            &dir,
            &[broken.to_string_lossy().into_owned()],
            false,
            no_stdin,
        )
        .expect("resolve");
        let Err(error) = invocation.typecheck(None) else {
            panic!("type error fails the compile");
        };
        let PackageError::CompileDiagnostics(diagnostics) = error else {
            panic!("expected source diagnostics, got {error}");
        };
        assert!(
            diagnostics
                .entries
                .iter()
                .any(|entry| entry.document_id.ends_with("broken.tlk"))
        );
        fs::remove_dir_all(dir).expect("remove temp dir");
    }

    #[test]
    fn selecting_a_binary_needs_a_package_target() {
        let dir = temp_dir("bin-flag");
        let file = dir.join("script.tlk");
        fs::write(&file, "print(1)\n").expect("write script");
        let invocation = CompileInvocation::resolve(
            &dir,
            &[file.to_string_lossy().into_owned()],
            false,
            no_stdin,
        )
        .expect("resolve");
        let Err(error) = invocation.typecheck(Some("app")) else {
            panic!("--bin needs a package");
        };
        assert!(error.to_string().contains("--bin"));
        fs::remove_dir_all(dir).expect("remove temp dir");
    }
}
