//! Builtin packages: ordinary Talk packages bundled with the compiler.
//!
//! A bare `use name` activates them during parse discovery like the
//! stdlib modules they used to be, but they compile and cache through
//! the package library pipeline (ADR 0056) — each package's manifest
//! names its library target and dependencies, and the compiled image
//! replays from the shared disk cache. Each package registers under a
//! permanent `WellKnown` slot (absolute identity, ADR 0038): symbols
//! mint under these ids, so a slot never moves and a retired slot
//! never returns.
//!
//! The `Package` package is the one bootstrap special case: manifests
//! are written in its DSL, so its own compile must not parse a
//! manifest. It compiles manifest-free from its known library root and
//! still keys and caches like the rest.

use std::path::{Path, PathBuf};
use std::sync::{Arc, OnceLock};

use crate::compiling::module::{Module, ModuleEnvironment, ModuleId};
use crate::compiling::typed_program::TypedProgram;

struct BuiltinPackage {
    name: &'static str,
    /// The package's permanent `WellKnown` slot.
    slot: u16,
    /// The manifest-DSL bootstrap: compile from `library_source`
    /// without parsing the package's manifest.
    manifest_free: bool,
    /// The bundled package tree, paths relative to the package root.
    files: &'static [(&'static str, &'static str)],
}

const BUILTIN_PACKAGES: &[BuiltinPackage] = &[
    BuiltinPackage {
        name: "fs",
        slot: 0,
        manifest_free: false,
        files: &[
            ("package.tlk", include_str!("../../packages/fs/package.tlk")),
            ("src/fs.tlk", include_str!("../../packages/fs/src/fs.tlk")),
        ],
    },
    BuiltinPackage {
        name: "ansi",
        slot: 1,
        manifest_free: false,
        files: &[
            (
                "package.tlk",
                include_str!("../../packages/ansi/package.tlk"),
            ),
            (
                "src/ansi.tlk",
                include_str!("../../packages/ansi/src/ansi.tlk"),
            ),
        ],
    },
    BuiltinPackage {
        name: "testing",
        slot: 2,
        manifest_free: false,
        files: &[
            (
                "package.tlk",
                include_str!("../../packages/testing/package.tlk"),
            ),
            (
                "src/testing.tlk",
                include_str!("../../packages/testing/src/testing.tlk"),
            ),
        ],
    },
    BuiltinPackage {
        name: "Package",
        slot: 3,
        manifest_free: true,
        files: &[
            (
                "package.tlk",
                include_str!("../../packages/Package/package.tlk"),
            ),
            (
                "src/Package.tlk",
                include_str!("../../packages/Package/src/Package.tlk"),
            ),
        ],
    },
    BuiltinPackage {
        name: "syntax",
        slot: 4,
        manifest_free: false,
        files: &[
            (
                "package.tlk",
                include_str!("../../packages/syntax/package.tlk"),
            ),
            (
                "src/syntax.tlk",
                include_str!("../../packages/syntax/src/syntax.tlk"),
            ),
            (
                "src/Ast.tlk",
                include_str!("../../packages/syntax/src/Ast.tlk"),
            ),
            (
                "src/Docs.tlk",
                include_str!("../../packages/syntax/src/Docs.tlk"),
            ),
            (
                "src/Dump.tlk",
                include_str!("../../packages/syntax/src/Dump.tlk"),
            ),
            (
                "src/Lexer.tlk",
                include_str!("../../packages/syntax/src/Lexer.tlk"),
            ),
            (
                "src/Parser.tlk",
                include_str!("../../packages/syntax/src/Parser.tlk"),
            ),
            (
                "src/Syntax.tlk",
                include_str!("../../packages/syntax/src/Syntax.tlk"),
            ),
        ],
    },
    BuiltinPackage {
        name: "html",
        slot: 5,
        manifest_free: false,
        files: &[
            (
                "package.tlk",
                include_str!("../../packages/html/package.tlk"),
            ),
            (
                "src/Html.tlk",
                include_str!("../../packages/html/src/Html.tlk"),
            ),
            (
                "src/html.macro.tlk",
                include_str!("../../packages/html/src/html.macro.tlk"),
            ),
        ],
    },
    BuiltinPackage {
        name: "dict",
        slot: 6,
        manifest_free: false,
        files: &[
            (
                "package.tlk",
                include_str!("../../packages/dict/package.tlk"),
            ),
            (
                "src/dict.tlk",
                include_str!("../../packages/dict/src/dict.tlk"),
            ),
        ],
    },
    BuiltinPackage {
        name: "net",
        slot: 7,
        manifest_free: false,
        files: &[
            (
                "package.tlk",
                include_str!("../../packages/net/package.tlk"),
            ),
            (
                "src/net.tlk",
                include_str!("../../packages/net/src/net.tlk"),
            ),
        ],
    },
    BuiltinPackage {
        name: "os",
        slot: 8,
        manifest_free: false,
        files: &[
            ("package.tlk", include_str!("../../packages/os/package.tlk")),
            ("src/os.tlk", include_str!("../../packages/os/src/os.tlk")),
        ],
    },
    BuiltinPackage {
        name: "http",
        slot: 9,
        manifest_free: false,
        files: &[
            (
                "package.tlk",
                include_str!("../../packages/http/package.tlk"),
            ),
            (
                "src/http.tlk",
                include_str!("../../packages/http/src/http.tlk"),
            ),
        ],
    },
    BuiltinPackage {
        name: "task",
        slot: 10,
        manifest_free: false,
        files: &[
            (
                "package.tlk",
                include_str!("../../packages/task/package.tlk"),
            ),
            (
                "src/task.tlk",
                include_str!("../../packages/task/src/task.tlk"),
            ),
        ],
    },
    BuiltinPackage {
        name: "coop",
        slot: 11,
        manifest_free: false,
        files: &[
            (
                "package.tlk",
                include_str!("../../packages/coop/package.tlk"),
            ),
            (
                "src/coop.tlk",
                include_str!("../../packages/coop/src/coop.tlk"),
            ),
        ],
    },
];

struct CompiledBuiltin {
    module: Arc<Module>,
    typed: Arc<TypedProgram>,
    /// The library's disk-cache key: dependents close their keys over
    /// it (ADR 0056). `None` when the cache is unavailable.
    cache_key: Option<[u8; 32]>,
}

static COMPILED: OnceLock<Vec<OnceLock<CompiledBuiltin>>> = OnceLock::new();

std::thread_local! {
    /// The builtins currently compiling on this thread, so a manifest
    /// dependency cycle degrades to an unresolved import instead of
    /// recursing forever.
    static VISITING: std::cell::RefCell<Vec<&'static str>> = const { std::cell::RefCell::new(Vec::new()) };
}

fn slots() -> &'static [OnceLock<CompiledBuiltin>] {
    COMPILED.get_or_init(|| BUILTIN_PACKAGES.iter().map(|_| OnceLock::new()).collect())
}

fn package_at(name: &str) -> Option<(usize, &'static BuiltinPackage)> {
    BUILTIN_PACKAGES
        .iter()
        .enumerate()
        .find(|(_, package)| package.name == name)
}

pub(crate) fn name_for_module_id(module_id: ModuleId) -> Option<&'static str> {
    BUILTIN_PACKAGES
        .iter()
        .find(|package| ModuleId::WellKnown(package.slot) == module_id)
        .map(|package| package.name)
}

/// Every builtin package's import name and fixed id, for the analysis
/// layer's module-id table.
pub(crate) fn all() -> impl Iterator<Item = (&'static str, ModuleId)> {
    BUILTIN_PACKAGES
        .iter()
        .map(|package| (package.name, ModuleId::WellKnown(package.slot)))
}

/// The builtin package whose library sources a path belongs to: the
/// editor scopes such files into their own module session instead of
/// compiling them as user programs. Test sources under the package
/// stay out — they compile against the finished module.
#[cfg(not(target_family = "wasm"))]
pub(crate) fn module_name_for_path(path: &Path) -> Option<&'static str> {
    let path = path.canonicalize().ok()?;
    if path
        .file_name()
        .and_then(|name| name.to_str())
        .is_some_and(|name| name.ends_with(".test.tlk"))
    {
        return None;
    }
    for (index, package) in BUILTIN_PACKAGES.iter().enumerate() {
        let src = package_root(index).join("src");
        let Ok(src) = src.canonicalize() else {
            continue;
        };
        if path.starts_with(&src) && path.extension().is_some_and(|extension| extension == "tlk") {
            return Some(package.name);
        }
    }
    None
}

/// `module_name_for_path` for the browser build: builtin sources live
/// under the virtual `builtin/{name}/src/` prefix the bundled compile
/// stamps on them.
#[cfg(target_family = "wasm")]
pub(crate) fn module_name_for_path(path: &Path) -> Option<&'static str> {
    if path
        .file_name()
        .and_then(|name| name.to_str())
        .is_some_and(|name| name.ends_with(".test.tlk"))
    {
        return None;
    }
    let relative = path.strip_prefix("builtin").ok()?;
    let mut components = relative.components();
    let name = components.next()?.as_os_str().to_str()?;
    let (_, package) = package_at(name)?;
    (components.next()?.as_os_str() == "src"
        && path.extension().is_some_and(|extension| extension == "tlk"))
    .then_some(package.name)
}

/// The on-disk roots of every builtin package, for editor scoping
/// (which open documents belong to a builtin tree) and cache
/// invalidation on edits under one.
#[cfg(not(target_family = "wasm"))]
pub(crate) fn package_roots() -> impl Iterator<Item = (&'static str, &'static Path)> {
    BUILTIN_PACKAGES
        .iter()
        .enumerate()
        .map(|(index, package)| (package.name, package_root(index)))
}

/// Load one builtin package by import name: `None` when no builtin has
/// the name or its sources do not compile cleanly right now, so parse
/// discovery degrades to ordinary unresolved-import diagnostics.
/// Failures are not memoized; a later call retries.
pub(crate) fn try_compiled(name: &str) -> Option<(ModuleId, Arc<Module>, Arc<TypedProgram>)> {
    let (package, compiled) = try_entry(name)?;
    Some((
        ModuleId::WellKnown(package.slot),
        compiled.module.clone(),
        compiled.typed.clone(),
    ))
}

fn try_entry(name: &str) -> Option<(&'static BuiltinPackage, &'static CompiledBuiltin)> {
    let (index, package) = package_at(name)?;
    let slot = &slots()[index];
    if let Some(compiled) = slot.get() {
        return Some((package, compiled));
    }
    let cycles = VISITING.with(|visiting| visiting.borrow().contains(&package.name));
    if cycles {
        tracing::warn!(
            "builtin package {} depends on itself; not registering it",
            package.name
        );
        return None;
    }
    VISITING.with(|visiting| visiting.borrow_mut().push(package.name));
    let compiled = compile(index, package);
    VISITING.with(|visiting| {
        visiting.borrow_mut().pop();
    });
    let compiled = compiled?;
    Some((package, slot.get_or_init(|| compiled)))
}

/// The package's sources, for editor navigation into the module (the
/// analysis layer builds a workspace from these) and for the macro
/// host, which compiles macro units against the syntax sources. The
/// checkout's files win when present; the bundled texts back a missing
/// tree and the browser build.
pub(crate) fn source_documents(name: &str) -> Option<Vec<(PathBuf, String)>> {
    let (index, package) = package_at(name)?;

    #[cfg(not(target_family = "wasm"))]
    let root = package_root(index);
    #[cfg(target_family = "wasm")]
    let root = PathBuf::from("builtin").join(package.name);
    #[cfg(target_family = "wasm")]
    let _ = index;

    package
        .files
        .iter()
        .filter(|(path, _)| path.starts_with("src/") && path.ends_with(".tlk"))
        .map(|(path, bundled_text)| {
            let path = root.join(path);
            #[cfg(not(target_family = "wasm"))]
            let text = std::fs::read_to_string(&path).unwrap_or_else(|_| bundled_text.to_string());
            #[cfg(target_family = "wasm")]
            let text = bundled_text.to_string();
            #[cfg(not(target_family = "wasm"))]
            let path = path.canonicalize().unwrap_or(path);
            Some((path, text))
        })
        .collect()
}

/// The manifest-free library root: the package's single bundled source.
fn manifest_free_source(package: &BuiltinPackage) -> &'static str {
    package
        .files
        .iter()
        .map(|(path, _)| *path)
        .find(|path| path.starts_with("src/"))
        .expect("a manifest-free builtin bundles its library source")
}

/// The builtin's dependencies as its manifest declares them, with the
/// compiled artifacts to import: each must itself be a builtin. The
/// key vector is `None` when any dependency's own key is unavailable.
fn compiled_dependencies(
    package: &BuiltinPackage,
    dependencies: &[super::package::PackageDependency],
) -> Option<(Vec<(ModuleId, Arc<Module>)>, Option<Vec<[u8; 32]>>)> {
    let mut modules = Vec::with_capacity(dependencies.len());
    let mut keys = Some(Vec::with_capacity(dependencies.len()));
    for dependency in dependencies {
        let import_name = super::package::normalized_import_name(&dependency.package);
        let Some((dependency_package, compiled)) = try_entry(&import_name) else {
            tracing::warn!(
                "builtin package {} depends on {}, which is not a builtin package; not registering it",
                package.name,
                import_name,
            );
            return None;
        };
        modules.push((
            ModuleId::WellKnown(dependency_package.slot),
            compiled.module.clone(),
        ));
        match (&mut keys, compiled.cache_key) {
            (Some(keys), Some(key)) => keys.push(key),
            _ => keys = None,
        }
    }
    Some((modules, keys))
}

#[cfg(not(target_family = "wasm"))]
fn compile(index: usize, package: &'static BuiltinPackage) -> Option<CompiledBuiltin> {
    let root = package_root(index);
    compile_at(root, package, super::cache::cache_root().as_deref())
}

/// The on-disk root of the builtin package at `index` in
/// `BUILTIN_PACKAGES`, resolved once per process. The editor's
/// invalidation path asks on every file event, so resolution must not
/// hit the filesystem — or re-extract the bundled tree — per call.
#[cfg(not(target_family = "wasm"))]
fn package_root(index: usize) -> &'static Path {
    static ROOTS: OnceLock<Vec<PathBuf>> = OnceLock::new();
    &ROOTS.get_or_init(|| BUILTIN_PACKAGES.iter().map(resolve_package_root).collect())[index]
}

/// Where a builtin's tree lives: the repository's checkout when present
/// (a source build, whose edits should win), otherwise the bundled
/// tree extracted under the temp dir — the same arrangement the
/// bundled stdlib used for distributed binaries.
#[cfg(not(target_family = "wasm"))]
fn resolve_package_root(package: &BuiltinPackage) -> PathBuf {
    let source_root = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("packages")
        .join(package.name);
    if source_root.join("package.tlk").is_file() {
        return source_root;
    }
    extract_bundled(&std::env::temp_dir().join("talk-builtin-packages"), package)
}

/// Write the bundled package tree under `base`, returning its root.
#[cfg(not(target_family = "wasm"))]
fn extract_bundled(base: &Path, package: &BuiltinPackage) -> PathBuf {
    let root = base.join(package.name);
    for (name, content) in package.files {
        let path = root.join(name);
        if let Some(parent) = path.parent() {
            let _ = std::fs::create_dir_all(parent);
        }
        let _ = std::fs::write(path, content);
    }
    root
}

/// One builtin's compile through the package library pipeline (ADR
/// 0056), against an explicit cache root so tests can inject their own.
#[cfg(not(target_family = "wasm"))]
fn compile_at(
    root: &Path,
    package: &'static BuiltinPackage,
    cache_root: Option<&Path>,
) -> Option<CompiledBuiltin> {
    let (source, dependencies) = if package.manifest_free {
        (root.join(manifest_free_source(package)), Vec::new())
    } else {
        let manifest = match super::package::PackageManifest::read(root) {
            Ok(manifest) => manifest,
            Err(error) => {
                tracing::warn!(
                    "builtin package {} has an unreadable manifest: {error}; not registering it",
                    package.name
                );
                return None;
            }
        };
        if manifest.import_name() != package.name {
            tracing::warn!(
                "builtin package {} has a manifest naming {}; not registering it",
                package.name,
                manifest.import_name()
            );
            return None;
        }
        let library = manifest.library()?;
        let source = manifest.source_path(root, library).ok()?;
        (source, manifest.dependencies)
    };

    let (imports, dependency_keys) = compiled_dependencies(package, &dependencies)?;
    let mut environment = ModuleEnvironment::default();
    environment.import_core(super::core::compile());
    for (module_id, module) in imports {
        environment
            .import_compiled((*module).clone(), module_id)
            .ok()?;
    }
    let shared = Default::default();
    let compiled = super::package::cached_library(
        cache_root,
        &format!("builtin/{}", package.name),
        root,
        package.name,
        &source,
        ModuleId::WellKnown(package.slot),
        environment,
        &shared,
        dependency_keys.as_deref(),
    );
    match compiled {
        Ok(compiled) => Some(CompiledBuiltin {
            module: Arc::new(compiled.module),
            typed: compiled.typed,
            cache_key: compiled.cache_key,
        }),
        Err(error) => {
            tracing::warn!("builtin package {} does not compile: {error}", package.name);
            None
        }
    }
}

/// The browser build has no filesystem for the package pipeline to
/// read, so builtins compile from the bundled sources in memory — the
/// whole src tree as one unit, mirroring the driver configuration
/// `compile_library` produces from a root on disk.
#[cfg(target_family = "wasm")]
fn compile(_index: usize, package: &'static BuiltinPackage) -> Option<CompiledBuiltin> {
    use crate::compiling::driver::{CompilationMode, Driver, DriverConfig, Source};

    let dependencies = if package.manifest_free {
        Vec::new()
    } else {
        let (_, manifest_text) = package
            .files
            .iter()
            .find(|(path, _)| *path == "package.tlk")?;
        let manifest_path = PathBuf::from("builtin")
            .join(package.name)
            .join("package.tlk");
        let manifest =
            super::package::PackageManifest::parse(&manifest_path, manifest_text).ok()?;
        if manifest.import_name() != package.name {
            return None;
        }
        manifest.dependencies
    };
    let (imports, _) = compiled_dependencies(package, &dependencies)?;

    let source_root = PathBuf::from("builtin").join(package.name).join("src");
    let sources: Vec<Source> = package
        .files
        .iter()
        .filter(|(path, _)| {
            path.starts_with("src/")
                && path.ends_with(".tlk")
                && !path.ends_with(crate::procedural_macros::MACRO_SUFFIX)
        })
        .map(|(path, content)| {
            Source::in_memory(
                PathBuf::from("builtin").join(package.name).join(path),
                content.to_string(),
            )
        })
        .collect();
    let macro_sources: Vec<(&'static str, &'static str)> = package
        .files
        .iter()
        .filter(|(path, _)| path.ends_with(crate::procedural_macros::MACRO_SUFFIX))
        .copied()
        .collect();

    let mut environment = ModuleEnvironment::default();
    environment.import_core(super::core::compile());
    for (module_id, module) in imports {
        environment
            .import_compiled((*module).clone(), module_id)
            .ok()?;
    }
    let mut config = DriverConfig::new(package.name);
    config.module_id = ModuleId::WellKnown(package.slot);
    config.mode = CompilationMode::Library;
    config.modules = std::rc::Rc::new(environment);
    config.source_root = Some(source_root);
    if !macro_sources.is_empty() {
        config.embedded_macro_sources = Some(macro_sources);
    }
    let driver = Driver::new_bare(sources, config);
    let typed = driver.parse().ok()?.resolve_names().ok()?.type_check();
    if typed.has_errors() {
        return None;
    }
    let program = Arc::new(typed.phase.program.clone());
    Some(CompiledBuiltin {
        module: Arc::new(typed.module(package.name)),
        typed: program,
        cache_key: None,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn well_known_slots_are_permanent() {
        // Absolute identity (ADR 0038): these ids are minted into
        // symbols and persisted artifacts, so a slot never moves and a
        // retired slot never returns.
        let expected: &[(&str, u16)] = &[
            ("fs", 0),
            ("ansi", 1),
            ("testing", 2),
            ("Package", 3),
            ("syntax", 4),
            ("html", 5),
            ("dict", 6),
            ("net", 7),
            ("os", 8),
            ("http", 9),
            ("task", 10),
            ("coop", 11),
        ];
        assert_eq!(BUILTIN_PACKAGES.len(), expected.len());
        for (name, slot) in expected {
            let (_, package) = package_at(name).expect("builtin is registered");
            assert_eq!(
                package.slot, *slot,
                "builtin package {name} moved off its permanent slot {slot}"
            );
        }
    }

    #[test]
    fn every_builtin_compiles_under_its_slot() {
        for package in BUILTIN_PACKAGES {
            let (id, module, typed) =
                try_compiled(package.name).unwrap_or_else(|| panic!("{} compiles", package.name));
            assert_eq!(id, ModuleId::WellKnown(package.slot));
            assert!(
                !module.exports.is_empty(),
                "builtin package {} exports nothing",
                package.name
            );
            assert!(!typed.symbol_names().is_empty());
        }
    }

    #[test]
    fn dependent_builtins_record_their_edges() {
        // The canonical module graph (CLEAN-03): a builtin compiled
        // against its manifest dependencies carries those edges, which
        // the backend's body closure walks.
        let dependencies_of = |name: &str| {
            let (_, module, _) = try_compiled(name).expect("builtin compiles");
            module
                .dependencies
                .iter()
                .filter_map(|id| name_for_module_id(*id))
                .collect::<Vec<_>>()
        };
        assert_eq!(dependencies_of("testing"), vec!["ansi"]);
        assert_eq!(dependencies_of("http"), vec!["net"]);
        assert_eq!(dependencies_of("fs"), vec!["os"]);
    }

    #[test]
    fn unknown_names_are_not_builtins() {
        assert!(try_compiled("no_such_builtin").is_none());
        assert!(name_for_module_id(ModuleId::WellKnown(12)).is_none());
    }

    #[test]
    fn syntax_exports_span_every_source_file() {
        // The aggregator root pulls each tip file into the compile
        // closure; a symbol from every file proves the whole tree
        // rides in the module.
        let (_, module, _) = try_compiled("syntax").expect("syntax compiles");
        for export in [
            "parse_file_source",    // Parser.tlk
            "Decl",                 // Ast.tlk
            "Comment",              // Lexer.tlk
            "collect_doc_comments", // Docs.tlk
            "parse",                // Dump.tlk
            "SyntaxScope",          // Syntax.tlk
        ] {
            assert!(
                module.exports.contains_key(export),
                "syntax should export {export}"
            );
        }
    }

    #[test]
    fn images_round_trip_through_an_injected_cache_root() {
        let (index, package) = package_at("dict").expect("dict is registered");
        let root = package_root(index);
        let cache =
            std::env::temp_dir().join(format!("talk-builtin-cache-test-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&cache);
        let compiled = compile_at(root, package, Some(&cache)).expect("dict compiles");
        let key = compiled.cache_key.expect("dict's inputs are keyable");
        let replayed = compile_at(root, package, Some(&cache)).expect("dict replays");
        std::fs::remove_dir_all(&cache).ok();
        assert_eq!(replayed.cache_key, Some(key));
        assert_eq!(replayed.module.name, compiled.module.name);
        assert_eq!(replayed.module.exports.len(), compiled.module.exports.len());
    }

    #[test]
    fn package_roots_are_memoized() {
        // The editor's invalidation path asks for the roots on every
        // file event: resolution happens once and the same allocations
        // are handed back after that.
        let first: Vec<&'static Path> = package_roots().map(|(_, root)| root).collect();
        let second: Vec<&'static Path> = package_roots().map(|(_, root)| root).collect();
        for (a, b) in first.iter().zip(&second) {
            assert!(std::ptr::eq(*a, *b), "package roots resolve once");
        }
        for (package, root) in BUILTIN_PACKAGES.iter().zip(&first) {
            assert!(
                root.join("package.tlk").is_file(),
                "{} root carries its manifest",
                package.name
            );
        }
    }

    #[test]
    fn bundled_extraction_writes_the_package_tree() {
        // The no-checkout fallback (distributed binaries): the bundled
        // tree lands under the base intact, manifest included.
        let base =
            std::env::temp_dir().join(format!("talk-builtin-extract-test-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&base);
        let (_, package) = package_at("syntax").expect("syntax is registered");
        let root = extract_bundled(&base, package);
        assert_eq!(root, base.join("syntax"));
        for (name, content) in package.files {
            assert_eq!(
                &std::fs::read_to_string(root.join(name)).expect("extracted file"),
                content,
                "extracted {name} matches the bundled text"
            );
        }
        std::fs::remove_dir_all(&base).ok();
    }

    #[test]
    fn dependent_keys_close_over_dependency_keys() {
        // testing's key folds ansi's in (ADR 0056), so the two never
        // collide and an ansi edit invalidates testing's image.
        let (_, testing) = try_entry("testing").expect("testing compiles");
        let (_, ansi) = try_entry("ansi").expect("ansi compiles");
        let testing_key = testing.cache_key.expect("testing is keyable");
        let ansi_key = ansi.cache_key.expect("ansi is keyable");
        assert_ne!(testing_key, ansi_key);
    }

    #[test]
    fn source_documents_cover_the_package_sources() {
        let documents = source_documents("syntax").expect("syntax sources");
        assert_eq!(documents.len(), 7);
        assert!(
            documents
                .iter()
                .any(|(path, _)| path.ends_with("src/Parser.tlk"))
        );
        let dict = source_documents("dict").expect("dict sources");
        assert_eq!(dict.len(), 1);
        assert!(dict[0].1.contains("pub struct Dict"));
    }
}
