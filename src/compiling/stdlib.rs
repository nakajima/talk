use std::path::{Path, PathBuf};
use std::rc::Rc;
use std::sync::{Arc, OnceLock};

use rustc_hash::FxHashMap;

use crate::compiling::{
    driver::{CompilationMode, Driver, DriverConfig, Source, Typed},
    module::{Module, ModuleEnvironment, ModuleId},
};

const TALK_STDLIB_PATH_ENV: &str = "TALK_STDLIB_PATH";

pub const STDLIB_SOURCE_NAMES: &[&str] = &[
    "fs.tlk",
    "ansi.tlk",
    "testing.tlk",
    "Package.tlk",
    "syntax/Dump.tlk",
    "html/Html.tlk",
    "dict.tlk",
    "net.tlk",
    "os.tlk",
    "http.tlk",
];

const STDLIB_MODULES: &[(&str, &str, &str)] = &[
    ("fs", "fs.tlk", include_str!("../../stdlib/fs.tlk")),
    ("ansi", "ansi.tlk", include_str!("../../stdlib/ansi.tlk")),
    (
        "testing",
        "testing.tlk",
        include_str!("../../stdlib/testing.tlk"),
    ),
    (
        "Package",
        "Package.tlk",
        include_str!("../../stdlib/Package.tlk"),
    ),
    (
        "syntax",
        "syntax/Dump.tlk",
        include_str!("../../stdlib/syntax/Dump.tlk"),
    ),
    (
        "html",
        "html/Html.tlk",
        include_str!("../../stdlib/html/Html.tlk"),
    ),
    ("dict", "dict.tlk", include_str!("../../stdlib/dict.tlk")),
    ("net", "net.tlk", include_str!("../../stdlib/net.tlk")),
    ("os", "os.tlk", include_str!("../../stdlib/os.tlk")),
    ("http", "http.tlk", include_str!("../../stdlib/http.tlk")),
];

const STDLIB_FILES: &[(&str, &str)] = &[
    ("fs.tlk", include_str!("../../stdlib/fs.tlk")),
    ("ansi.tlk", include_str!("../../stdlib/ansi.tlk")),
    ("testing.tlk", include_str!("../../stdlib/testing.tlk")),
    ("Package.tlk", include_str!("../../stdlib/Package.tlk")),
    (
        "syntax/Ast.tlk",
        include_str!("../../stdlib/syntax/Ast.tlk"),
    ),
    (
        "syntax/Dump.tlk",
        include_str!("../../stdlib/syntax/Dump.tlk"),
    ),
    (
        "syntax/Lexer.tlk",
        include_str!("../../stdlib/syntax/Lexer.tlk"),
    ),
    (
        "syntax/Parser.tlk",
        include_str!("../../stdlib/syntax/Parser.tlk"),
    ),
    (
        "syntax/Syntax.tlk",
        include_str!("../../stdlib/syntax/Syntax.tlk"),
    ),
    ("html/Html.tlk", include_str!("../../stdlib/html/Html.tlk")),
    (
        "html/html.macro.tlk",
        include_str!("../../stdlib/html/html.macro.tlk"),
    ),
    ("dict.tlk", include_str!("../../stdlib/dict.tlk")),
    ("net.tlk", include_str!("../../stdlib/net.tlk")),
    ("os.tlk", include_str!("../../stdlib/os.tlk")),
    ("http.tlk", include_str!("../../stdlib/http.tlk")),
];

static STDLIB: OnceLock<Vec<OnceLock<CompiledStdlib>>> = OnceLock::new();
// The syntax runtime module remains lazy for ordinary source imports. A
// stdlib-owned procedural macro may still compile against the syntax sources
// while its owning module artifact is built.
static SYNTAX: OnceLock<CompiledStdlib> = OnceLock::new();

pub fn path_override() -> Option<PathBuf> {
    std::env::var_os(TALK_STDLIB_PATH_ENV)
        .filter(|path| !path.is_empty())
        .map(|path| {
            let path = PathBuf::from(path);
            path.canonicalize().unwrap_or(path)
        })
}

/// All bundled stdlib module roots, in a fixed order.
pub fn stdlib_sources() -> Vec<(&'static str, &'static str)> {
    STDLIB_MODULES
        .iter()
        .map(|(name, _, text)| (*name, *text))
        .collect()
}

pub fn module_name_for_path(path: &Path) -> Option<&'static str> {
    #[cfg(target_family = "wasm")]
    let relative = path.strip_prefix("stdlib").ok()?;

    #[cfg(not(target_family = "wasm"))]
    let relative = {
        let source_path = path.canonicalize().ok()?;
        let stdlib_dir = active_stdlib_dir().canonicalize().ok()?;
        source_path.strip_prefix(stdlib_dir).ok()?.to_path_buf()
    };

    for (name, source, _) in STDLIB_MODULES {
        if relative == Path::new(source) {
            return Some(name);
        }
    }
    if relative.starts_with("syntax")
        && relative
            .extension()
            .is_some_and(|extension| extension == "tlk")
    {
        return Some("syntax");
    }
    None
}

pub fn source_documents(name: &str) -> Option<Vec<(PathBuf, String)>> {
    let (_, root_source, _) = STDLIB_MODULES
        .iter()
        .find(|(module_name, _, _)| *module_name == name)?;
    let files: Vec<(&str, &str)> = if name == "syntax" {
        STDLIB_FILES
            .iter()
            .filter(|(path, _)| Path::new(path).starts_with("syntax"))
            .copied()
            .collect()
    } else {
        STDLIB_FILES
            .iter()
            .filter(|(path, _)| path == root_source)
            .copied()
            .collect()
    };

    if let Some(stdlib_dir) = path_override() {
        return files
            .into_iter()
            .map(|(filename, _)| {
                let path = stdlib_dir.join(filename);
                let text = std::fs::read_to_string(&path).ok()?;
                let path = path.canonicalize().unwrap_or(path);
                Some((path, text))
            })
            .collect();
    }

    let repository_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("stdlib");
    let relative_dir = PathBuf::from("stdlib");
    let bundled_dir = bundled_compilation_dir();
    files
        .into_iter()
        .map(|(filename, bundled_text)| {
            for candidate in [repository_dir.join(filename), relative_dir.join(filename)] {
                if candidate.is_file()
                    && let Ok(path) = candidate.canonicalize()
                {
                    let text =
                        std::fs::read_to_string(&path).unwrap_or_else(|_| bundled_text.to_string());
                    return Some((path, text));
                }
            }
            let path = bundled_dir.join(filename);
            let text = std::fs::read_to_string(&path).unwrap_or_else(|_| bundled_text.to_string());
            Some((path, text))
        })
        .collect()
}

/// The fixed id of a stdlib module: `WellKnown(index)` in
/// `stdlib_sources` order. Stdlib modules mint their symbols under
/// these ids (absolute identity, ADR 0038), so every session registers
/// them at the same ids and no artifact is ever respelled.
fn module_id_for_index(index: usize) -> ModuleId {
    ModuleId::WellKnown(u16::try_from(index).expect("stdlib module count fits the reserved band"))
}

/// The stdlib module a fixed id names: the inverse of
/// `module_id_for_index`.
pub(crate) fn name_for_module_id(module_id: ModuleId) -> Option<&'static str> {
    STDLIB_MODULES
        .iter()
        .enumerate()
        .find(|(index, _)| module_id_for_index(*index) == module_id)
        .map(|(_, (name, _, _))| *name)
}

/// The fixed id a stdlib module registers under, by public import name.
pub(crate) fn module_id_for_name(name: &str) -> Option<ModuleId> {
    STDLIB_MODULES
        .iter()
        .position(|(candidate, _, _)| *candidate == name)
        .map(module_id_for_index)
}

/// Load one stdlib module by its public import name, compiling only that
/// module. The driver uses this after parsing imports to activate modules
/// that are intentionally lazy.
pub fn module_with_id(name: &str) -> Option<(ModuleId, Arc<Module>)> {
    let index = STDLIB_MODULES
        .iter()
        .position(|(candidate, _, _)| *candidate == name)?;
    let (_, module, _) = compiled_at(index);
    Some((module_id_for_index(index), module.clone()))
}

/// `module_with_id` for editor sessions: `None` when the module's
/// current sources do not compile cleanly (mid-edit), so sessions
/// degrade to ordinary unresolved-import diagnostics instead of
/// panicking inside parse discovery.
pub fn try_module_with_id(name: &str) -> Option<(ModuleId, Arc<Module>)> {
    let index = STDLIB_MODULES
        .iter()
        .position(|(candidate, _, _)| *candidate == name)?;
    let (_, module, _) = try_compiled_at(index)?;
    Some((module_id_for_index(index), module.clone()))
}

/// One module's typed bodies, compiled on demand. The backend compiles
/// the reachable source graph as one unit, so imported stdlib modules
/// supply their bodies from here.
pub(crate) fn typed_program(
    name: &str,
) -> Option<Arc<crate::compiling::typed_program::TypedProgram>> {
    let index = STDLIB_MODULES
        .iter()
        .position(|(candidate, _, _)| *candidate == name)?;
    let (_, _, program) = compiled_at(index);
    Some(program.clone())
}

fn slots() -> &'static [OnceLock<CompiledStdlib>] {
    STDLIB.get_or_init(|| STDLIB_MODULES.iter().map(|_| OnceLock::new()).collect())
}

fn compiled_at(index: usize) -> &'static CompiledStdlib {
    let (name, _, _) = STDLIB_MODULES[index];
    if name == "syntax" {
        return SYNTAX.get_or_init(|| compile_index(index));
    }
    slots()[index].get_or_init(|| compile_index(index))
}

fn compile_index(index: usize) -> CompiledStdlib {
    let (name, _, _) = STDLIB_MODULES[index];
    if let Some(cached) = load_cached(name) {
        return cached;
    }
    let compiled = compile_module(name, module_sources(name), module_id_for_index(index));
    store_cached(name, &compiled);
    compiled
}

/// `compiled_at` for editor sessions: a module whose sources do not
/// compile cleanly right now (mid-edit) comes back `None` instead of
/// panicking, so the session degrades to ordinary unresolved-import
/// diagnostics. Only clean results are cached.
fn try_compiled_at(index: usize) -> Option<&'static CompiledStdlib> {
    let (name, _, _) = STDLIB_MODULES[index];
    let slot = if name == "syntax" {
        &SYNTAX
    } else {
        &slots()[index]
    };
    if let Some(cached) = slot.get() {
        return Some(cached);
    }
    if let Some(cached) = load_cached(name) {
        return Some(slot.get_or_init(|| cached));
    }
    let compiled = compile_module_fallible(name, module_sources(name), module_id_for_index(index))?;
    store_cached(name, &compiled);
    Some(slot.get_or_init(|| compiled))
}

type CompiledStdlib = (
    &'static str,
    Arc<Module>,
    Arc<crate::compiling::typed_program::TypedProgram>,
);

// ===== The compiled-stdlib disk cache =====
//
// One file per module under the shared cache root (src/compiling/cache.rs):
// products are a pure function of (sources, compiler), keyed on the
// module's own sources plus the keys of the stdlib modules those sources
// `use` (CLEAN-05) — a change to one module no longer invalidates every
// module.

/// One module's cache key. The bundled source set is fixed for the
/// process, so each module's key computes once; an override directory
/// can change between runs and stays dynamic.
fn cache_key_for(name: &'static str) -> Option<[u8; 32]> {
    static BUNDLED_KEYS: OnceLock<FxHashMap<&'static str, Option<[u8; 32]>>> = OnceLock::new();
    if path_override().is_none() {
        return BUNDLED_KEYS
            .get_or_init(|| {
                STDLIB_MODULES
                    .iter()
                    .map(|(name, _, _)| (*name, cache_key_dynamic(name, &mut Vec::new())))
                    .collect()
            })
            .get(name)
            .copied()
            .flatten();
    }
    cache_key_dynamic(name, &mut Vec::new())
}

fn cache_key_dynamic(name: &'static str, visiting: &mut Vec<&'static str>) -> Option<[u8; 32]> {
    if visiting.contains(&name) {
        // Stdlib has no import cycles; if one ever appears, no key is
        // better than an unbounded recursion.
        return None;
    }
    visiting.push(name);

    let sources = module_sources(name);
    let mut inputs: Vec<(String, String)> = Vec::with_capacity(sources.len());
    let mut texts: Vec<String> = Vec::with_capacity(sources.len());
    for source in &sources {
        let text = source.read().ok()?.to_string();
        inputs.push((source.path().into_owned(), text.clone()));
        texts.push(text);
    }

    // The transitive inputs: the stdlib modules these sources name in
    // `use` lines, discovered from the same texts being keyed (an
    // override directory's imports count, not the bundle's). Their
    // keys already close over their own dependencies.
    let mut dependencies = stdlib_dependencies_in(&texts);
    if name == "html" {
        // The html module's macro service compiles against the syntax
        // source set, which no import line names.
        dependencies.push("syntax");
    }
    dependencies.sort_unstable();
    dependencies.dedup();
    for dependency in dependencies {
        if dependency == name {
            continue;
        }
        let dependency_key = cache_key_dynamic(dependency, visiting)?;
        inputs.push((
            format!("$dependency:{dependency}"),
            dependency_key
                .iter()
                .map(|byte| format!("{byte:02x}"))
                .collect(),
        ));
    }
    visiting.pop();

    let refs: Vec<(&str, &str)> = inputs
        .iter()
        .map(|(path, content)| (path.as_str(), content.as_str()))
        .collect();
    super::cache::key(
        &format!("stdlib/{name}"),
        &refs,
        super::core::compiler_stamp(),
    )
}

/// The stdlib modules a source set imports, by scanning `use` lines.
/// Used only to close cache keys over transitive inputs; compilation
/// itself discovers imports through the parser (CLEAN-03).
fn stdlib_dependencies_in(texts: &[String]) -> Vec<&'static str> {
    let mut dependencies = Vec::new();
    for line in texts.iter().flat_map(|text| text.lines()) {
        let Some(rest) = line.trim().strip_prefix("use ") else {
            continue;
        };
        let rest = rest.strip_prefix("package::").unwrap_or(rest);
        let end = rest
            .find(|c: char| !(c.is_ascii_alphanumeric() || c == '_'))
            .unwrap_or(rest.len());
        let dependency = &rest[..end];
        if let Some((dependency, _, _)) = STDLIB_MODULES
            .iter()
            .find(|(candidate, _, _)| *candidate == dependency)
        {
            dependencies.push(*dependency);
        }
    }
    dependencies
}

fn load_cached(name: &'static str) -> Option<CompiledStdlib> {
    let key = cache_key_for(name)?;
    let payload = super::cache::load(&format!("stdlib/{name}"), &key)?;
    let (module, program): (Module, crate::compiling::typed_program::TypedProgram) =
        bincode::deserialize(&payload).ok()?;
    Some((name, Arc::new(module), Arc::new(program)))
}

fn store_cached(name: &'static str, compiled: &CompiledStdlib) {
    let Some(key) = cache_key_for(name) else {
        return;
    };
    let Ok(payload) = bincode::serialize(&(compiled.1.as_ref(), compiled.2.as_ref())) else {
        return;
    };
    super::cache::store(&format!("stdlib/{name}"), &key, &payload);
}

/// One module's compilation sources: the bundled text under the active
/// stdlib directory (a path override or the extracted bundle).
fn module_sources(name: &'static str) -> Vec<Source> {
    compilation_sources()
        .into_iter()
        .find(|(candidate, _)| *candidate == name)
        .unwrap_or_else(|| panic!("{name} stdlib sources are registered"))
        .1
}

fn compile_module(name: &'static str, sources: Vec<Source>, module_id: ModuleId) -> CompiledStdlib {
    let typed = compile_driver(name, sources, module_id);
    let program = typed.phase.program.clone();
    (name, Arc::new(typed.module(name)), Arc::new(program))
}

/// `compile_module` without the clean-compile assert: `None` when the
/// module's current sources produce errors.
fn compile_module_fallible(
    name: &'static str,
    sources: Vec<Source>,
    module_id: ModuleId,
) -> Option<CompiledStdlib> {
    let typed = compile_driver_fallible(name, sources, module_id)?;
    let program = typed.phase.program.clone();
    Some((name, Arc::new(typed.module(name)), Arc::new(program)))
}

/// The stdlib source tree sessions compile against: the
/// `TALK_STDLIB_PATH` override when set, otherwise the bundled tree
/// (the repository's `stdlib/` for a source build). The LSP scopes
/// per-module editing sessions against this root.
#[cfg(not(target_family = "wasm"))]
pub fn active_stdlib_dir() -> PathBuf {
    path_override().unwrap_or_else(bundled_compilation_dir)
}

fn compilation_sources() -> Vec<(&'static str, Vec<Source>)> {
    if let Some(stdlib_dir) = path_override() {
        assert!(
            stdlib_dir.is_dir(),
            "{TALK_STDLIB_PATH_ENV} must point to a directory: {}",
            stdlib_dir.display()
        );

        return STDLIB_MODULES
            .iter()
            .map(|(name, root_source, _)| {
                let paths: Vec<&str> = if *name == "syntax" {
                    STDLIB_FILES
                        .iter()
                        .filter(|(path, _)| Path::new(path).starts_with("syntax"))
                        .map(|(path, _)| *path)
                        .collect()
                } else {
                    vec![*root_source]
                };
                (
                    *name,
                    paths
                        .into_iter()
                        .map(|path| Source::from(stdlib_dir.join(path)))
                        .collect(),
                )
            })
            .collect();
    }

    let stdlib_dir = bundled_compilation_dir();
    STDLIB_MODULES
        .iter()
        .map(|(name, root_source, _)| {
            let files: Vec<(&str, &str)> = if *name == "syntax" {
                STDLIB_FILES
                    .iter()
                    .filter(|(path, _)| Path::new(path).starts_with("syntax"))
                    .copied()
                    .collect()
            } else {
                STDLIB_FILES
                    .iter()
                    .filter(|(path, _)| path == root_source)
                    .copied()
                    .collect()
            };
            (
                *name,
                files
                    .into_iter()
                    .map(|(path, content)| {
                        Source::in_memory(stdlib_dir.join(path), content.to_string())
                    })
                    .collect(),
            )
        })
        .collect()
}

fn bundled_compilation_dir() -> PathBuf {
    #[cfg(target_family = "wasm")]
    {
        PathBuf::from("stdlib")
    }

    #[cfg(not(target_family = "wasm"))]
    {
        let source_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("stdlib");
        if source_dir.is_dir() {
            return source_dir;
        }

        let dir = std::env::temp_dir().join("talk-stdlib");
        let _ = std::fs::create_dir_all(&dir);
        for (name, content) in STDLIB_FILES {
            let path = dir.join(name);
            if let Some(parent) = path.parent() {
                let _ = std::fs::create_dir_all(parent);
            }
            let _ = std::fs::write(path, content);
        }
        dir
    }
}

fn compile_driver_config(
    name: &'static str,
    module_id: ModuleId,
) -> DriverConfig {
    let mut modules = ModuleEnvironment::default();
    modules.import_core(super::core::compile());
    // Stdlib-internal imports (`use ansi` in testing.tlk) activate
    // their modules during parse discovery, which also records the
    // canonical dependency edges on the compiled module artifact.

    let mut config = DriverConfig::new(name);
    config.module_id = module_id;
    config.mode = CompilationMode::Library;
    config.modules = Rc::new(modules);
    // The html workspace root is a filesystem path; wasm has no
    // filesystem, so its macro units come from the embedded source set
    // instead.
    #[cfg(not(target_family = "wasm"))]
    if name == "html" {
        config.workspace_root = Some(active_stdlib_dir().join("html"));
    }
    #[cfg(target_family = "wasm")]
    {
        let prefix = format!("{name}/");
        let macro_sources: Vec<(&'static str, &'static str)> = STDLIB_FILES
            .iter()
            .filter(|(path, _)| {
                path.starts_with(&prefix)
                    && path.ends_with(crate::procedural_macros::MACRO_SUFFIX)
            })
            .copied()
            .collect();
        if !macro_sources.is_empty() {
            config.embedded_macro_sources = Some(macro_sources);
        }
    }
    config
}

/// `compile_driver` without the clean-compile assert: `None` on parse,
/// resolution, or type errors.
fn compile_driver_fallible(
    name: &'static str,
    sources: Vec<Source>,
    module_id: ModuleId,
) -> Option<Driver<Typed>> {
    let driver = Driver::new_bare(sources, compile_driver_config(name, module_id));
    let typed = driver.parse().ok()?.resolve_names().ok()?.type_check();
    if typed.has_errors() {
        return None;
    }
    Some(typed)
}

fn compile_driver(name: &'static str, sources: Vec<Source>, module_id: ModuleId) -> Driver<Typed> {
    let driver = Driver::new_bare(sources, compile_driver_config(name, module_id));

    #[allow(clippy::unwrap_used)]
    let typed = driver
        .parse()
        .unwrap()
        .resolve_names()
        .unwrap()
        .type_check();

    assert!(
        !typed.has_errors(),
        "Stdlib module {name} compiled with errors: {:#?}",
        typed.diagnostics()
    );

    typed
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn compiled_modules_record_their_dependency_edges() {
        // The canonical module graph (CLEAN-03): each compiled stdlib
        // module carries the edges its own parse discovery activated.
        let dependencies_of = |name: &str| {
            let (_, module) = module_with_id(name).expect("stdlib module");
            module
                .dependencies
                .iter()
                .filter_map(|id| name_for_module_id(*id))
                .collect::<Vec<_>>()
        };
        assert_eq!(dependencies_of("testing"), vec!["ansi"]);
        assert_eq!(dependencies_of("http"), vec!["net"]);
    }

    #[test]
    fn cache_keys_close_over_each_modules_own_inputs() {
        // CLEAN-05: key inputs are per-module, not the full stdlib set.
        let texts = |name: &str| {
            STDLIB_FILES
                .iter()
                .filter(|(path, _)| *path == format!("{name}.tlk"))
                .map(|(_, content)| content.to_string())
                .collect::<Vec<_>>()
        };
        assert_eq!(stdlib_dependencies_in(&texts("testing")), vec!["ansi"]);
        assert_eq!(stdlib_dependencies_in(&texts("http")), vec!["net"]);
        assert_eq!(stdlib_dependencies_in(&texts("fs")), vec!["os"]);
        // And the closure lands in the keys: fs's key is unaffected by
        // ansi's sources, testing's is not.
        let fs_key = cache_key_for("fs").expect("fs key");
        let ansi_key = cache_key_for("ansi").expect("ansi key");
        let testing_key = cache_key_for("testing").expect("testing key");
        assert_ne!(fs_key, ansi_key);
        assert_ne!(testing_key, ansi_key);
    }
}
