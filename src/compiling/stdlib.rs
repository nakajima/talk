use std::path::{Path, PathBuf};
use std::rc::Rc;
use std::sync::{Arc, OnceLock};

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

/// Stdlib-internal import edges, read from each module's root source: a
/// module's typed bodies may call into the modules it `use`s (for
/// example testing calls into ansi), so backend inputs must close over
/// them. A missed edge fails compilation loudly rather than silently.
pub(crate) fn dependencies_of(name: &str) -> Vec<&'static str> {
    let Some((_, _, text)) = STDLIB_MODULES
        .iter()
        .find(|(candidate, _, _)| *candidate == name)
    else {
        return Vec::new();
    };
    text.lines()
        .filter_map(|line| {
            let rest = line.trim().strip_prefix("use package::")?;
            let end = rest
                .find(|c: char| !(c.is_ascii_alphanumeric() || c == '_'))
                .unwrap_or(rest.len());
            let dependency = &rest[..end];
            STDLIB_MODULES
                .iter()
                .any(|(candidate, _, _)| *candidate == dependency)
                .then_some(dependency)
        })
        .collect()
}

/// Compile and register every stdlib module interface. Only the editor
/// wants this: auto-import completions and cross-module navigation need
/// every export available, not just the ones a document already names.
pub fn modules_with_ids() -> Vec<(ModuleId, Arc<Module>)> {
    STDLIB_MODULES
        .iter()
        .enumerate()
        .filter(|(_, (name, _, _))| {
            *name != "syntax" && !(cfg!(target_family = "wasm") && *name == "testing")
        })
        .map(|(index, _)| {
            let (_, module, _) = compiled_at(index);
            (module_id_for_index(index), module.clone())
        })
        .collect()
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

type CompiledStdlib = (
    &'static str,
    Arc<Module>,
    Arc<crate::compiling::typed_program::TypedProgram>,
);

// ===== The compiled-stdlib disk cache =====
//
// One file per module under the shared cache root (src/compiling/cache.rs):
// products are a pure function of (sources, compiler), keyed on the full
// stdlib source set plus this binary's identity.

fn cache_key() -> Option<[u8; 32]> {
    let sources: Vec<(String, String)> = if let Some(stdlib_dir) = path_override() {
        // The html module's macro service compiles against the syntax source
        // set, so those sources are inputs to every stdlib module's key too.
        STDLIB_FILES
            .iter()
            .map(|(path, _)| {
                std::fs::read_to_string(stdlib_dir.join(path))
                    .ok()
                    .map(|content| (path.to_string(), content))
            })
            .collect::<Option<Vec<_>>>()?
    } else {
        STDLIB_FILES
            .iter()
            .map(|(path, content)| (path.to_string(), content.to_string()))
            .collect()
    };
    let refs: Vec<(&str, &str)> = sources
        .iter()
        .map(|(path, content)| (path.as_str(), content.as_str()))
        .collect();
    super::cache::key(&refs, super::core::exe_fingerprint())
}

fn load_cached(name: &'static str) -> Option<CompiledStdlib> {
    let key = cache_key()?;
    let payload = super::cache::load(&format!("stdlib/{name}"), &key)?;
    let (module, program): (Module, crate::compiling::typed_program::TypedProgram) =
        bincode::deserialize(&payload).ok()?;
    Some((name, Arc::new(module), Arc::new(program)))
}

fn store_cached(name: &'static str, compiled: &CompiledStdlib) {
    let Some(key) = cache_key() else { return };
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

#[cfg(not(target_family = "wasm"))]
fn active_stdlib_dir() -> PathBuf {
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

fn compile_driver(name: &'static str, sources: Vec<Source>, module_id: ModuleId) -> Driver<Typed> {
    let mut modules = ModuleEnvironment::default();
    modules.import_core(super::core::compile());

    let mut config = DriverConfig::new(name);
    config.module_id = module_id;
    config.mode = CompilationMode::Library;
    config.modules = Rc::new(modules);
    if name == "html" {
        config.workspace_root = Some(active_stdlib_dir().join("html"));
    }

    let driver = Driver::new_bare(sources, config);

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
