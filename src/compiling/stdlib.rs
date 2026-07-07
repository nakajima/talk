use rustc_hash::FxHashMap;
use std::path::{Path, PathBuf};
use std::rc::Rc;
use std::sync::{Arc, Mutex, OnceLock};

use crate::compiling::{
    core::LibraryTyped,
    driver::{CompilationMode, Driver, DriverConfig, Source, Typed},
    module::{Module, ModuleEnvironment, ModuleId},
};

const TALK_STDLIB_PATH_ENV: &str = "TALK_STDLIB_PATH";

pub const STDLIB_SOURCE_NAMES: &[&str] = &["fs.tlk", "ansi.tlk", "testing.tlk"];

static STDLIB: OnceLock<Vec<Arc<Module>>> = OnceLock::new();
/// Typed artifacts per (module, assigned id) — `Driver::lower()` asks
/// for these on every compile (each REPL line, each test), so the full
/// pipeline must run once per module, not once per call. The id is
/// part of the key because the environment assigns it.
static STDLIB_TYPED: OnceLock<Mutex<FxHashMap<(&'static str, ModuleId), Arc<LibraryTyped>>>> =
    OnceLock::new();

pub fn path_override() -> Option<PathBuf> {
    std::env::var_os(TALK_STDLIB_PATH_ENV)
        .filter(|path| !path.is_empty())
        .map(|path| {
            let path = PathBuf::from(path);
            path.canonicalize().unwrap_or(path)
        })
}

/// All bundled stdlib source strings, in a fixed order.
pub fn stdlib_sources() -> Vec<(&'static str, &'static str)> {
    vec![
        ("fs", include_str!("../../stdlib/fs.tlk")),
        ("ansi", include_str!("../../stdlib/ansi.tlk")),
        ("testing", include_str!("../../stdlib/testing.tlk")),
    ]
}

pub fn module_name_for_path(path: &Path) -> Option<&'static str> {
    let source_path = path.canonicalize().ok()?;
    let stdlib_dir = active_stdlib_dir().canonicalize().ok()?;
    if source_path.parent()? != stdlib_dir.as_path() {
        return None;
    }
    let file_name = source_path.file_name()?.to_str()?;
    module_name_for_file_name(file_name)
}

pub fn source_document(name: &str) -> Option<(PathBuf, String)> {
    let filename = source_file_name(name)?;

    if let Some(stdlib_dir) = path_override() {
        let path = stdlib_dir.join(filename);
        let text = std::fs::read_to_string(&path).ok()?;
        let path = path.canonicalize().unwrap_or(path);
        return Some((path, text));
    }

    let bundled_text = stdlib_sources()
        .into_iter()
        .find_map(|(source_name, text)| (source_name == name).then_some(text))?;

    let candidates = [
        PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("stdlib")
            .join(filename),
        PathBuf::from("stdlib").join(filename),
    ];
    for candidate in candidates {
        if candidate.is_file()
            && let Ok(path) = candidate.canonicalize()
        {
            let text = std::fs::read_to_string(&path).unwrap_or_else(|_| bundled_text.to_string());
            return Some((path, text));
        }
    }

    let dir = std::env::temp_dir().join("talk-stdlib");
    let _ = std::fs::create_dir_all(&dir);
    let path = dir.join(filename);
    let _ = std::fs::write(&path, bundled_text);
    Some((path, bundled_text.to_string()))
}

pub fn modules() -> Vec<Arc<Module>> {
    STDLIB.get_or_init(compile_all).clone()
}

pub fn typed_modules(module_env: &ModuleEnvironment) -> Vec<Arc<LibraryTyped>> {
    compilation_sources()
        .into_iter()
        .filter_map(|(name, source)| {
            let module_id = module_env.get_module_id_by_name(name)?;
            #[allow(clippy::unwrap_used)]
            let mut cache = STDLIB_TYPED.get_or_init(Mutex::default).lock().unwrap();
            let typed = cache
                .entry((name, module_id))
                .or_insert_with(|| Arc::new(compile_typed_module(name, source, module_id)));
            Some(Arc::clone(typed))
        })
        .collect()
}

fn compile_all() -> Vec<Arc<Module>> {
    compilation_sources()
        .into_iter()
        .map(|(name, source)| compile_module(name, source))
        .collect()
}

fn compile_module(name: &'static str, source: Source) -> Arc<Module> {
    let typed = compile_driver(name, source, ModuleId::Current);
    Arc::new(typed.module(name))
}

fn compile_typed_module(name: &'static str, source: Source, module_id: ModuleId) -> LibraryTyped {
    let typed = compile_driver(name, source, module_id);
    let Typed {
        program,
        checked_mir,
        ..
    } = typed.phase;
    LibraryTyped {
        program,
        checked_mir,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn typed_modules_are_cached() {
        // Driver::lower() calls typed_modules() on every compile (each
        // REPL line, each test): the full parse/resolve/check pipeline
        // must run once per module, not once per call.
        let mut env = ModuleEnvironment::default();
        env.import_core(crate::compiling::core::compile());
        for module in modules() {
            env.import((*module).clone());
        }
        let first = typed_modules(&env);
        let second = typed_modules(&env);
        assert!(!first.is_empty(), "stdlib has modules");
        assert!(
            first.iter().zip(&second).all(|(a, b)| Arc::ptr_eq(a, b)),
            "repeated calls must return the cached artifacts"
        );
    }
}

fn active_stdlib_dir() -> PathBuf {
    path_override().unwrap_or_else(|| PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("stdlib"))
}

fn source_file_name(name: &str) -> Option<&'static str> {
    STDLIB_SOURCE_NAMES
        .iter()
        .copied()
        .find(|file_name| module_name_for_file_name(file_name) == Some(name))
}

fn module_name_for_file_name(file_name: &str) -> Option<&'static str> {
    STDLIB_SOURCE_NAMES.iter().find_map(|source_name| {
        if *source_name != file_name {
            return None;
        }
        source_name.strip_suffix(".tlk")
    })
}

fn compilation_sources() -> Vec<(&'static str, Source)> {
    if let Some(stdlib_dir) = path_override() {
        assert!(
            stdlib_dir.is_dir(),
            "{TALK_STDLIB_PATH_ENV} must point to a directory: {}",
            stdlib_dir.display()
        );

        return STDLIB_SOURCE_NAMES
            .iter()
            .filter_map(|filename| {
                let name = module_name_for_file_name(filename)?;
                Some((name, Source::from(stdlib_dir.join(filename))))
            })
            .collect();
    }

    let stdlib_dir = bundled_compilation_dir();
    stdlib_sources()
        .into_iter()
        .map(|(name, content)| {
            (
                name,
                Source::in_memory(stdlib_dir.join(format!("{name}.tlk")), content),
            )
        })
        .collect()
}

fn bundled_compilation_dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("stdlib")
}

fn compile_driver(name: &'static str, source: Source, module_id: ModuleId) -> Driver<Typed> {
    let mut modules = ModuleEnvironment::default();
    modules.import_core(super::core::compile());

    let mut config = DriverConfig::new(name);
    config.module_id = module_id;
    config.mode = CompilationMode::Library;
    config.modules = Rc::new(modules);

    let driver = Driver::new_bare(vec![source], config);

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
