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
];

static STDLIB: OnceLock<Vec<CompiledStdlib>> = OnceLock::new();
// The parser is much larger than the other stdlib modules. Compile it only
// when source imports `syntax`, so ordinary compiler startup stays unchanged.
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
    let source_path = path.canonicalize().ok()?;
    let stdlib_dir = active_stdlib_dir().canonicalize().ok()?;
    let relative = source_path.strip_prefix(stdlib_dir).ok()?;

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

pub fn modules_with_ids() -> Vec<(ModuleId, Arc<Module>)> {
    STDLIB
        .get_or_init(compile_all)
        .iter()
        .map(|(name, module, _)| {
            let index = STDLIB_MODULES
                .iter()
                .position(|(candidate, _, _)| candidate == name)
                .expect("compiled stdlib module is registered");
            (module_id_for_index(index), module.clone())
        })
        .collect()
}

/// Load one stdlib module by its public import name. The driver uses this
/// after parsing imports to activate modules that are intentionally lazy.
pub fn module_with_id(name: &str) -> Option<(ModuleId, Arc<Module>)> {
    let index = STDLIB_MODULES
        .iter()
        .position(|(candidate, _, _)| *candidate == name)?;
    if name == "syntax" {
        let (_, module, _) = SYNTAX.get_or_init(compile_syntax);
        return Some((module_id_for_index(index), module.clone()));
    }
    STDLIB
        .get_or_init(compile_all)
        .iter()
        .find(|(candidate, _, _)| *candidate == name)
        .map(|(_, module, _)| (module_id_for_index(index), module.clone()))
}

/// The typed bodies behind every stdlib module interface, by module name.
/// The backend compiles the reachable source graph as one unit, so stdlib
/// callables supply their bodies from here.
pub(crate) fn typed_programs() -> Vec<(
    &'static str,
    Arc<crate::compiling::typed_program::TypedProgram>,
)> {
    let mut programs: Vec<_> = STDLIB
        .get_or_init(compile_all)
        .iter()
        .map(|(name, _, program)| (*name, program.clone()))
        .collect();
    if let Some((name, _, program)) = SYNTAX.get() {
        programs.push((*name, program.clone()));
    }
    programs
}

type CompiledStdlib = (
    &'static str,
    Arc<Module>,
    Arc<crate::compiling::typed_program::TypedProgram>,
);

fn compile_all() -> Vec<CompiledStdlib> {
    if let Some(cached) = load_cached() {
        return cached;
    }
    let compiled: Vec<CompiledStdlib> = compilation_sources()
        .into_iter()
        .filter(|(name, _)| *name != "syntax")
        .map(|(name, sources)| {
            let index = STDLIB_MODULES
                .iter()
                .position(|(candidate, _, _)| *candidate == name)
                .expect("stdlib module is registered");
            compile_module(name, sources, module_id_for_index(index))
        })
        .collect();
    store_cached(&compiled);
    compiled
}

// ===== The compiled-stdlib disk cache =====
//
// The same shape as core's (src/compiling/core.rs): products are a
// pure function of (sources, compiler), keyed by the source contents
// plus this binary's identity.

fn cache_key() -> Option<[u8; 32]> {
    use sha2::{Digest, Sha256};
    let mut hasher = Sha256::new();
    if let Some(stdlib_dir) = path_override() {
        for (path, _) in STDLIB_FILES
            .iter()
            .filter(|(path, _)| !Path::new(path).starts_with("syntax"))
        {
            let content = std::fs::read(stdlib_dir.join(path)).ok()?;
            hasher.update(path.as_bytes());
            hasher.update(&content);
        }
    } else {
        for (path, content) in STDLIB_FILES
            .iter()
            .filter(|(path, _)| !Path::new(path).starts_with("syntax"))
        {
            hasher.update(path.as_bytes());
            hasher.update(content.as_bytes());
        }
    }
    let (stamp, len) = super::core::exe_fingerprint()?;
    hasher.update(stamp.to_le_bytes());
    hasher.update(len.to_le_bytes());
    Some(hasher.finalize().into())
}

fn cache_path() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("target/.talk-cache/stdlib.bin")
}

type CachedStdlib = Vec<(Module, crate::compiling::typed_program::TypedProgram)>;

fn load_cached() -> Option<Vec<CompiledStdlib>> {
    let key = cache_key()?;
    let data = std::fs::read(cache_path()).ok()?;
    let (stored, payload) = data.split_at_checked(32)?;
    if stored != key {
        return None;
    }
    let cached: CachedStdlib = bincode::deserialize(payload).ok()?;
    let names: Vec<&'static str> = stdlib_sources()
        .into_iter()
        .map(|(name, _)| name)
        .filter(|name| *name != "syntax")
        .collect();
    if cached.len() != names.len() {
        return None;
    }
    Some(
        names
            .into_iter()
            .zip(cached)
            .map(|(name, (module, program))| (name, Arc::new(module), Arc::new(program)))
            .collect(),
    )
}

fn store_cached(compiled: &[CompiledStdlib]) {
    let Some(key) = cache_key() else { return };
    let payload: Vec<(&Module, &crate::compiling::typed_program::TypedProgram)> = compiled
        .iter()
        .map(|(_, module, program)| (module.as_ref(), program.as_ref()))
        .collect();
    let Ok(payload) = bincode::serialize(&payload) else {
        return;
    };
    let path = cache_path();
    if let Some(parent) = path.parent()
        && std::fs::create_dir_all(parent).is_err()
    {
        return;
    }
    let mut bytes = key.to_vec();
    bytes.extend_from_slice(&payload);
    let tmp = path.with_extension(format!("bin.{}", std::process::id()));
    if std::fs::write(&tmp, &bytes).is_ok() {
        let _ = std::fs::rename(&tmp, &path);
    }
}

fn compile_syntax() -> CompiledStdlib {
    if let Some(cached) = load_syntax_cached() {
        return cached;
    }
    let (_, sources) = compilation_sources()
        .into_iter()
        .find(|(name, _)| *name == "syntax")
        .expect("syntax stdlib sources are registered");
    let index = STDLIB_MODULES
        .iter()
        .position(|(name, _, _)| *name == "syntax")
        .expect("syntax stdlib module is registered");
    let compiled = compile_module("syntax", sources, module_id_for_index(index));
    store_syntax_cached(&compiled);
    compiled
}

// Syntax has a separate cache because populating the ordinary stdlib cache
// must not force the parser module to compile.
fn syntax_cache_key() -> Option<[u8; 32]> {
    use sha2::{Digest, Sha256};
    let mut hasher = Sha256::new();
    if let Some(stdlib_dir) = path_override() {
        for (path, _) in STDLIB_FILES
            .iter()
            .filter(|(path, _)| Path::new(path).starts_with("syntax"))
        {
            let content = std::fs::read(stdlib_dir.join(path)).ok()?;
            hasher.update(path.as_bytes());
            hasher.update(&content);
        }
    } else {
        for (path, content) in STDLIB_FILES
            .iter()
            .filter(|(path, _)| Path::new(path).starts_with("syntax"))
        {
            hasher.update(path.as_bytes());
            hasher.update(content.as_bytes());
        }
    }
    let (stamp, len) = super::core::exe_fingerprint()?;
    hasher.update(stamp.to_le_bytes());
    hasher.update(len.to_le_bytes());
    Some(hasher.finalize().into())
}

fn syntax_cache_path() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("target/.talk-cache/syntax.bin")
}

fn load_syntax_cached() -> Option<CompiledStdlib> {
    let key = syntax_cache_key()?;
    let data = std::fs::read(syntax_cache_path()).ok()?;
    let (stored, payload) = data.split_at_checked(32)?;
    if stored != key {
        return None;
    }
    let (module, program): (Module, crate::compiling::typed_program::TypedProgram) =
        bincode::deserialize(payload).ok()?;
    Some(("syntax", Arc::new(module), Arc::new(program)))
}

fn store_syntax_cached(compiled: &CompiledStdlib) {
    let Some(key) = syntax_cache_key() else {
        return;
    };
    let Ok(payload) = bincode::serialize(&(compiled.1.as_ref(), compiled.2.as_ref())) else {
        return;
    };
    let path = syntax_cache_path();
    if let Some(parent) = path.parent()
        && std::fs::create_dir_all(parent).is_err()
    {
        return;
    }
    let mut bytes = key.to_vec();
    bytes.extend_from_slice(&payload);
    let tmp = path.with_extension(format!("bin.{}", std::process::id()));
    if std::fs::write(&tmp, &bytes).is_ok() {
        let _ = std::fs::rename(&tmp, &path);
    }
}

fn compile_module(name: &'static str, sources: Vec<Source>, module_id: ModuleId) -> CompiledStdlib {
    let typed = compile_driver(name, sources, module_id);
    let program = typed.phase.program.clone();
    (name, Arc::new(typed.module(name)), Arc::new(program))
}

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

fn compile_driver(name: &'static str, sources: Vec<Source>, module_id: ModuleId) -> Driver<Typed> {
    let mut modules = ModuleEnvironment::default();
    modules.import_core(super::core::compile());

    let mut config = DriverConfig::new(name);
    config.module_id = module_id;
    config.mode = CompilationMode::Library;
    config.modules = Rc::new(modules);

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
