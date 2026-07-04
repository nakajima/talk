use std::rc::Rc;
use std::sync::{Arc, Mutex};

use lazy_static::lazy_static;
use rustc_hash::FxHashMap;

use crate::compiling::{
    core::LibraryTyped,
    driver::{CompilationMode, Driver, DriverConfig, Source, Typed},
    module::{Module, ModuleEnvironment, ModuleId},
};

lazy_static! {
    static ref STDLIB: Vec<Arc<Module>> = compile_all();
    /// Typed artifacts per (module, assigned id) — `Driver::lower()` asks
    /// for these on every compile (each REPL line, each test), so the full
    /// pipeline must run once per module, not once per call. The id is
    /// part of the key because the environment assigns it.
    static ref STDLIB_TYPED: Mutex<FxHashMap<(&'static str, ModuleId), Arc<LibraryTyped>>> =
        Mutex::default();
}

/// All stdlib source strings, in a fixed order.
pub fn stdlib_sources() -> Vec<(&'static str, &'static str)> {
    vec![("fs", include_str!("../../stdlib/fs.tlk"))]
}

pub fn modules() -> Vec<Arc<Module>> {
    STDLIB.clone()
}

pub fn typed_modules(module_env: &ModuleEnvironment) -> Vec<Arc<LibraryTyped>> {
    stdlib_sources()
        .into_iter()
        .filter_map(|(name, content)| {
            let module_id = module_env.get_module_id_by_name(name)?;
            #[allow(clippy::unwrap_used)]
            let mut cache = STDLIB_TYPED.lock().unwrap();
            let typed = cache
                .entry((name, module_id))
                .or_insert_with(|| Arc::new(compile_typed_module(name, content, module_id)));
            Some(Arc::clone(typed))
        })
        .collect()
}

fn compile_all() -> Vec<Arc<Module>> {
    stdlib_sources()
        .into_iter()
        .map(|(name, content)| compile_module(name, content))
        .collect()
}

fn compile_module(name: &'static str, content: &'static str) -> Arc<Module> {
    let typed = compile_driver(name, content, ModuleId::Current);
    Arc::new(typed.module(name))
}

fn compile_typed_module(
    name: &'static str,
    content: &'static str,
    module_id: ModuleId,
) -> LibraryTyped {
    let typed = compile_driver(name, content, module_id);
    let Typed {
        hir,
        mir_bodies,
        resolved_names,
        types,
        ..
    } = typed.phase;
    LibraryTyped {
        hir,
        mir_bodies,
        types,
        resolved_names,
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

fn compile_driver(name: &'static str, content: &'static str, module_id: ModuleId) -> Driver<Typed> {
    let mut modules = ModuleEnvironment::default();
    modules.import_core(super::core::compile());

    let mut config = DriverConfig::new(name);
    config.module_id = module_id;
    config.mode = CompilationMode::Library;
    config.modules = Rc::new(modules);

    let driver = Driver::new_bare(
        vec![Source::in_memory(
            format!("stdlib/{name}.tlk").into(),
            content,
        )],
        config,
    );

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
