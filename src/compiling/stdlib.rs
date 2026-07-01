use std::rc::Rc;
use std::sync::Arc;

use indexmap::IndexMap;
use lazy_static::lazy_static;

use crate::compiling::{
    driver::{CompilationMode, Driver, DriverConfig, Source, Typed},
    module::{Module, ModuleEnvironment, ModuleId},
};
use crate::name_resolution::name_resolver::ResolvedNames;
use crate::ownership::OwnershipOutput;
use crate::types::TypeOutput;

lazy_static! {
    static ref STDLIB: Vec<Arc<Module>> = compile_all();
}

/// Stdlib typed artifacts retained for whole-program lowering, just like
/// core's typed artifacts. Imported module metadata is enough for checking,
/// but lowering needs the actual bodies for demanded specializations.
pub struct StdlibTyped {
    pub hir: IndexMap<Source, crate::hir::HirFile>,
    pub types: TypeOutput,
    pub resolved_names: ResolvedNames,
    pub ownership: OwnershipOutput,
}

/// All stdlib source strings, in a fixed order.
pub fn stdlib_sources() -> Vec<(&'static str, &'static str)> {
    vec![("fs", include_str!("../../stdlib/fs.tlk"))]
}

pub fn modules() -> Vec<Arc<Module>> {
    STDLIB.clone()
}

pub fn typed_modules(module_env: &ModuleEnvironment) -> Vec<Arc<StdlibTyped>> {
    stdlib_sources()
        .into_iter()
        .filter_map(|(name, content)| {
            let module_id = module_env.get_module_id_by_name(name)?;
            Some(Arc::new(compile_typed_module(name, content, module_id)))
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
) -> StdlibTyped {
    let typed = compile_driver(name, content, module_id);
    let Typed {
        hir,
        resolved_names,
        types,
        ownership,
        ..
    } = typed.phase;
    StdlibTyped {
        hir,
        types,
        resolved_names,
        ownership,
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
