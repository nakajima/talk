use std::sync::Arc;

use lazy_static::lazy_static;

use crate::compiling::{
    driver::{CompilationMode, Driver, DriverConfig, Source},
    module::{Module, ModuleId},
};

lazy_static! {
    static ref CORE_MODULE: Arc<Module> = Arc::new(_compile());
}

pub fn compile() -> Arc<Module> {
    CORE_MODULE.clone()
}

fn _compile() -> Module {
    let _s = tracing::trace_span!("compile_prelude", prelude = true).entered();
    let mut config = DriverConfig::new("Core");
    config.module_id = ModuleId::Core;
    config.mode = CompilationMode::Library;
    let driver = Driver::new_bare(
        vec![
            Source::in_memory(
                "Optional.tlk".into(),
                include_str!("../../core/Optional.tlk"),
            ),
            Source::in_memory(
                "Operators.tlk".into(),
                include_str!("../../core/Operators.tlk"),
            ),
            Source::in_memory("String.tlk".into(), include_str!("../../core/String.tlk")),
            Source::in_memory("Memory.tlk".into(), include_str!("../../core/Memory.tlk")),
            Source::in_memory("Array.tlk".into(), include_str!("../../core/Array.tlk")),
            Source::in_memory(
                "Iterable.tlk".into(),
                include_str!("../../core/Iterable.tlk"),
            ),
            Source::in_memory(
                "Generator.tlk".into(),
                include_str!("../../core/Generator.tlk"),
            ),
        ],
        config,
    );

    #[allow(clippy::unwrap_used)]
    let module = driver
        .parse()
        .unwrap()
        .resolve_names()
        .unwrap()
        .typecheck()
        .unwrap()
        .lower()
        .unwrap()
        .module("Core");

    module
}
