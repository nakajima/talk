use crate::compiling::{
    driver::{Driver, DriverConfig, Source},
    module::{Module, ModuleId},
};

pub fn compile() -> Module {
    let _s = tracing::trace_span!("compile_prelude", prelude = true).entered();
    let config = DriverConfig {
        module_id: ModuleId::Core,
        ..Default::default()
    };
    let driver = Driver::new_bare(
        vec![
            Source::from(include_str!("../../core/Optional.tlk")),
            Source::from(include_str!("../../core/Operators.tlk")),
            Source::from(include_str!("../../core/Equals.tlk")),
            Source::from(include_str!("../../core/String.tlk")),
            Source::from(include_str!("../../core/Array.tlk")),
        ],
        config,
    );

    driver
        .parse()
        .unwrap()
        .resolve_names()
        .unwrap()
        .typecheck()
        .unwrap()
        .lower()
        .unwrap()
        .module("Core")
}
