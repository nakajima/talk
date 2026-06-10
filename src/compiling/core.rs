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

/// The filenames of all core source files.
pub const CORE_SOURCE_NAMES: &[&str] = &[
    "Optional.tlk",
    "Operators.tlk",
    "Convert.tlk",
    "String.tlk",
    "Memory.tlk",
    "Array.tlk",
    "Iterable.tlk",
    "Async.tlk",
    "IO.tlk",
    "Net.tlk",
    "File.tlk",
    "Showable.tlk",
    "Http.tlk",
];

/// All core source strings, in a fixed order.
pub fn core_sources() -> Vec<(&'static str, &'static str)> {
    vec![
        ("Optional.tlk", include_str!("../../core/Optional.tlk")),
        ("Operators.tlk", include_str!("../../core/Operators.tlk")),
        ("Convert.tlk", include_str!("../../core/Convert.tlk")),
        ("String.tlk", include_str!("../../core/String.tlk")),
        ("Memory.tlk", include_str!("../../core/Memory.tlk")),
        ("Array.tlk", include_str!("../../core/Array.tlk")),
        ("Iterable.tlk", include_str!("../../core/Iterable.tlk")),
        ("Async.tlk", include_str!("../../core/Async.tlk")),
        ("IO.tlk", include_str!("../../core/IO.tlk")),
        ("Net.tlk", include_str!("../../core/Net.tlk")),
        ("File.tlk", include_str!("../../core/File.tlk")),
        ("Showable.tlk", include_str!("../../core/Showable.tlk")),
        ("Http.tlk", include_str!("../../core/Http.tlk")),
    ]
}

fn _compile() -> Module {
    let _s = tracing::trace_span!("compile_prelude", prelude = true).entered();
    let mut config = DriverConfig::new("Core");
    config.module_id = ModuleId::Core;
    config.mode = CompilationMode::Library;
    let sources = core_sources()
        .into_iter()
        .map(|(name, content)| Source::in_memory(name.into(), content))
        .collect();
    let driver = Driver::new_bare(sources, config);

    #[allow(clippy::unwrap_used)]
    let resolved = driver.parse().unwrap().resolve_names().unwrap();

    assert!(
        !resolved.has_errors(),
        "Core module compiled with errors: {:#?}",
        resolved.diagnostics()
    );

    resolved.module("Core")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn core_resolves_without_errors() {
        // _compile() asserts there are no error diagnostics.
        let module = _compile();
        assert_eq!(module.name, "Core");
        assert!(!module.exports.is_empty());
    }
}
