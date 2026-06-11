use std::sync::Arc;

use indexmap::IndexMap;
use lazy_static::lazy_static;

use crate::ast::{AST, NameResolved};
use crate::compiling::{
    driver::{CompilationMode, Driver, DriverConfig, Source},
    module::{Module, ModuleId},
};
use crate::name_resolution::name_resolver::ResolvedNames;
use crate::types::TypeOutput;

/// Core's typed artifacts, retained for whole-program lowering: lazy
/// monomorphization needs core's *bodies* (witnesses, protocol defaults,
/// @_ir splices) at user-program lower time — the MLton whole-program
/// model rather than polymorphic IR in modules.
pub struct CoreTyped {
    pub asts: IndexMap<Source, AST<NameResolved>>,
    pub types: TypeOutput,
    pub resolved_names: ResolvedNames,
}

lazy_static! {
    static ref CORE: (Arc<Module>, Arc<CoreTyped>) = _compile();
}

pub fn compile() -> Arc<Module> {
    CORE.0.clone()
}

pub fn typed() -> Arc<CoreTyped> {
    CORE.1.clone()
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

fn _compile() -> (Arc<Module>, Arc<CoreTyped>) {
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
    let typed = driver
        .parse()
        .unwrap()
        .resolve_names()
        .unwrap()
        .type_check();

    assert!(
        !typed.has_errors(),
        "Core module compiled with errors: {:#?}",
        typed.diagnostics()
    );

    let core_typed = CoreTyped {
        asts: typed.phase.asts.clone(),
        types: typed.phase.types.clone(),
        resolved_names: typed.phase.resolved_names.clone(),
    };
    (Arc::new(typed.module("Core")), Arc::new(core_typed))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn core_resolves_without_errors() {
        // _compile() asserts there are no error diagnostics.
        let (module, typed) = _compile();
        assert_eq!(module.name, "Core");
        assert!(!module.exports.is_empty());
        assert!(!typed.types.schemes.is_empty());
    }
}
