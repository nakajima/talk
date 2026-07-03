use std::sync::Arc;

use indexmap::IndexMap;
use lazy_static::lazy_static;

use crate::compiling::{
    driver::{CompilationMode, Driver, DriverConfig, Source},
    module::{Module, ModuleId},
};
use crate::name_resolution::name_resolver::ResolvedNames;
use crate::types::TypeOutput;

/// A bundled library's typed artifacts (core, stdlib), retained for
/// whole-program lowering: lazy monomorphization needs the library's
/// *bodies* (witnesses, protocol defaults, @_ir splices) at user-program
/// lower time — the MLton whole-program model rather than polymorphic IR
/// in modules.
pub struct LibraryTyped {
    pub hir: IndexMap<Source, crate::hir::HirFile>,
    pub mir_bodies: crate::lower::mir::ModuleBodies,
    pub types: TypeOutput,
    pub resolved_names: ResolvedNames,
}

lazy_static! {
    static ref CORE: (Arc<Module>, Arc<LibraryTyped>) = _compile();
}

pub fn compile() -> Arc<Module> {
    CORE.0.clone()
}

pub fn typed() -> Arc<LibraryTyped> {
    CORE.1.clone()
}

/// The filenames of all core source files.
pub const CORE_SOURCE_NAMES: &[&str] = &[
    "Ownership.tlk",
    "Optional.tlk",
    "Operators.tlk",
    "Convert.tlk",
    "String.tlk",
    "Memory.tlk",
    "Array.tlk",
    "Dict.tlk",
    "Iterable.tlk",
    "Async.tlk",
    "IO.tlk",
    "Net.tlk",
    "File.tlk",
    "Showable.tlk",
    "Http.tlk",
    "OS.tlk",
];

/// All core source strings, in a fixed order.
pub fn core_sources() -> Vec<(&'static str, &'static str)> {
    vec![
        ("Ownership.tlk", include_str!("../../core/Ownership.tlk")),
        ("Optional.tlk", include_str!("../../core/Optional.tlk")),
        ("Operators.tlk", include_str!("../../core/Operators.tlk")),
        ("Convert.tlk", include_str!("../../core/Convert.tlk")),
        ("String.tlk", include_str!("../../core/String.tlk")),
        ("Memory.tlk", include_str!("../../core/Memory.tlk")),
        ("Array.tlk", include_str!("../../core/Array.tlk")),
        ("Dict.tlk", include_str!("../../core/Dict.tlk")),
        ("Iterable.tlk", include_str!("../../core/Iterable.tlk")),
        ("Async.tlk", include_str!("../../core/Async.tlk")),
        ("IO.tlk", include_str!("../../core/IO.tlk")),
        ("Net.tlk", include_str!("../../core/Net.tlk")),
        ("File.tlk", include_str!("../../core/File.tlk")),
        ("Showable.tlk", include_str!("../../core/Showable.tlk")),
        ("Http.tlk", include_str!("../../core/Http.tlk")),
        ("OS.tlk", include_str!("../../core/OS.tlk")),
    ]
}

fn _compile() -> (Arc<Module>, Arc<LibraryTyped>) {
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

    let core_typed = LibraryTyped {
        hir: typed.phase.hir.clone(),
        mir_bodies: typed.phase.mir_bodies.clone(),
        types: typed.phase.types.clone(),
        resolved_names: typed.phase.resolved_names.clone(),
    };
    (Arc::new(typed.module("Core")), Arc::new(core_typed))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::name_resolution::symbol::Symbol;

    #[test]
    fn core_resolves_without_errors() {
        // _compile() asserts there are no error diagnostics.
        let (module, typed) = _compile();
        assert_eq!(module.name, "Core");
        assert!(!module.exports.is_empty());
        assert!(!typed.types.schemes.is_empty());
    }

    #[test]
    fn core_exports_use_well_known_symbols() {
        let (module, typed) = _compile();

        assert_eq!(module.exports.get("String").copied(), Some(Symbol::String));
        assert_eq!(module.exports.get("Array").copied(), Some(Symbol::Array));
        assert_eq!(
            module.exports.get("Storage").copied(),
            Some(Symbol::Storage)
        );
        assert_eq!(
            module.exports.get("Borrowed").copied(),
            Some(Symbol::Borrowed)
        );
        assert_eq!(module.exports.get("Owner").copied(), Some(Symbol::Owner));

        assert!(typed.types.catalog.structs.contains_key(&Symbol::String));
        assert!(typed.types.catalog.structs.contains_key(&Symbol::Array));
        assert!(typed.types.catalog.structs.contains_key(&Symbol::Storage));
        assert!(
            typed
                .types
                .catalog
                .protocols
                .contains_key(&Symbol::Borrowed)
        );
        assert!(typed.types.catalog.protocols.contains_key(&Symbol::Owner));
    }
}
