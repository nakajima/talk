use std::{
    path::PathBuf,
    sync::{Arc, OnceLock},
};

use crate::compiling::{
    driver::{CompilationMode, Driver, DriverConfig, Source},
    module::{Module, ModuleId},
};

/// A bundled library's typed artifacts (core, stdlib), retained for
/// whole-program lowering: lazy monomorphization needs the library's
/// *bodies* (witnesses, protocol defaults, @_ir splices) at user-program
/// lower time — the MLton whole-program model rather than polymorphic IR
/// in modules.
pub struct LibraryTyped {
    pub(crate) program: crate::compiling::typed_program::TypedProgram,
    pub(crate) checked_mir: crate::lower::mir::CheckedMir,
}

const TALK_CORE_PATH_ENV: &str = "TALK_CORE_PATH";

pub fn path_override() -> Option<PathBuf> {
    std::env::var_os(TALK_CORE_PATH_ENV)
        .filter(|path| !path.is_empty())
        .map(|path| {
            let path = PathBuf::from(path);
            path.canonicalize().unwrap_or(path)
        })
}

static CORE: OnceLock<(Arc<Module>, Arc<LibraryTyped>)> = OnceLock::new();

pub fn compile() -> Arc<Module> {
    CORE.get_or_init(_compile).0.clone()
}

pub fn typed() -> Arc<LibraryTyped> {
    CORE.get_or_init(_compile).1.clone()
}

/// The filenames of all core source files.
pub const CORE_SOURCE_NAMES: &[&str] = &[
    "Ownership.tlk",
    "Optional.tlk",
    "Operators.tlk",
    "Convert.tlk",
    "String.tlk",
    "Memory.tlk",
    "UnicodeData.tlk",
    "Unicode.tlk",
    "Array.tlk",
    "Dict.tlk",
    "Iterable.tlk",
    "Async.tlk",
    "IO.tlk",
    "Net.tlk",
    "Rawfile.tlk",
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
        (
            "UnicodeData.tlk",
            include_str!("../../core/UnicodeData.tlk"),
        ),
        ("Unicode.tlk", include_str!("../../core/Unicode.tlk")),
        ("Array.tlk", include_str!("../../core/Array.tlk")),
        ("Dict.tlk", include_str!("../../core/Dict.tlk")),
        ("Iterable.tlk", include_str!("../../core/Iterable.tlk")),
        ("Async.tlk", include_str!("../../core/Async.tlk")),
        ("IO.tlk", include_str!("../../core/IO.tlk")),
        ("Net.tlk", include_str!("../../core/Net.tlk")),
        ("Rawfile.tlk", include_str!("../../core/Rawfile.tlk")),
        ("Showable.tlk", include_str!("../../core/Showable.tlk")),
        ("Http.tlk", include_str!("../../core/Http.tlk")),
        ("OS.tlk", include_str!("../../core/OS.tlk")),
    ]
}

fn compilation_sources() -> Vec<Source> {
    if let Some(core_dir) = path_override() {
        assert!(
            core_dir.is_dir(),
            "{TALK_CORE_PATH_ENV} must point to a directory: {}",
            core_dir.display()
        );

        return CORE_SOURCE_NAMES
            .iter()
            .map(|name| Source::from(core_dir.join(name)))
            .collect();
    }

    core_sources()
        .into_iter()
        .map(|(name, content)| Source::in_memory(name.into(), content))
        .collect()
}

fn _compile() -> (Arc<Module>, Arc<LibraryTyped>) {
    let _s = tracing::trace_span!("compile_prelude", prelude = true).entered();
    let mut config = DriverConfig::new("Core");
    config.module_id = ModuleId::Core;
    config.mode = CompilationMode::Library;
    let driver = Driver::new_bare(compilation_sources(), config);

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
        program: typed.phase.program.clone(),
        checked_mir: typed.phase.checked_mir.clone(),
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
        assert!(!typed.program.types().schemes.is_empty());
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
            module.exports.get("Character").copied(),
            Some(Symbol::Character)
        );
        assert_eq!(
            module.exports.get("Borrowed").copied(),
            Some(Symbol::Borrowed)
        );
        assert_eq!(module.exports.get("Owner").copied(), Some(Symbol::Owner));

        let types = typed.program.types();
        assert!(types.catalog.structs.contains_key(&Symbol::String));
        assert!(types.catalog.structs.contains_key(&Symbol::Array));
        assert!(types.catalog.structs.contains_key(&Symbol::Storage));
        assert!(types.catalog.structs.contains_key(&Symbol::Character));
        assert!(types.catalog.protocols.contains_key(&Symbol::Borrowed));
        assert!(types.catalog.protocols.contains_key(&Symbol::Owner));
    }

    #[test]
    fn core_iterator_into_array_conformance_is_exported() {
        let (module, typed) = _compile();
        let array_into_iterator = module.exports["ArrayIntoIterator"];
        let into = module.exports["Into"];
        let target = crate::types::ty::ProtocolRef {
            protocol: into,
            args: vec![crate::types::ty::Ty::Nominal(
                Symbol::Array,
                vec![crate::types::ty::Ty::Nominal(Symbol::Int, vec![])],
            )],
        };
        let catalog = &typed.program.types().catalog;
        let matches = catalog.matching_conformances(
            array_into_iterator,
            &[crate::types::ty::Ty::Nominal(Symbol::Int, vec![])],
            &target,
        );
        assert_eq!(matches.len(), 1);
    }
}
