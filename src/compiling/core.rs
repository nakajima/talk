use std::{
    path::PathBuf,
    sync::{Arc, OnceLock},
};

use crate::compiling::{
    driver::{CompilationMode, Driver, DriverConfig, Source},
    module::{Module, ModuleId},
};

const TALK_CORE_PATH_ENV: &str = "TALK_CORE_PATH";

pub fn path_override() -> Option<PathBuf> {
    std::env::var_os(TALK_CORE_PATH_ENV)
        .filter(|path| !path.is_empty())
        .map(|path| {
            let path = PathBuf::from(path);
            path.canonicalize().unwrap_or(path)
        })
}

struct CoreArtifacts {
    module: Arc<Module>,
    typed: Arc<crate::compiling::typed_program::TypedProgram>,
}

static CORE: OnceLock<CoreArtifacts> = OnceLock::new();

pub fn compile() -> Arc<Module> {
    CORE.get_or_init(_compile).module.clone()
}

/// The typed bodies behind the core interface. The backend compiles the
/// reachable source graph as one unit, so core callables supply their
/// bodies from here.
pub(crate) fn typed_program() -> Arc<crate::compiling::typed_program::TypedProgram> {
    CORE.get_or_init(_compile).typed.clone()
}

/// The filenames of all core source files.
pub const CORE_SOURCE_NAMES: &[&str] = &[
    "Ownership.tlk",
    "Optional.tlk",
    "Result.tlk",
    "Operators.tlk",
    "Convert.tlk",
    "String.tlk",
    "Memory.tlk",
    "UnicodeData.tlk",
    "Unicode.tlk",
    "Array.tlk",
    "InlineArray.tlk",
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
        ("Result.tlk", include_str!("../../core/Result.tlk")),
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
        (
            "InlineArray.tlk",
            include_str!("../../core/InlineArray.tlk"),
        ),
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

fn _compile() -> CoreArtifacts {
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

    let program = typed.phase.program.clone();
    let module = Arc::new(typed.module("Core"));
    CoreArtifacts {
        module,
        typed: Arc::new(program),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::name_resolution::symbol::Symbol;

    #[test]
    fn core_resolves_without_errors() {
        // _compile() asserts there are no error diagnostics.
        let module = _compile().module;
        assert_eq!(module.name, "Core");
        assert!(!module.exports.is_empty());
        assert!(!module.types.schemes.is_empty());
    }

    #[test]
    fn core_exports_use_well_known_symbols() {
        let module = _compile().module;

        assert_eq!(module.exports.get("String").copied(), Some(Symbol::String));
        assert_eq!(module.exports.get("Array").copied(), Some(Symbol::Array));
        assert_eq!(
            module.exports.get("InlineArray").copied(),
            Some(Symbol::InlineArray)
        );
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

        let catalog = &module.types.catalog;
        assert!(catalog.structs.contains_key(&Symbol::String));
        assert!(catalog.structs.contains_key(&Symbol::Array));
        assert!(catalog.structs.contains_key(&Symbol::InlineArray));
        assert!(catalog.structs.contains_key(&Symbol::Storage));
        assert!(catalog.structs.contains_key(&Symbol::Character));
        assert!(catalog.protocols.contains_key(&Symbol::Borrowed));
        assert!(catalog.protocols.contains_key(&Symbol::Owner));
    }

    #[test]
    fn core_iterator_into_array_conformance_is_exported() {
        let module = _compile().module;
        let array_into_iterator = module.exports["ArrayIntoIterator"];
        let into = module.exports["Into"];
        let target = crate::types::ty::ProtocolRef {
            protocol: into,
            args: vec![crate::types::ty::Ty::Nominal(
                Symbol::Array,
                vec![crate::types::ty::Ty::Nominal(Symbol::Int, vec![])],
            )],
        };
        let catalog = &module.types.catalog;
        let matches = catalog.matching_conformances(
            array_into_iterator,
            &[crate::types::ty::Ty::Nominal(Symbol::Int, vec![])],
            &target,
        );
        assert_eq!(matches.len(), 1);
    }
}
