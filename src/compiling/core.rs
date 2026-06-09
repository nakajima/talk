use std::sync::Arc;

use lazy_static::lazy_static;
use sha2::{Digest, Sha256};

use crate::compiling::{
    driver::{CompilationMode, Driver, DriverConfig, Source},
    module::{Module, ModuleId},
};

lazy_static! {
    static ref CORE_MODULE: Arc<Module> = Arc::new(load_or_compile());
}

// Bump this whenever compiler/lowering changes invalidate serialized core modules
// even if the core source text itself is unchanged.
const CORE_CACHE_VERSION: &str = "2026-06-07-callee-cleanup-showable-derive";

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

/// All core source strings, in a fixed order for hashing.
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

fn source_hash() -> [u8; 32] {
    let mut hasher = Sha256::new();
    hasher.update(CORE_CACHE_VERSION.as_bytes());
    for (name, content) in core_sources() {
        hasher.update(name.as_bytes());
        hasher.update(content.as_bytes());
    }
    hasher.finalize().into()
}

fn cache_path() -> std::path::PathBuf {
    std::path::PathBuf::from("target/.talk-cache/core.bin")
}

fn load_cached() -> Option<Module> {
    let path = cache_path();
    let data = std::fs::read(&path).ok()?;
    // First 32 bytes are the source hash
    if data.len() < 32 {
        return None;
    }
    let (stored_hash, payload) = data.split_at(32);
    let expected = source_hash();
    if stored_hash != expected {
        tracing::debug!("core cache hash mismatch, recompiling");
        return None;
    }
    match bincode::deserialize::<Module>(payload) {
        Ok(module) => {
            tracing::debug!("loaded core module from cache");
            Some(module)
        }
        Err(e) => {
            tracing::debug!("core cache deserialization failed: {e}, recompiling");
            None
        }
    }
}

fn save_cached(module: &Module) {
    let path = cache_path();
    if let Some(parent) = path.parent() {
        let _ = std::fs::create_dir_all(parent);
    }
    let hash = source_hash();
    let payload = match bincode::serialize(module) {
        Ok(p) => p,
        Err(e) => {
            tracing::debug!("core cache serialization failed: {e}");
            return;
        }
    };
    let mut data = Vec::with_capacity(32 + payload.len());
    data.extend_from_slice(&hash);
    data.extend_from_slice(&payload);
    if let Err(e) = std::fs::write(&path, &data) {
        tracing::debug!("core cache write failed: {e}");
    } else {
        tracing::debug!("saved core module to cache");
    }
}

fn load_or_compile() -> Module {
    if let Some(module) = load_cached() {
        return module;
    }

    let module = _compile();
    save_cached(&module);
    module
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
    let lowered = driver
        .parse()
        .unwrap()
        .resolve_names()
        .unwrap()
        .typecheck()
        .unwrap()
        .lower()
        .unwrap();

    assert!(
        !lowered.has_errors(),
        "Core module compiled with errors: {:#?}",
        lowered.diagnostics()
    );

    lowered.module("Core")
}

#[cfg(test)]
mod tests {
    use rustc_hash::FxHashMap;

    use crate::{
        ir::{instruction::Instruction, instruction::InstructionMeta, value::Value},
        name_resolution::symbol::Symbol,
        node_id::{FileID, NodeID},
        types::{callee::Callee, infer_ty::Ty},
    };

    use super::*;

    fn typecheck_core() -> Driver<crate::compiling::driver::Typed> {
        let config = {
            let mut c = DriverConfig::new("Core");
            c.module_id = ModuleId::Core;
            c.mode = CompilationMode::Library;
            c
        };
        let sources = core_sources()
            .into_iter()
            .map(|(name, content)| Source::in_memory(name.into(), content))
            .collect();
        Driver::new_bare(sources, config)
            .parse()
            .unwrap()
            .resolve_names()
            .unwrap()
            .typecheck()
            .unwrap()
    }

    fn concrete_receiver_symbol(ty: &Ty) -> Option<Symbol> {
        match ty {
            Ty::Primitive(symbol) | Ty::Nominal { symbol, .. } => Some(*symbol),
            _ => None,
        }
    }

    fn callees_for_source(module: &Module, source: NodeID) -> Vec<Symbol> {
        module
            .program
            .functions
            .values()
            .flat_map(|function| &function.blocks)
            .flat_map(|block| &block.instructions)
            .filter_map(|instruction| {
                let Instruction::Call { callee, meta, .. } = instruction else {
                    return None;
                };
                if !meta
                    .items
                    .iter()
                    .any(|item| matches!(item, InstructionMeta::Source(id) if *id == source))
                {
                    return None;
                }
                let Value::Func(symbol) = callee else {
                    return None;
                };
                Some(*symbol)
            })
            .collect()
    }

    fn resolved_callees_for_source(module: &Module, source: NodeID) -> Vec<Callee> {
        module
            .program
            .functions
            .values()
            .flat_map(|function| &function.blocks)
            .flat_map(|block| &block.instructions)
            .filter_map(|instruction| {
                let Instruction::Call {
                    resolved_callee,
                    meta,
                    ..
                } = instruction
                else {
                    return None;
                };
                if !meta
                    .items
                    .iter()
                    .any(|item| matches!(item, InstructionMeta::Source(id) if *id == source))
                {
                    return None;
                }
                resolved_callee.clone()
            })
            .collect()
    }

    #[test]
    fn core_module_roundtrips_through_cache() {
        // Compile from scratch
        let original = _compile();

        // Serialize and deserialize
        let payload = bincode::serialize(&original).expect("serialization failed");
        let deserialized: Module = bincode::deserialize(&payload).expect("deserialization failed");

        // The deserialized module should match the original
        assert_eq!(original.name, deserialized.name);
        assert_eq!(original.id, deserialized.id);
        assert_eq!(original.exports.len(), deserialized.exports.len());
        assert_eq!(
            original.program.functions.len(),
            deserialized.program.functions.len()
        );
        assert_eq!(
            original.types.types_by_symbol.len(),
            deserialized.types.types_by_symbol.len()
        );
    }

    #[test]
    fn source_hash_is_deterministic() {
        let h1 = source_hash();
        let h2 = source_hash();
        assert_eq!(h1, h2);
    }

    #[test]
    fn core_compiles_without_errors() {
        use crate::common::diagnostic::{AnyDiagnostic, Severity};

        let lowered = typecheck_core().lower().unwrap();

        let critical_errors: Vec<_> = lowered
            .diagnostics()
            .iter()
            .filter(|d| match d {
                AnyDiagnostic::Parsing(d) => d.severity == Severity::Error,
                AnyDiagnostic::NameResolution(d) => d.severity == Severity::Error,
                AnyDiagnostic::Typing(d) => d.severity == Severity::Error,
            })
            .collect();

        assert!(
            critical_errors.is_empty(),
            "Core compiled with critical errors: {:#?}",
            critical_errors
        );
    }

    #[test]
    fn core_concrete_method_callees_match_receiver_type() {
        let module = typecheck_core().lower().unwrap().module("Core");
        let types = &module.types;

        let method_owners: FxHashMap<Symbol, Symbol> = types
            .catalog
            .instance_methods
            .iter()
            .flat_map(|(owner, methods)| methods.values().map(|method| (*method, *owner)))
            .collect();

        let mut mismatches = vec![];
        for function in module.program.functions.values() {
            for block in &function.blocks {
                for instruction in &block.instructions {
                    let Instruction::Call {
                        resolved_callee: Some(callee),
                        meta,
                        ..
                    } = instruction
                    else {
                        continue;
                    };
                    let Callee::Method {
                        symbol, self_ty, ..
                    } = callee
                    else {
                        continue;
                    };
                    let Some(expected_owner) = method_owners.get(symbol).copied() else {
                        continue;
                    };
                    if matches!(expected_owner, Symbol::Protocol(_)) {
                        continue;
                    }
                    let Some(actual_owner) = concrete_receiver_symbol(self_ty) else {
                        continue;
                    };

                    if actual_owner != expected_owner {
                        let call_id = meta.items.iter().find_map(|item| match item {
                            InstructionMeta::Source(id) => Some(*id),
                            _ => None,
                        });
                        let target_name = module
                            .symbol_names
                            .get(symbol)
                            .map(String::as_str)
                            .unwrap_or("<unknown>");
                        mismatches.push(format!(
                    "{call_id:?}: target {symbol:?} ({target_name}) belongs to {expected_owner:?}, but receiver type is {self_ty:?}"
                ));
                    }
                }
            }
        }

        assert!(
            mismatches.is_empty(),
            "concrete method callee metadata contains impossible target/receiver pairs:\n{}",
            mismatches.join("\n")
        );
    }

    #[test]
    fn core_lowering_uses_callee_fact_for_float_show_int_part() {
        let lowered = typecheck_core().lower().unwrap().module("Core");
        assert_float_show_int_part_uses_callee_fact(&lowered);
    }

    #[test]
    fn cached_core_uses_callee_fact_for_float_show_int_part() {
        assert_float_show_int_part_uses_callee_fact(compile().as_ref());
    }

    fn assert_float_show_int_part_uses_callee_fact(module: &Module) {
        let int_part_show = NodeID(FileID(11), 186);
        let resolved = resolved_callees_for_source(module, int_part_show);
        let [Callee::Method { symbol, .. }] = resolved.as_slice() else {
            panic!("missing callee metadata for Float.show int_part.show()");
        };

        assert_eq!(
            callees_for_source(module, int_part_show),
            vec![*symbol],
            "lowered call target must match semantic callee metadata"
        );
    }

    #[test]
    fn core_float_show_string_add_callees_have_string_self() {
        let module = compile();
        for node in [174, 198, 233, 250, 252] {
            let call_id = NodeID(FileID(11), node);
            let resolved = resolved_callees_for_source(&module, call_id);
            let [Callee::Method { self_ty, .. }] = resolved.as_slice() else {
                panic!("missing String.add callee metadata at {call_id:?}");
            };
            assert_eq!(
                concrete_receiver_symbol(self_ty),
                Some(Symbol::Struct(
                    crate::name_resolution::symbol::StructId::new(ModuleId::Core, 2,)
                )),
                "String.add call {call_id:?} should record String as semantic self type, got {self_ty:?}"
            );
        }
    }
}
