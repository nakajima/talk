//! Public API closure validation (ADR 0042 §3): a public declaration
//! cannot expose a symbol its consumer is forbidden to name. This pass
//! walks every public source-facing contract — exported top-level
//! values, public members and their synthesized initializers, enum
//! payloads, protocol requirements, public effects, and public type
//! aliases — and diagnoses every effectively-private local dependency
//! at the public declaration. Bodies may use private declarations
//! freely — implementation dependencies are not source-facing
//! contracts.

use rustc_hash::{FxHashMap, FxHashSet};

use crate::name_resolution::name_resolver::ResolvedNames;
use crate::name_resolution::symbol::{Symbol, SymbolKind};
use crate::node_id::NodeID;
use crate::node_kinds::decl::Visibility;
use crate::types::catalog::TypeCatalog;
use crate::types::error::TypeError;
use crate::types::ty::Scheme;

pub(super) fn check_public_api_closure(
    resolved: &ResolvedNames,
    schemes: &FxHashMap<Symbol, Scheme>,
    catalog: &TypeCatalog,
    errors: &mut Vec<(TypeError, NodeID)>,
) {
    let mut findings: Vec<(Symbol, Symbol)> = vec![];
    for (&symbol, record) in &resolved.declarations {
        if record.effective != Visibility::Public {
            continue;
        }
        let mut dependencies = FxHashSet::default();
        match record.role {
            SymbolKind::Global => {
                if let Some(scheme) = schemes.get(&symbol) {
                    scheme.referenced_symbols(&mut dependencies);
                }
            }
            // Public callables' contracts, including the synthesized
            // memberwise initializer (whose parameters cover every
            // stored property) and protocol requirements (which inherit
            // the protocol's visibility).
            SymbolKind::InstanceMethod
            | SymbolKind::StaticMethod
            | SymbolKind::Initializer
            | SymbolKind::Synthesized
            | SymbolKind::MethodRequirement => {
                if let Some(scheme) = schemes.get(&symbol) {
                    scheme.referenced_symbols(&mut dependencies);
                }
            }
            SymbolKind::Property => {
                if let Some(owner) = record.owner
                    && let Some(name) = resolved.symbol_names.get(&symbol)
                    && let Some(info) = catalog.structs.get(&owner)
                    && let Some((_, ty)) = info.fields.get(name)
                {
                    ty.referenced_symbols(&mut dependencies);
                }
            }
            // Cases inherit the enum's visibility, so a public enum's
            // payload types are part of the public API closure.
            SymbolKind::Variant => {
                if let Some(owner) = record.owner
                    && let Some(name) = resolved.symbol_names.get(&symbol)
                    && let Some(info) = catalog.enums.get(&owner)
                    && let Some(variant) = info.variants.get(name)
                {
                    variant
                        .constructor_scheme
                        .referenced_symbols(&mut dependencies);
                }
            }
            SymbolKind::Effect => {
                if let Some(signature) = catalog.effects.get(&symbol) {
                    for param in &signature.params {
                        param.referenced_symbols(&mut dependencies);
                    }
                    signature.ret.referenced_symbols(&mut dependencies);
                    for predicate in &signature.predicates {
                        predicate.referenced_symbols(&mut dependencies);
                    }
                }
            }
            SymbolKind::TypeAlias => {
                if let Some(alias) = catalog.type_aliases.get(&symbol) {
                    alias.ty.referenced_symbols(&mut dependencies);
                }
            }
            _ => continue,
        }
        for dependency in dependencies {
            let Some(target) = resolved.declarations.get(&dependency) else {
                continue;
            };
            if target.effective == Visibility::Public {
                continue;
            }
            if !matches!(
                target.role,
                SymbolKind::Struct
                    | SymbolKind::Enum
                    | SymbolKind::Protocol
                    | SymbolKind::TypeAlias
                    | SymbolKind::Effect
            ) {
                continue;
            }
            findings.push((symbol, dependency));
        }
    }
    // Table iteration is unordered; report in a stable order.
    findings.sort_by_key(|(symbol, dependency)| {
        (
            resolved.symbols_to_node.get(symbol).copied(),
            resolved.symbols_to_node.get(dependency).copied(),
        )
    });
    findings.dedup();
    for (symbol, dependency) in findings {
        let node = resolved
            .symbols_to_node
            .get(&symbol)
            .copied()
            .unwrap_or(NodeID(crate::node_id::FileID(0), 0));
        errors.push((
            TypeError::PublicApiExposesPrivate {
                name: resolved
                    .symbol_names
                    .get(&symbol)
                    .cloned()
                    .unwrap_or_default(),
                dependency: resolved
                    .symbol_names
                    .get(&dependency)
                    .cloned()
                    .unwrap_or_default(),
            },
            node,
        ));
    }
}
