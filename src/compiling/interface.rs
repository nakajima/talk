//! The public module interface (ADR 0042 §7): a compiled module ships
//! its exported names, the transitive semantic closure needed to type
//! them, and nothing else. Private implementation payload — unrelated
//! private schemes, nominals, rows, and helpers — stays in the owning
//! compiled artifact (the backend reads full `TypedProgram`s, never
//! `Module.types`).
//!
//! Reachability starts at every effectively-public declaration and
//! walks source-facing contracts: schemes, field and payload types,
//! requirement signatures, effect signatures, alias targets, and the
//! conformance rows of reachable heads whose target protocol is
//! nameable by an importer. Private symbols referenced by those
//! contracts stay in the interface as suppliers — a private field type
//! keeps its layout info, an exported conformance keeps its private
//! witness schemes — without becoming importable names (imports and
//! member lookup still consult the visibility records).

use rustc_hash::{FxHashMap, FxHashSet};

use crate::compiling::module::ModuleTypes;
use crate::name_resolution::name_resolver::ResolvedNames;
use crate::name_resolution::symbol::Symbol;
use crate::node_kinds::decl::Visibility;
use crate::types::TypeOutput;
use crate::types::catalog::{ConformanceId, MemberOwner};
use crate::types::ty::ParamKind;

pub(crate) struct PublicInterface {
    pub symbol_names: FxHashMap<Symbol, String>,
    pub types: ModuleTypes,
}

pub(crate) fn split_public_interface(
    resolved: &ResolvedNames,
    types: TypeOutput,
    own: impl Fn(&Symbol) -> bool,
) -> PublicInterface {
    let TypeOutput {
        mut catalog,
        schemes,
        ..
    } = types;

    // A locally declared symbol an importer may not name. Foreign and
    // builtin symbols have no record here and are importable by
    // construction.
    let local_private = |symbol: &Symbol| {
        resolved
            .declarations
            .get(symbol)
            .is_some_and(|record| record.effective != Visibility::Public)
    };

    let mut keep: FxHashSet<Symbol> = FxHashSet::default();
    let mut queue: Vec<Symbol> = Vec::new();
    for (&symbol, record) in &resolved.declarations {
        if record.effective == Visibility::Public && keep.insert(symbol) {
            queue.push(symbol);
        }
    }

    // Generic-parameter symbols of kept contracts: the retention key
    // for the param-keyed side tables (bounds, static value types).
    let mut kept_params: FxHashSet<Symbol> = FxHashSet::default();

    // Row inclusion grows the reachable set (witness suppliers, assoc
    // bindings), and reachability admits more rows: iterate to fixpoint.
    let mut kept_rows: FxHashSet<ConformanceId> = FxHashSet::default();
    loop {
        while let Some(symbol) = queue.pop() {
            let mut found: FxHashSet<Symbol> = FxHashSet::default();
            if let Some(scheme) = schemes.get(&symbol) {
                scheme.referenced_symbols(&mut found);
                for param in &scheme.params {
                    kept_params.insert(param.symbol);
                }
                kept_params.extend(scheme.eff_params.iter().copied());
                kept_params.extend(scheme.row_params.iter().copied());
                kept_params.extend(scheme.perm_params.iter().copied());
            }
            if let Some(info) = catalog.structs.get(&symbol) {
                for param in &info.params {
                    kept_params.insert(param.symbol);
                    if let Some(default) = &param.default {
                        default.referenced_symbols(&mut found);
                    }
                    if let ParamKind::Static(value_ty) = &param.kind {
                        value_ty.referenced_symbols(&mut found);
                    }
                }
                // Every field type, private fields included: importers
                // need complete layout and teardown facts for values
                // that flow across the boundary.
                for (_, (_, field_ty)) in &info.fields {
                    field_ty.referenced_symbols(&mut found);
                }
                for predicate in &info.predicates {
                    predicate.referenced_symbols(&mut found);
                }
            }
            if let Some(info) = catalog.enums.get(&symbol) {
                for param in &info.params {
                    kept_params.insert(param.symbol);
                    if let Some(default) = &param.default {
                        default.referenced_symbols(&mut found);
                    }
                    if let ParamKind::Static(value_ty) = &param.kind {
                        value_ty.referenced_symbols(&mut found);
                    }
                }
                for variant in info.variants.values() {
                    variant.constructor_scheme.referenced_symbols(&mut found);
                }
                for predicate in &info.predicates {
                    predicate.referenced_symbols(&mut found);
                }
            }
            if let Some(info) = catalog.protocols.get(&symbol) {
                for param in &info.params {
                    kept_params.insert(param.symbol);
                }
                for requirements in info.requirements.values() {
                    for requirement in requirements {
                        found.insert(requirement.symbol);
                    }
                }
                for &assoc in info.assoc.values() {
                    found.insert(assoc);
                }
                for super_ref in &info.supers {
                    found.insert(super_ref.protocol);
                    for arg in &super_ref.args {
                        arg.referenced_symbols(&mut found);
                    }
                }
                for predicate in &info.predicates {
                    predicate.referenced_symbols(&mut found);
                }
            }
            if let Some(signature) = catalog.effects.get(&symbol) {
                for generic in &signature.generics {
                    kept_params.insert(generic.symbol);
                }
                for param in &signature.params {
                    param.referenced_symbols(&mut found);
                }
                signature.ret.referenced_symbols(&mut found);
                for predicate in &signature.predicates {
                    predicate.referenced_symbols(&mut found);
                }
            }
            if let Some(alias) = catalog.type_aliases.get(&symbol) {
                alias.ty.referenced_symbols(&mut found);
            }
            // A nested type's identity includes its enclosing owner.
            if let Some(&owner) = catalog.nominal_owners.get(&symbol) {
                found.insert(owner);
            }
            for symbol in found {
                if keep.insert(symbol) {
                    queue.push(symbol);
                }
            }
        }

        let mut grew = false;
        for (&id, row) in &catalog.conformances {
            if kept_rows.contains(&id) || !keep.contains(&row.head) {
                continue;
            }
            // A conformance exports only when its COMPLETE conclusion is
            // publicly nameable (ADR 0042 §1): head, target protocol,
            // instance-head arguments, context, and associated bindings.
            // A private type anywhere in the conclusion keeps the row
            // file-private; witnesses are suppliers and do not gate.
            let conclusion_nameable = !local_private(&row.head)
                && !local_private(&row.protocol.protocol)
                && {
                    let mut named: FxHashSet<Symbol> = FxHashSet::default();
                    for arg in &row.protocol.args {
                        arg.referenced_symbols(&mut named);
                    }
                    for ty in &row.self_args {
                        ty.referenced_symbols(&mut named);
                    }
                    for predicate in &row.context {
                        predicate.referenced_symbols(&mut named);
                    }
                    for ty in row.assoc.values() {
                        ty.referenced_symbols(&mut named);
                    }
                    named.iter().all(|symbol| !local_private(symbol))
                };
            if !conclusion_nameable {
                continue;
            }
            kept_rows.insert(id);
            grew = true;
            kept_params.extend(row.params.iter().copied());
            let mut found: FxHashSet<Symbol> = FxHashSet::default();
            found.insert(row.protocol.protocol);
            for arg in &row.protocol.args {
                arg.referenced_symbols(&mut found);
            }
            for ty in &row.self_args {
                ty.referenced_symbols(&mut found);
            }
            for predicate in &row.context {
                predicate.referenced_symbols(&mut found);
            }
            for (&assoc, ty) in &row.assoc {
                found.insert(assoc);
                ty.referenced_symbols(&mut found);
            }
            // Witness suppliers cross as linkage, never as importable
            // names: their schemes travel because the row references
            // them.
            for &witness in row.witnesses.values() {
                found.insert(witness);
            }
            for entry in &row.dictionary {
                if let crate::types::catalog::DictionaryEntry::Implementation {
                    symbol, ..
                } = entry
                {
                    found.insert(*symbol);
                }
            }
            for symbol in found {
                if keep.insert(symbol) {
                    queue.push(symbol);
                }
            }
        }
        if !grew && queue.is_empty() {
            break;
        }
    }

    catalog.structs.retain(|symbol, _| keep.contains(symbol));
    catalog.enums.retain(|symbol, _| keep.contains(symbol));
    catalog.protocols.retain(|symbol, _| keep.contains(symbol));
    catalog.effects.retain(|symbol, _| keep.contains(symbol));
    catalog.type_aliases.retain(|symbol, _| keep.contains(symbol));
    catalog
        .nominal_owners
        .retain(|symbol, _| keep.contains(symbol));
    catalog
        .callable_contracts
        .retain(|symbol, _| keep.contains(symbol));
    catalog.conformances.retain(|id, _| kept_rows.contains(id));
    catalog.conformances_by_head.clear();
    let heads: Vec<(Symbol, ConformanceId)> = catalog
        .conformances
        .iter()
        .map(|(&id, row)| (row.head, id))
        .collect();
    for (head, id) in heads {
        catalog.conformances_by_head.entry(head).or_default().push(id);
    }
    // Param-keyed side tables retain entries for kept contracts'
    // parameters and reachable associated types only.
    catalog
        .param_bounds
        .retain(|symbol, _| kept_params.contains(symbol) || keep.contains(symbol));
    catalog
        .static_params
        .retain(|symbol, _| kept_params.contains(symbol) || keep.contains(symbol));
    // Improvement candidates never come from declarations an importer
    // cannot reach.
    for owners in catalog.member_owners.values_mut() {
        owners.retain(|owner| match owner {
            MemberOwner::Protocol(symbol) | MemberOwner::Nominal(symbol) => {
                keep.contains(symbol)
            }
        });
    }
    catalog.member_owners.retain(|_, owners| !owners.is_empty());
    // Extension rows of reachable heads, public members only.
    catalog
        .extend_members
        .retain(|head, _| keep.contains(head));
    for members in catalog.extend_members.values_mut() {
        for rows in members.values_mut() {
            rows.retain(|row| keep.contains(&row.symbol));
        }
        members.retain(|_, rows| !rows.is_empty());
    }
    catalog.extend_members.retain(|_, members| !members.is_empty());
    // Accessibility records must cover every member an importer can
    // still see in the retained tables, so all own records stay: an
    // absent entry means unrestricted.
    catalog.member_visibility.retain(|symbol, _| own(symbol));
    // Derived indexes are rebuilt over the filtered rows.
    catalog.commit_deinit_rows();
    catalog.commit_dictionaries();
    catalog.commit_callable_owners();

    let schemes = schemes
        .into_iter()
        .filter(|(symbol, _)| own(symbol) && keep.contains(symbol))
        .map(|(symbol, scheme)| (symbol, scheme.sanitize_for_export(symbol)))
        .collect();
    let symbol_names = resolved
        .symbol_names
        .iter()
        .filter(|(symbol, _)| own(symbol) && keep.contains(symbol))
        .map(|(&symbol, name)| (symbol, name.clone()))
        .collect();

    PublicInterface {
        symbol_names,
        types: ModuleTypes { schemes, catalog },
    }
}
