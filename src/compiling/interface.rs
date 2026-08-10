//! A module's exported slice (ADR 0053): export is SELECTION, not
//! surgery. The slice carries the module's own facts, whole — plus its
//! amendments to foreign entities (extension requirements added to an
//! imported protocol, retroactive conformance rows on imported heads,
//! bounds registered under foreign param/assoc symbols). Privacy is the
//! accessibility checks' job (ADR 0042); an importer sees every fact and
//! may use exactly what those checks admit. Derived indexes (deinit,
//! dictionaries, owner bindings) do not travel: the receiving table
//! re-derives them at the backend boundary.

use rustc_hash::FxHashMap;

use crate::{
    compiling::module::{ModuleId, ModuleTypes},
    name_resolution::{name_resolver::ResolvedNames, symbol::Symbol},
    types::TypeOutput,
};

pub(crate) struct PublicInterface {
    pub symbol_names: FxHashMap<Symbol, String>,
    pub types: ModuleTypes,
}

pub(crate) fn module_slice(
    resolved: &ResolvedNames,
    types: TypeOutput,
    own: impl Fn(&Symbol) -> bool,
    module_id: ModuleId,
) -> PublicInterface {
    let TypeOutput {
        mut catalog,
        schemes,
        ..
    } = types;

    catalog.structs.retain(|symbol, _| own(symbol));
    catalog.enums.retain(|symbol, _| own(symbol));
    catalog.effects.retain(|symbol, _| own(symbol));
    catalog.type_aliases.retain(|symbol, _| own(symbol));
    catalog.nominal_owners.retain(|symbol, _| own(symbol));
    catalog.callable_contracts.retain(|symbol, _| own(symbol));
    catalog.static_params.retain(|symbol, _| own(symbol));
    catalog.member_visibility.retain(|symbol, _| own(symbol));

    // A protocol entry is the module's own when it declared the protocol;
    // a FOREIGN protocol this module amended exports as a stub carrying
    // only the requirements this module added (`insert_slice` appends
    // them after the exporter's — the slot-prefix rule).
    catalog.protocols.retain(|symbol, info| {
        if own(symbol) {
            return true;
        }
        for set in info.requirements.values_mut() {
            set.retain(|requirement| own(&requirement.symbol));
        }
        info.requirements.retain(|_, set| !set.is_empty());
        !info.requirements.is_empty()
    });

    // A conformance row belongs to the module that DECLARED it —
    // retroactive rows on foreign heads included. Synthesized rows are
    // per-table derivations and never travel.
    catalog
        .conformances
        .retain(|id, row| id.module_id == module_id && !row.synthesized);
    catalog.conformances_by_head.clear();
    let ids: Vec<(Symbol, crate::types::catalog::ConformanceId)> = catalog
        .conformances
        .iter()
        .map(|(id, row)| (row.head, *id))
        .collect();
    for (head, id) in ids {
        catalog.conformances_by_head.entry(head).or_default().push(id);
    }

    // Amendment tables keyed by symbols this module may not own
    // (where-clause bounds under a foreign assoc symbol, member-owner
    // entries pointing new labels at a foreign protocol, inherent extend
    // rows on foreign heads): travel whole where additions are not
    // distinguishable from imported copies — `insert_slice` dedups.
    for members in catalog.extend_members.values_mut() {
        for rows in members.values_mut() {
            rows.retain(|row| own(&row.symbol));
        }
        members.retain(|_, rows| !rows.is_empty());
    }
    catalog.extend_members.retain(|_, members| !members.is_empty());

    // Derived indexes re-derive on the receiving side.
    catalog.deinit_rows.clear();
    catalog.callable_owners.clear();

    let schemes = schemes
        .into_iter()
        .filter(|(symbol, _)| own(symbol))
        .map(|(symbol, scheme)| (symbol, scheme.sanitize_for_export(symbol)))
        .collect();
    let symbol_names = resolved
        .symbol_names
        .iter()
        .filter(|(symbol, _)| own(symbol))
        .map(|(&symbol, name)| (symbol, name.clone()))
        .collect();

    PublicInterface {
        symbol_names,
        types: ModuleTypes { schemes, catalog },
    }
}
