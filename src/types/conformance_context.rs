use indexmap::IndexMap;
use itertools::Itertools;

use crate::{
    compiling::module::ModuleEnvironment,
    label::Label,
    name_resolution::{
        name_resolver::ResolvedNames,
        symbol::{ProtocolId, Symbol},
    },
    node_id::NodeID,
    span::Span,
    types::{
        conformance::{
            ConformanceClaim, ConformanceEvidence, ConformanceKey, ConformanceObligation,
            ConformanceOrigin,
        },
        infer_ty::Ty,
        type_catalog::TypeCatalog,
    },
};

#[derive(Debug, Clone, PartialEq)]
pub(crate) enum ProjectionResolution {
    Alias(Symbol),
    Witness(Ty),
    PendingSlot(ConformanceKey),
}

#[derive(Debug, Default)]
pub(crate) struct ConformanceContext {
    obligations: IndexMap<ConformanceKey, ConformanceObligation>,
}

impl ConformanceContext {
    pub(crate) fn declare_obligation(&mut self, obligation: ConformanceObligation) {
        let key = obligation.key();
        if let Some(existing) = self.obligations.get_mut(&key) {
            existing.merge(obligation);
        } else {
            self.obligations.insert(key, obligation);
        }
    }

    pub(crate) fn associated_type_slot(
        &mut self,
        catalog: &mut TypeCatalog,
        modules: &ModuleEnvironment,
        key: ConformanceKey,
        label: &Label,
        ty: Ty,
    ) -> Ty {
        if let Some(existing) = self.lookup_associated_type_slot(&key, label) {
            return existing;
        }

        let obligation = self
            .lookup_claim(catalog, modules, &key)
            .map(|claim| ConformanceObligation::from_claim(&claim))
            .unwrap_or_else(|| {
                ConformanceObligation::new(
                    NodeID::SYNTHESIZED,
                    key.conforming_id,
                    key.protocol_id,
                    Span::SYNTHESIZED,
                )
            });
        self.declare_obligation(obligation);
        self.obligations
            .get_mut(&key)
            .unwrap_or_else(|| unreachable!())
            .associated_types
            .insert(label.clone(), ty.clone());
        ty
    }

    pub(crate) fn lookup_associated_type_slot(
        &self,
        key: &ConformanceKey,
        label: &Label,
    ) -> Option<Ty> {
        self.obligations
            .get(key)
            .and_then(|obligation| obligation.associated_types.get(label))
            .cloned()
    }

    pub(crate) fn lookup_claim(
        &mut self,
        catalog: &mut TypeCatalog,
        modules: &ModuleEnvironment,
        key: &ConformanceKey,
    ) -> Option<ConformanceClaim> {
        if let Some(claim) = catalog.conformance_claims.get(key) {
            return Some(claim.clone());
        }

        if let Some(claim) = modules.lookup_conformance_claim(key) {
            catalog.conformance_claims.insert(*key, claim.clone());
            return Some(claim.clone());
        }

        None
    }

    pub(crate) fn lookup_evidence(
        &mut self,
        catalog: &mut TypeCatalog,
        modules: &ModuleEnvironment,
        key: &ConformanceKey,
    ) -> Option<ConformanceEvidence> {
        if let Some(conformance) = catalog.conformance_evidence.get(key) {
            return Some(conformance.clone());
        }

        if let Some(conformance) = modules.lookup_conformance(key) {
            catalog
                .conformance_evidence
                .insert(*key, conformance.clone());
            return Some(conformance.clone());
        }

        None
    }

    pub(crate) fn conformance_seed(
        &mut self,
        catalog: &mut TypeCatalog,
        modules: &ModuleEnvironment,
        key: ConformanceKey,
        seed: Option<ConformanceEvidence>,
    ) -> Option<ConformanceEvidence> {
        self.lookup_evidence(catalog, modules, &key).or_else(|| {
            self.lookup_claim(catalog, modules, &key)
                .as_ref()
                .map(ConformanceEvidence::from_claim)
                .or(seed)
        })
    }

    pub(crate) fn protocol_implies(
        &mut self,
        catalog: &mut TypeCatalog,
        modules: &ModuleEnvironment,
        source_protocol_id: ProtocolId,
        target_protocol_id: ProtocolId,
    ) -> bool {
        let key = ConformanceKey {
            conforming_id: Symbol::Protocol(source_protocol_id),
            protocol_id: target_protocol_id,
        };

        catalog.conformance_evidence.contains_key(&key)
            || catalog.conformance_claims.contains_key(&key)
            || self.lookup_claim(catalog, modules, &key).is_some()
    }

    pub(crate) fn superprotocol_keys_for(
        &self,
        catalog: &TypeCatalog,
        protocol_id: ProtocolId,
    ) -> Vec<ConformanceKey> {
        let mut keys = catalog
            .conformance_evidence
            .keys()
            .chain(catalog.conformance_claims.keys())
            .chain(self.obligations.keys())
            .filter(|key| key.conforming_id == Symbol::Protocol(protocol_id))
            .copied()
            .collect_vec();
        keys.sort();
        keys.dedup();
        keys
    }

    pub(crate) fn claimed_protocols_for(
        &self,
        catalog: &TypeCatalog,
        symbol: Symbol,
    ) -> Vec<ProtocolId> {
        let mut protocols = catalog
            .conformance_claims
            .keys()
            .chain(self.obligations.keys())
            .filter(|key| key.conforming_id == symbol)
            .map(|key| key.protocol_id)
            .collect_vec();
        protocols.sort();
        protocols.dedup();
        protocols
    }

    pub(crate) fn associated_type_candidate(
        &mut self,
        catalog: &mut TypeCatalog,
        modules: &ModuleEnvironment,
        resolved_names: &ResolvedNames,
        key: ConformanceKey,
        label: &Label,
        origin: ConformanceOrigin,
    ) -> Option<Symbol> {
        let claim = self.lookup_claim(catalog, modules, &key);
        if let Some(sym) = claim
            .as_ref()
            .and_then(|claim| claim.associated_type_candidates.get(label))
            .copied()
        {
            return Some(sym);
        }

        if claim.is_none() && !matches!(origin, ConformanceOrigin::Declared) {
            return Self::child_type_symbol(catalog, resolved_names, &key.conforming_id, label);
        }

        None
    }

    pub(crate) fn method_candidate(
        &mut self,
        catalog: &mut TypeCatalog,
        modules: &ModuleEnvironment,
        key: ConformanceKey,
        label: &Label,
    ) -> Option<Symbol> {
        self.lookup_claim(catalog, modules, &key)
            .and_then(|claim| claim.method_candidates.get(label).copied())
    }

    pub(crate) fn resolve_associated_projection(
        &mut self,
        catalog: &mut TypeCatalog,
        modules: &ModuleEnvironment,
        resolved_names: &ResolvedNames,
        protocol_id: Option<ProtocolId>,
        base_sym: Symbol,
        label: &Label,
    ) -> Option<ProjectionResolution> {
        if let Some(protocol_id) = protocol_id {
            let key = ConformanceKey {
                protocol_id,
                conforming_id: base_sym,
            };
            return self.resolve_associated_projection_for_key(
                catalog,
                modules,
                resolved_names,
                key,
                label,
            );
        }

        let conformance = catalog
            .conformance_evidence
            .iter()
            .find(|(_, conformance)| conformance.conforming_id == base_sym)
            .map(|(key, conformance)| (*key, conformance.clone()));

        let Some((key, conformance)) = conformance else {
            return None;
        };

        if let Some(alias) = self.projection_alias_for(catalog, modules, resolved_names, key, label)
        {
            return Some(ProjectionResolution::Alias(alias));
        }

        conformance
            .witnesses
            .associated_types
            .get(label)
            .filter(|witness| !matches!(witness, Ty::Param(..)))
            .cloned()
            .map(ProjectionResolution::Witness)
    }

    fn resolve_associated_projection_for_key(
        &mut self,
        catalog: &mut TypeCatalog,
        modules: &ModuleEnvironment,
        resolved_names: &ResolvedNames,
        key: ConformanceKey,
        label: &Label,
    ) -> Option<ProjectionResolution> {
        if let Some(conformance) = self.lookup_evidence(catalog, modules, &key) {
            if let Some(alias) =
                self.projection_alias_for(catalog, modules, resolved_names, key, label)
            {
                return Some(ProjectionResolution::Alias(alias));
            }

            if let Some(witness) = conformance
                .witnesses
                .associated_types
                .get(label)
                .filter(|witness| !matches!(witness, Ty::Param(..)))
                .cloned()
            {
                return Some(ProjectionResolution::Witness(witness));
            }
        }

        let has_claim = self.lookup_claim(catalog, modules, &key).is_some();
        let has_obligation = self.obligations.contains_key(&key);
        if !(has_claim || has_obligation) {
            return None;
        }

        if let Some(alias) = self.projection_alias_for(catalog, modules, resolved_names, key, label)
        {
            return Some(ProjectionResolution::Alias(alias));
        }

        Some(ProjectionResolution::PendingSlot(key))
    }

    fn projection_alias_for(
        &mut self,
        catalog: &mut TypeCatalog,
        modules: &ModuleEnvironment,
        resolved_names: &ResolvedNames,
        key: ConformanceKey,
        label: &Label,
    ) -> Option<Symbol> {
        self.lookup_claim(catalog, modules, &key)
            .and_then(|claim| claim.associated_type_candidates.get(label).copied())
            .or_else(|| Self::child_type_symbol(catalog, resolved_names, &key.conforming_id, label))
    }

    fn child_type_symbol(
        catalog: &TypeCatalog,
        resolved_names: &ResolvedNames,
        symbol: &Symbol,
        label: &Label,
    ) -> Option<Symbol> {
        resolved_names
            .child_types
            .get(symbol)
            .and_then(|types| types.get(label))
            .copied()
            .or_else(|| {
                catalog
                    .child_types
                    .get(symbol)
                    .and_then(|types| types.get(label))
                    .copied()
            })
    }
}
