use super::*;

impl<'s, 'a> BodyChecker<'s, 'a> {
    pub(super) fn join(&mut self, a: Ty, b: Ty, node: NodeID) -> Ty {
        if a.is_never() {
            return b;
        }
        if b.is_never() {
            return a;
        }
        self.emit_eq(a.clone(), b, node, CtReason::Branch);
        a
    }

    pub(super) fn emit_eq(&mut self, expected: Ty, found: Ty, node: NodeID, reason: CtReason) {
        self.wanteds
            .push(Constraint::Eq(expected, found, CtOrigin::new(node, reason)));
    }

    pub(super) fn emit_eff_eq(&mut self, a: EffectRow, b: EffectRow, node: NodeID) {
        self.wanteds.push(Constraint::EffEq(
            a,
            b,
            CtOrigin::new(node, CtReason::Effect),
        ));
    }

    pub(super) fn unsupported(&mut self, node: NodeID, what: &str) {
        self.diagnostics.unsupported(node, what);
    }
}

impl<'s, 'a> CatalogBuilder<'s, 'a> {
    pub(super) fn unsupported(&mut self, node: NodeID, what: &str) {
        self.diagnostics.unsupported(node, what);
    }
}

impl<'s, 'a> BindingGroupChecker<'s, 'a> {
    pub(super) fn group_owned_roots(&mut self, ty: &Ty, roots: &mut Vec<u32>) {
        let _ = self.store.query_resolved(ty, &mut |store, node| {
            if let TyNode::Ty(Ty::Var(v)) = node {
                let root = store.find(v.0);
                if store.level(root) > OUTER_LEVEL {
                    roots.push(root);
                }
            }
            ControlFlow::<()>::Continue(())
        });
    }

    pub(super) fn emit_eq(&mut self, expected: Ty, found: Ty, node: NodeID, reason: CtReason) {
        self.wanteds
            .push(Constraint::Eq(expected, found, CtOrigin::new(node, reason)));
    }

    pub(super) fn unsupported(&mut self, node: NodeID, what: &str) {
        self.diagnostics.unsupported(node, what);
    }
}

impl<'a> TypecheckSession<'a> {
    fn final_ty(&mut self, ty: &Ty) -> Ty {
        final_ty(&mut self.store, &self.catalog, ty)
    }

    fn zonk_predicate(&mut self, predicate: Predicate) -> Predicate {
        zonk_predicate(&mut self.store, &self.catalog, predicate)
    }

    /// The borrowed-to-owned judgment for an implicit existential pack's
    /// payload (the deferred twin of `solve_coerce_owned`'s tier-2 rule):
    /// a borrow of a Copy payload is a value copy, a CheapClone payload
    /// retains (recorded in `coerce_clones` for lowering), and anything
    /// else — linear or uniquely-owned — is an error. Returns the owned
    /// payload type the pack carries forward.
    fn check_pack_payload_ownership(&mut self, node: NodeID, payload: Ty) -> Ty {
        let Ty::Borrow(perm, inner) = payload else {
            return payload;
        };
        let coerces = match &*inner {
            Ty::Nominal(symbol, args) => {
                match self.catalog.coerce_kind_application(*symbol, args) {
                    Some(kind) => {
                        if kind == crate::types::catalog::CoerceKind::CheapClone {
                            self.artifacts.coerce_clones.insert(node);
                        }
                        true
                    }
                    None => false,
                }
            }
            Ty::Param(param) => {
                let bounds = self
                    .catalog
                    .param_bounds
                    .get(param)
                    .cloned()
                    .unwrap_or_default();
                match self.catalog.bounds_coerce_kind(&bounds) {
                    Some(kind) => {
                        if kind == crate::types::catalog::CoerceKind::CheapClone {
                            self.artifacts.coerce_clones.insert(node);
                        }
                        true
                    }
                    None => false,
                }
            }
            _ => false,
        };
        if coerces {
            *inner
        } else {
            let expected = self.store.render(&inner);
            let found = self.store.render(&Ty::Borrow(perm, inner.clone()));
            self.diagnostics.errors.push((
                TypeError::Mismatch {
                    expected,
                    found,
                    reason: CtReason::Body,
                },
                node,
            ));
            Ty::Borrow(perm, inner)
        }
    }

    /// Whether a `copy`-marked argument of this (resolved) type has the
    /// evidence an explicit clone requires: Copy or CheapClone, judged
    /// through a borrow and componentwise through tuples.
    fn copy_marker_coerces(&self, ty: &Ty) -> bool {
        match ty {
            Ty::Borrow(_, inner) => self.copy_marker_coerces(inner),
            Ty::Tuple(items) => items.iter().all(|item| self.copy_marker_coerces(item)),
            Ty::Nominal(symbol, args) => self
                .catalog
                .coerce_kind_application(*symbol, args)
                .is_some(),
            Ty::Param(param) => {
                let bounds = self
                    .catalog
                    .param_bounds
                    .get(param)
                    .cloned()
                    .unwrap_or_default();
                self.catalog.bounds_coerce_kind(&bounds).is_some()
            }
            Ty::Error => true,
            _ => false,
        }
    }

    pub(super) fn finalize(mut self) -> (TypeOutput, Vec<AnyDiagnostic>) {
        // ADR 0035 §5: no unresolved static metavariable may survive
        // finalization. A hole with no unique solution reports here, at
        // the use that minted it, before it degrades with the other
        // leftover variables.
        for origin in self.store.unresolved_static_holes() {
            self.diagnostics
                .errors
                .push((TypeError::UnderdeterminedStaticArgument, origin));
        }
        // Call-site marker checks (ADR 0038): typing owns marker
        // legality; lowering only realizes the already-checked use.
        // `copy` needs Copy/CheapClone evidence; `mut` and `borrow`
        // must agree with the callee's parameter mode.
        for (node, slot, mode) in std::mem::take(&mut self.artifacts.marked_args) {
            use crate::parsing::node_kinds::call_arg::ArgMode;
            // The parameter type the marker must agree with. Through an
            // unresolved callee, index its solved function type from the
            // right (member types may exclude the receiver); an
            // unresolved or non-function callee already errored.
            let param = match &slot {
                MarkedSlot::Param(ty) => Some(self.final_ty(ty)),
                MarkedSlot::CalleeIndexed {
                    callee,
                    index,
                    arg_count,
                    ..
                } => {
                    let mut callee = self.final_ty(callee);
                    while let Ty::Borrow(_, inner) = callee {
                        callee = *inner;
                    }
                    match callee {
                        Ty::Func(params, _, _) if params.len() >= *arg_count => {
                            Some(params[params.len() - arg_count + index].clone())
                        }
                        _ => None,
                    }
                }
            };
            match mode {
                ArgMode::Copy => {
                    // Evidence is about the value the copy duplicates:
                    // the argument's own type when the slot came through
                    // an unresolved callee.
                    let ty = match &slot {
                        MarkedSlot::Param(_) => param.clone(),
                        MarkedSlot::CalleeIndexed { arg_ty, .. } => Some(self.final_ty(arg_ty)),
                    };
                    if let Some(ty) = ty
                        && !self.copy_marker_coerces(&ty)
                    {
                        let rendered = self.store.render(&ty);
                        self.diagnostics.errors.push((
                            TypeError::NotConforming {
                                ty: rendered,
                                protocol: "Copy or CheapClone".to_string(),
                            },
                            node,
                        ));
                    }
                }
                ArgMode::Mut => {
                    if let Some(param) = param
                        && !matches!(param, Ty::Error | Ty::Borrow(Perm::Exclusive, _))
                    {
                        self.diagnostics.errors.push((
                            TypeError::ArgMarkerMismatch {
                                marker: "mut".to_string(),
                                requires: "a `mut` parameter".to_string(),
                            },
                            node,
                        ));
                    }
                }
                ArgMode::Borrow => {
                    if let Some(param) = param
                        && !matches!(param, Ty::Error | Ty::Borrow(_, _))
                    {
                        self.diagnostics.errors.push((
                            TypeError::ArgMarkerMismatch {
                                marker: "borrow".to_string(),
                                requires: "a borrowing parameter".to_string(),
                            },
                            node,
                        ));
                    }
                }
                ArgMode::Consume => {}
            }
        }
        let mut schemes = FxHashMap::default();
        for (symbol, mut scheme) in std::mem::take(&mut self.schemes) {
            let ty = self.final_ty(&scheme.ty);
            scheme.predicates = scheme
                .predicates
                .into_iter()
                .map(|predicate| self.zonk_predicate(predicate))
                .collect();
            schemes.insert(symbol, Scheme { ty, ..scheme });
        }
        let mut node_types = FxHashMap::default();
        for (node, ty) in std::mem::take(&mut self.artifacts.node_types) {
            node_types.insert(node, self.final_ty(&ty));
        }
        let mut instantiations = FxHashMap::default();
        for (node, subst) in std::mem::take(&mut self.artifacts.instantiations) {
            let mut finalized = vec![];
            for (sym, ty) in subst {
                finalized.push((sym, self.final_ty(&ty)));
            }
            instantiations.insert(node, finalized);
        }
        let mut member_resolutions = FxHashMap::default();
        for (node, resolution) in std::mem::take(&mut self.artifacts.member_resolutions) {
            let resolution = match resolution {
                MemberResolution::Direct(symbol) => MemberResolution::Direct(symbol),
                MemberResolution::ViaConformance {
                    row,
                    protocol,
                    witness,
                    substitution,
                } => {
                    let protocol = ProtocolRef {
                        protocol: protocol.protocol,
                        args: protocol.args.iter().map(|arg| self.final_ty(arg)).collect(),
                    };
                    let substitution = substitution
                        .iter()
                        .map(|(symbol, ty)| (*symbol, self.final_ty(ty)))
                        .collect();
                    MemberResolution::ViaConformance {
                        row,
                        protocol: self.catalog.canonical_protocol_ref(protocol),
                        witness,
                        substitution,
                    }
                }
                MemberResolution::ViaRequirement {
                    protocol,
                    requirement,
                    self_ty,
                } => {
                    let protocol = ProtocolRef {
                        protocol: protocol.protocol,
                        args: protocol.args.iter().map(|arg| self.final_ty(arg)).collect(),
                    };
                    let protocol = self.catalog.canonical_protocol_ref(protocol);
                    let self_ty = self.final_ty(&self_ty);
                    let mut matches = match &self_ty {
                        Ty::Nominal(head, args) => {
                            self.catalog.matching_conformances(*head, args, &protocol)
                        }
                        _ => Vec::new(),
                    };
                    if matches.is_empty() && matches!(self_ty, Ty::Nominal(..)) {
                        matches = self
                            .catalog
                            .matching_protocol_head_conformances(&self_ty, &protocol);
                    }
                    let selected = match matches.as_slice() {
                        [selected] => Some(selected),
                        _ => None,
                    };
                    let commitment = selected.and_then(|selected| {
                        let info = self.catalog.protocols.get(&protocol.protocol)?;
                        let (label, candidate) = info
                            .requirements
                            .iter()
                            .flat_map(|(label, set)| set.iter().map(move |req| (label, req)))
                            .find(|(_, candidate)| candidate.symbol == requirement)?;
                        let key = self.catalog.witness_key(
                            protocol.protocol,
                            label,
                            candidate.symbol,
                        );
                        // A row without a witness for the label is
                        // recipe-backed (a synthesized derivation) unless
                        // the requirement carries a default body; the
                        // recipe case stays ViaRequirement so the backend
                        // dereferences the committed dictionary entry.
                        let witness = match selected.conformance.witnesses.get(&key).copied() {
                            Some(witness) => witness,
                            None if candidate.has_default => requirement,
                            None => return None,
                        };
                        let mut substitution = selected.evidence_substitution();
                        substitution.push((protocol.protocol, self_ty.clone()));
                        substitution.extend(
                            info.params
                                .iter()
                                .zip(&protocol.args)
                                .map(|(param, arg)| (param.symbol, arg.clone())),
                        );
                        Some(MemberResolution::ViaConformance {
                            row: selected.id,
                            protocol: protocol.clone(),
                            witness,
                            substitution,
                        })
                    });
                    commitment.unwrap_or(MemberResolution::ViaRequirement {
                        protocol,
                        requirement,
                        self_ty,
                    })
                }
            };
            member_resolutions.insert(node, resolution);
        }
        let mut for_plans = FxHashMap::default();
        for (node, plan) in std::mem::take(&mut self.artifacts.for_plans) {
            for_plans.insert(
                node,
                ForPlan {
                    iterator_ty: self.final_ty(&plan.iterator_ty),
                    element_ty: self.final_ty(&plan.element_ty),
                    next_result_ty: self.final_ty(&plan.next_result_ty),
                    body_ty: self.final_ty(&plan.body_ty),
                    ..plan
                },
            );
        }
        // Catalog types outlive this module's solver store (importers'
        // stores don't share its ids): bake in everything solving
        // inferred, then degrade genuine leftovers per the export
        // sanitizer — a raw variable crossing the boundary reads foreign
        // store slots (mis-unification, or the flatten_eff panic).
        // ONE walk covers every embedded type (`for_each_embedded_mut`
        // is the single authority for what the catalog carries); the
        // normalization context is a pre-bake snapshot, since projection
        // reduction consults the catalog being rewritten.
        let mut catalog = std::mem::take(&mut self.catalog);
        let normalize_ctx = catalog.clone();
        let store = &mut self.store;
        catalog.for_each_embedded_mut(&mut |owner, item| match item {
            crate::types::catalog::EmbeddedTypes::Ty(ty) => {
                *ty = final_ty(store, &normalize_ctx, ty).sanitize_for_export(owner);
            }
            crate::types::catalog::EmbeddedTypes::Scheme(scheme) => {
                let ty = final_ty(store, &normalize_ctx, &scheme.ty);
                *scheme = Scheme {
                    ty,
                    ..scheme.clone()
                }
                .sanitize_for_export(owner);
            }
            crate::types::catalog::EmbeddedTypes::Predicate(predicate) => {
                *predicate = zonk_predicate(store, &normalize_ctx, predicate.clone())
                    .sanitize_for_export(owner);
            }
        });
        // Protocol-head rows use Ty::Param(protocol) as the axiom Self
        // placeholder. Default-body normalization collapses that projection
        // to the associated param, but axiom contexts must keep the projection
        // so use-site substitution ties target args back to the receiver.
        let protocol_head_assoc: FxHashMap<Symbol, Vec<(ProtocolRef, Symbol)>> = catalog
            .protocols
            .iter()
            .map(|(protocol, info)| {
                let protocol_ref = ProtocolRef {
                    protocol: *protocol,
                    args: info.params.iter().map(|p| Ty::Param(p.symbol)).collect(),
                };
                let assocs = info
                    .assoc
                    .values()
                    .copied()
                    .map(|assoc| (protocol_ref.clone(), assoc))
                    .collect();
                (*protocol, assocs)
            })
            .collect();
        for conformance in catalog.conformances.values_mut() {
            let head = conformance.head;
            let Some(assocs) = protocol_head_assoc.get(&head) else {
                continue;
            };
            for (owner, assoc) in assocs {
                let lhs = Ty::Param(*assoc);
                let rhs = Ty::Proj(Box::new(Ty::Param(head)), owner.clone(), *assoc);
                if let Some(predicate) = conformance.context.iter_mut().find(|predicate| {
                    matches!(predicate, Predicate::TypeEq(a, b) if *a == lhs && *b == lhs)
                }) {
                    *predicate = Predicate::TypeEq(lhs, rhs);
                }
            }
        }
        self.catalog = catalog;
        let mut existential_packs = FxHashMap::default();
        for (node, pack) in std::mem::take(&mut self.artifacts.existential_packs) {
            let existential = self.final_ty(&pack.existential);
            let payload = self.final_ty(&pack.payload);
            // An implicit pack OWNS its payload, so a borrowed source gets
            // the same judgment as every other borrowed-to-owned coercion:
            // a free copy (Copy), an O(1) retain (CheapClone, recorded for
            // lowering at the pack node), or a type error. Without this a
            // borrowed payload launders into an owned `any P` — and a
            // borrowed `'linear` value stays consumable at the call site
            // (ownership-soundness plan B4 / ADR 0018's known gap). Sits
            // here, post-solve, so payloads that resolve late (deferred
            // member results, pattern binders) get the same gate.
            let payload = self.check_pack_payload_ownership(node, payload);
            existential_packs.insert(
                node,
                ExistentialPack {
                    existential,
                    payload,
                },
            );
        }

        let mut local_tys = FxHashMap::default();
        for (symbol, ty) in std::mem::take(&mut self.mono) {
            local_tys.insert(symbol, self.final_ty(&ty));
        }

        let mut pattern_tys = FxHashMap::default();
        for (node, ty) in std::mem::take(&mut self.artifacts.pattern_tys) {
            pattern_tys.insert(node, self.final_ty(&ty));
        }

        let mut struct_pattern_slots = FxHashMap::default();
        for (node, slots) in std::mem::take(&mut self.artifacts.struct_pattern_slots) {
            let slots: Vec<(Ty, Option<crate::node_id::NodeID>)> = slots
                .into_iter()
                .map(|(ty, sub)| (self.final_ty(&ty), sub))
                .collect();
            struct_pattern_slots.insert(node, slots);
        }

        // Record-pattern slots assemble here, once the row has solved:
        // the final row fixes the layout order; the recorded labels map
        // each slot to its written field. Open or non-record occurrences
        // publish nothing (lowering rejects them as unsupported).
        let mut record_pattern_slots = FxHashMap::default();
        for (node, labels) in std::mem::take(&mut self.artifacts.record_pattern_labels) {
            let Some(occurrence) = pattern_tys.get(&node) else {
                continue;
            };
            let mut occurrence = occurrence.clone();
            while let Ty::Borrow(_, inner) = occurrence {
                occurrence = *inner;
            }
            let Ty::Record(row) = occurrence else {
                continue;
            };
            if row.tail.is_some() {
                continue;
            }
            let mut slots: Vec<(Ty, Option<crate::node_id::NodeID>)> = Vec::new();
            let mut named = true;
            for (label, ty) in &row.fields {
                let crate::label::Label::Named(label) = label else {
                    named = false;
                    break;
                };
                let field = labels
                    .iter()
                    .find(|(written, _)| written == label)
                    .map(|(_, id)| *id);
                slots.push((ty.clone(), field));
            }
            if named {
                record_pattern_slots.insert(node, slots);
            }
        }

        // Checked inline-IR ops carry embedded annotation types; zonk
        // them like every other published type.
        let mut checked_ir = std::mem::take(&mut self.artifacts.checked_ir);
        for kind in checked_ir.values_mut() {
            use crate::types::output::CheckedIrKind as C;
            match kind {
                C::Alloc { elem: ty, .. }
                | C::Retain { ty, .. }
                | C::Load { ty, .. }
                | C::Store { ty, .. }
                | C::Swap { ty, .. }
                | C::Take { ty, .. }
                | C::Gep { elem: ty, .. } => *ty = final_ty(&mut self.store, &self.catalog, ty),
                C::Scalar { .. }
                | C::Free { .. }
                | C::IsUnique { .. }
                | C::MemCopy { .. }
                | C::InlineGet { .. }
                | C::Io { .. } => {}
            }
        }

        let diagnostics = self
            .diagnostics
            .into_diagnostics(&self.artifacts.synthetic_origins);

        (
            TypeOutput {
                catalog: self.catalog,
                node_types,
                schemes,
                instantiations,
                member_resolutions,
                selected_callables: self.artifacts.selected_callables,
                integer_literals: self.artifacts.integer_literals,
                for_plans,
                propagation_plans: self.artifacts.propagation_plans,
                synthetic_floors: self.artifacts.synthetic_next,
                coerce_clones: self.artifacts.coerce_clones,
                local_tys,
                existential_packs,
                checked_ir,
                effect_contracts: self.artifacts.effect_contracts,
                pattern_tys,
                struct_pattern_slots,
                record_pattern_slots,
                display_names: self.artifacts.display_names,
            },
            diagnostics,
        )
    }
}

fn final_ty(store: &mut VarStore, catalog: &TypeCatalog, ty: &Ty) -> Ty {
    // All solving is done: a borrow permission nothing forced exclusive
    // defaults to `Shared` here (binding in the store, so sharers agree).
    let zonked = store.default_unsolved_perms(ty);
    normalize_deep(store, catalog, zonked)
}

fn normalize_deep(store: &mut VarStore, catalog: &TypeCatalog, ty: Ty) -> Ty {
    Normalizer { store, catalog }.fold_ty(&ty)
}

fn final_row(store: &mut VarStore, catalog: &TypeCatalog, row: Row) -> Row {
    Row {
        fields: row
            .fields
            .into_iter()
            .map(|(label, ty)| (label, normalize_deep(store, catalog, ty)))
            .collect(),
        tail: row.tail,
    }
}

fn zonk_predicate(store: &mut VarStore, catalog: &TypeCatalog, predicate: Predicate) -> Predicate {
    match predicate {
        Predicate::TypeEq(a, b) => {
            Predicate::TypeEq(final_ty(store, catalog, &a), final_ty(store, catalog, &b))
        }
        Predicate::EffectEq(a, b) => Predicate::EffectEq(store.zonk_eff(&a), store.zonk_eff(&b)),
        Predicate::RowEq(a, b) => {
            let a = store.zonk_row(&a);
            let b = store.zonk_row(&b);
            Predicate::RowEq(final_row(store, catalog, a), final_row(store, catalog, b))
        }
        Predicate::Conforms { ty, protocol } => Predicate::Conforms {
            ty: final_ty(store, catalog, &ty),
            protocol,
        },
        Predicate::HasMember {
            receiver,
            label,
            member,
        } => Predicate::HasMember {
            receiver: final_ty(store, catalog, &receiver),
            label,
            member: final_ty(store, catalog, &member),
        },
        Predicate::StaticCmp { op, lhs, rhs } => Predicate::StaticCmp {
            op,
            lhs: final_ty(store, catalog, &lhs),
            rhs: final_ty(store, catalog, &rhs),
        },
    }
}

struct Normalizer<'a> {
    store: &'a mut VarStore,
    catalog: &'a TypeCatalog,
}

impl TyFold for Normalizer<'_> {
    fn fold_ty(&mut self, ty: &Ty) -> Ty {
        let normalized = normalize_ty(self.store, self.catalog, ty);
        let rebuilt = self.fold_children(&normalized);
        match &rebuilt {
            Ty::Proj(..) => normalize_ty(self.store, self.catalog, &rebuilt),
            // `&Int` never surfaces (ADR 0014): a shared borrow of a
            // Copy-grade head IS the value. Annotation lowering erases the
            // wrap eagerly; this is the deferred twin for borrows whose
            // payload only resolved to a Copy head during solving (inferred
            // borrow-default params — plan 3.3(b) — and generic
            // instantiations at Int). Finalize-time only, so in-solve perm
            // unification (`&Int` vs `&mut Int`) is untouched.
            Ty::Borrow(perm, inner)
                if matches!(self.store.shallow_perm(*perm), Perm::Shared)
                    && matches!(&**inner, Ty::Nominal(symbol, args)
                        if self.catalog.grade_of_application(*symbol, args)
                            == crate::types::catalog::Grade::Copy) =>
            {
                (**inner).clone()
            }
            _ => rebuilt,
        }
    }
}
