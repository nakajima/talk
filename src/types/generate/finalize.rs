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

    pub(super) fn finalize(mut self) -> (TypeOutput, Vec<AnyDiagnostic>) {
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
                MemberResolution::ViaConformance { protocol, witness } => {
                    let protocol = ProtocolRef {
                        protocol: protocol.protocol,
                        args: protocol.args.iter().map(|arg| self.final_ty(arg)).collect(),
                    };
                    MemberResolution::ViaConformance {
                        protocol: self.catalog.canonical_protocol_ref(protocol),
                        witness,
                    }
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
        self.catalog = catalog;
        let mut existential_packs = FxHashMap::default();
        for (node, pack) in std::mem::take(&mut self.artifacts.existential_packs) {
            existential_packs.insert(
                node,
                ExistentialPack {
                    existential: self.final_ty(&pack.existential),
                    payload: self.final_ty(&pack.payload),
                },
            );
        }

        let mut local_tys = FxHashMap::default();
        for (symbol, ty) in std::mem::take(&mut self.mono) {
            local_tys.insert(symbol, self.final_ty(&ty));
        }

        let diagnostics = self.diagnostics.into_diagnostics();

        (
            TypeOutput {
                catalog: self.catalog,
                node_types,
                schemes,
                instantiations,
                member_resolutions,
                for_plans,
                synthetic_floors: self.artifacts.synthetic_next,
                coerce_clones: self.artifacts.coerce_clones,
                local_tys,
                existential_packs,
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
            _ => rebuilt,
        }
    }
}
