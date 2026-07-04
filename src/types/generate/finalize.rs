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
        // Catalog types outlive this module's solver store (importers'
        // stores don't share its ids): bake in everything solving
        // inferred, then degrade genuine leftovers per the export
        // sanitizer — a raw variable crossing the boundary reads foreign
        // store slots (mis-unification, or the flatten_eff panic).
        let mut effects = std::mem::take(&mut self.catalog.effects);
        for (symbol, sig) in effects.iter_mut() {
            sig.params = sig
                .params
                .iter()
                .map(|ty| self.final_ty(ty).sanitize_for_export(*symbol))
                .collect();
            sig.ret = self.final_ty(&sig.ret).sanitize_for_export(*symbol);
        }
        self.catalog.effects = effects;
        let mut structs = std::mem::take(&mut self.catalog.structs);
        for (symbol, info) in structs.iter_mut() {
            for (_, field_ty) in info.fields.values_mut() {
                *field_ty = self.final_ty(field_ty).sanitize_for_export(*symbol);
            }
        }
        self.catalog.structs = structs;
        let mut enums = std::mem::take(&mut self.catalog.enums);
        for (symbol, info) in enums.iter_mut() {
            for variant in info.variants.values_mut() {
                let ty = self.final_ty(&variant.constructor_scheme.ty);
                variant.constructor_scheme = Scheme {
                    ty,
                    ..variant.constructor_scheme.clone()
                }
                .sanitize_for_export(*symbol);
            }
        }
        self.catalog.enums = enums;
        let mut protocols = std::mem::take(&mut self.catalog.protocols);
        for info in protocols.values_mut() {
            for requirement in info.requirements.values_mut() {
                requirement.sig = self
                    .final_ty(&requirement.sig)
                    .sanitize_for_export(requirement.symbol);
            }
        }
        self.catalog.protocols = protocols;
        let mut extend_members = std::mem::take(&mut self.catalog.extend_members);
        for members in extend_members.values_mut() {
            for member in members.values_mut() {
                member.sig = self.final_ty(&member.sig).sanitize_for_export(member.symbol);
            }
        }
        self.catalog.extend_members = extend_members;
        let mut conformances = std::mem::take(&mut self.catalog.conformances);
        for ((head, _), conformance) in conformances.iter_mut() {
            for ty in conformance.assoc.values_mut() {
                *ty = self.final_ty(ty).sanitize_for_export(*head);
            }
        }
        self.catalog.conformances = conformances;
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
                member_resolutions: self.artifacts.member_resolutions,
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
