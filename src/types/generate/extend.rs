use super::*;

impl<'s, 'a> BindingGroupChecker<'s, 'a> {
    /// Check an extend's member bodies as a mini binding group, equating
    /// each witness against its requirement (this is what infers unannotated
    /// witness return types and rejects mismatched witnesses).
    pub(super) fn check_extend(&mut self, work: ExtendWork<'a>) {
        let DeclKind::Extend { body, .. } = &work.decl.kind else {
            return;
        };
        self.level = GROUP_LEVEL;
        debug_assert!(self.wanteds.is_empty());

        let group_eff = self.ambient_row();
        let group_ret = Ty::Var(self.store.fresh_ty(OUTER_LEVEL, NodeID::SYNTHESIZED));
        let group_ctx = Ctx::root().with_ret_eff(group_ret, group_eff);
        self.self_types.push(work.self_ty.clone());
        let extend_wanted_start = self.wanteds.len();

        let mut outputs: Vec<(Symbol, Ty, DeclaredSchemeContext)> = vec![];
        // Associated types without a declared binding are inferred from
        // the member bodies: remember the fresh variables so the solved
        // bindings can be written back into the conformance row (the
        // lowerer specializes default bodies from it).
        let mut inferred_assoc: Vec<((Symbol, Symbol), Symbol, Ty)> = vec![];
        for member in &body.decls {
            let DeclKind::Method { func, .. } = &member.kind else {
                continue;
            };
            let Ok(method) = func.name.symbol() else {
                continue;
            };
            self.register_func_bounds(func);
            let declared = self.declared_scheme_context(&func.generics, func.where_clause.as_ref());
            let ty = self.body().infer_func(func, &group_ctx.with_binder(method));

            // Witness ~ requirement (substituting Self and the conformance's
            // associated bindings).
            let label = func.name.name_str();
            for protocol in &work.protocols {
                let Some((owner, requirement)) = self.catalog.requirement_in(*protocol, &label)
                else {
                    continue;
                };
                let requirement = requirement.clone();
                let assoc_symbols: Vec<Symbol> = self
                    .catalog
                    .protocols
                    .get(&owner)
                    .map(|i| i.assoc.values().copied().collect())
                    .unwrap_or_default();
                let bindings = self
                    .catalog
                    .conformances
                    .get(&(head_symbol(&work.self_ty), owner))
                    .map(|c| c.assoc.clone())
                    .unwrap_or_default();

                let mut tys: FxHashMap<Symbol, Ty> = FxHashMap::default();
                tys.insert(owner, work.self_ty.clone());
                for assoc in assoc_symbols {
                    let binding = match bindings.get(&assoc) {
                        Some(bound) => bound.clone(),
                        None => {
                            let var = Ty::Var(self.store.fresh_ty(self.level, member.id));
                            inferred_assoc.push((
                                (head_symbol(&work.self_ty), owner),
                                assoc,
                                var.clone(),
                            ));
                            var
                        }
                    };
                    tys.insert(assoc, binding);
                }
                let mut effs = FxHashMap::default();
                effs.insert(
                    requirement.symbol,
                    EffTail::Var(self.store.fresh_eff(self.level, member.id)),
                );
                let expected = requirement.sig.substitute(&tys, &effs, &Default::default());
                let wanted = Constraint::Eq(
                    expected,
                    ty.clone(),
                    CtOrigin::new(member.id, CtReason::Annotation),
                );
                let givens: Vec<Predicate> = requirement
                    .predicates
                    .iter()
                    .map(|predicate| predicate.substitute(&tys, &effs, &Default::default()))
                    .collect();
                if givens.is_empty() {
                    self.wanteds.push(wanted);
                } else {
                    self.wanteds.push(Constraint::Implic(Box::new(Implication {
                        level: self.level,
                        givens,
                        wanteds: vec![wanted],
                        local_params: vec![],
                        touchable_level: None,
                    })));
                }
                break;
            }

            outputs.push((method, ty, declared));
        }

        if !work.context.is_empty() {
            let wanteds = self.wanteds.split_off(extend_wanted_start);
            if !wanteds.is_empty() {
                self.wanteds.push(Constraint::Implic(Box::new(Implication {
                    level: self.level,
                    givens: work.context.clone(),
                    wanteds,
                    local_params: vec![],
                    touchable_level: None,
                })));
            }
        }

        self.self_types.pop();

        let wanteds = std::mem::take(self.wanteds);
        let residuals = self.run_solver(wanteds);
        self.report_unresolved_residuals(residuals);

        for (symbol, ty, declared) in outputs {
            let zonked = self.store.zonk_ty(&ty);
            let mut scheme = Scheme::mono(zonked);
            // The witness's own generics quantify its scheme.
            scheme.params = declared.params.clone();
            scheme.predicates = declared.predicates.clone();
            self.diagnostics
                .errors
                .extend(Self::ambiguous_declared_predicate_errors(
                    &scheme, &declared,
                ));
            self.schemes.insert(symbol, scheme);
        }
        // Write the solved associated-type bindings back into the row.
        for (key, assoc, var) in inferred_assoc {
            let solved = self.store.zonk_ty(&var);
            if matches!(solved, Ty::Var(_)) {
                continue;
            }
            if let Some(conformance) = self.catalog.conformances.get_mut(&key) {
                conformance.assoc.entry(assoc).or_insert(solved);
            }
        }
    }

    /// Check one default-bodied requirement generically over Self.
    pub(super) fn check_protocol_default(
        &mut self,
        protocol: Symbol,
        requirement_symbol: Symbol,
        func: &'a Func,
    ) {
        self.level = GROUP_LEVEL;
        debug_assert!(self.wanteds.is_empty());

        // Self conforms to the protocol by construction; registering the
        // bound lets `self.other_requirement(...)` dispatch (and supers
        // resolve through the bounds closure).
        self.catalog
            .param_bounds
            .entry(protocol)
            .or_insert_with(|| vec![protocol]);

        let group_eff = self.ambient_row();
        let group_ret = Ty::Var(self.store.fresh_ty(OUTER_LEVEL, NodeID::SYNTHESIZED));
        let group_ctx = Ctx::root().with_ret_eff(group_ret, group_eff);
        self.self_types.push(Ty::Param(protocol));

        let inferred = self
            .body()
            .infer_func(func, &group_ctx.with_binder(requirement_symbol));
        let expected = self
            .catalog
            .protocols
            .get(&protocol)
            .and_then(|info| info.requirements.get(&func.name.name_str()))
            .map(|requirement| requirement.sig.clone());
        if let Some(expected) = expected {
            let mut effs = FxHashMap::default();
            effs.insert(
                requirement_symbol,
                EffTail::Var(self.store.fresh_eff(self.level, func.id)),
            );
            let expected = expected.substitute(&Default::default(), &effs, &Default::default());
            self.emit_eq(expected, inferred, func.id, CtReason::Annotation);
        }

        self.self_types.pop();

        let wanteds = std::mem::take(self.wanteds);
        let residuals = self.run_solver(wanteds);
        self.report_unresolved_residuals(residuals);
    }
}
