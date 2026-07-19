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
        // `Deinit` witnesses to row-check after solving: drop glue calls
        // deinit through a fixed signature with no capability parameters,
        // so a user effect in the hook's row could never be handled
        // (ADR 0027, open question 2).
        let mut deinit_rows: Vec<(NodeID, Ty)> = vec![];
        // Associated types without a declared binding are inferred from
        // the member bodies: remember the fresh variables so the solved
        // bindings can be written back into the conformance row (the
        // lowerer specializes default bodies from it).
        let mut inferred_assoc: Vec<((Symbol, ProtocolRef), Symbol, Ty)> = vec![];
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
                let Some((owner, requirement)) = self.catalog.requirement_in_ref(protocol, &label)
                else {
                    continue;
                };
                let requirement = requirement.clone();
                // The requirement's type is its scheme (the one signature
                // carrier); the witness unifies against it with Self,
                // assoc bindings, generics, and effect rows substituted.
                let Some(req_scheme) = self.schemes.get(&requirement.symbol).cloned() else {
                    continue;
                };
                let assoc_symbols: Vec<Symbol> = self
                    .catalog
                    .protocols
                    .get(&owner.protocol)
                    .map(|i| i.assoc.values().copied().collect())
                    .unwrap_or_default();
                let bindings = self
                    .catalog
                    .conformances
                    .get(&(head_symbol(&work.self_ty), owner.clone()))
                    .map(|c| c.assoc.clone())
                    .unwrap_or_default();

                let mut tys: FxHashMap<Symbol, Ty> = FxHashMap::default();
                tys.insert(owner.protocol, work.self_ty.clone());
                if let Some(info) = self.catalog.protocols.get(&owner.protocol) {
                    for (param, arg) in info.params.iter().copied().zip(owner.args.iter().cloned())
                    {
                        tys.insert(param, arg);
                    }
                }
                // Method-level generics unify against the witness's own
                // rigid generics through fresh variables.
                for param in &req_scheme.params {
                    tys.insert(
                        param.symbol,
                        Ty::Var(self.store.fresh_ty(self.level, member.id)),
                    );
                }
                for assoc in assoc_symbols {
                    let binding = match bindings.get(&assoc) {
                        Some(bound) => bound.clone(),
                        None => {
                            let var = Ty::Var(self.store.fresh_ty(self.level, member.id));
                            inferred_assoc.push((
                                (head_symbol(&work.self_ty), owner.clone()),
                                assoc,
                                var.clone(),
                            ));
                            var
                        }
                    };
                    tys.insert(assoc, binding);
                }
                let mut effs = FxHashMap::default();
                for param in &req_scheme.eff_params {
                    effs.insert(
                        *param,
                        EffTail::Var(self.store.fresh_eff(self.level, member.id)),
                    );
                }
                let expected = req_scheme.ty.substitute(&tys, &effs, &Default::default());
                let wanted = Constraint::Eq(
                    expected,
                    ty.clone(),
                    CtOrigin::new(member.id, CtReason::Annotation),
                );
                let givens: Vec<Predicate> = req_scheme
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
                if owner.protocol == Symbol::Deinit {
                    deinit_rows.push((member.id, ty.clone()));
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

        for (node, ty) in deinit_rows {
            let zonked = self.store.zonk_ty(&ty);
            let Ty::Func(_, _, eff) = &zonked else {
                continue;
            };
            for entry in &eff.effects {
                if entry.effect.external_module_id()
                    == Some(crate::compiling::module::ModuleId::Core)
                {
                    continue;
                }
                self.diagnostics.errors.push((
                    TypeError::DeinitEffectRow {
                        ty: work.self_ty.render_mono(),
                        effect: entry.effect.to_string(),
                    },
                    node,
                ));
            }
        }

        for (symbol, ty, declared) in outputs {
            let zonked = self.store.zonk_ty(&ty);
            // Leftover effect rows (closure-typed params, the outer tail)
            // quantify into eff_params so every use freshens them — the
            // same treatment the group Generalizer gives ordinary funcs.
            let (zonked, eff_params) = crate::types::solve::quantify_leftover_eff_vars(
                self.store,
                self.symbols,
                self.module_id,
                &zonked,
            );
            let mut scheme = Scheme::mono(zonked);
            // The witness's own generics quantify its scheme.
            scheme.params = declared.params.clone();
            scheme.eff_params = eff_params;
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
            .or_insert_with(|| {
                let args = self
                    .catalog
                    .protocols
                    .get(&protocol)
                    .map(|info| info.params.iter().copied().map(Ty::Param).collect())
                    .unwrap_or_default();
                vec![ProtocolRef { protocol, args }]
            });

        let group_eff = self.ambient_row();
        let group_ret = Ty::Var(self.store.fresh_ty(OUTER_LEVEL, NodeID::SYNTHESIZED));
        let group_ctx = Ctx::root().with_ret_eff(group_ret, group_eff);
        self.self_types.push(Ty::Param(protocol));
        let wanted_start = self.wanteds.len();

        let inferred = self
            .body()
            .infer_func(func, &group_ctx.with_binder(requirement_symbol));
        // The requirement's type is its scheme (the one signature carrier).
        let req_scheme = self.schemes.get(&requirement_symbol).cloned();
        if let Some(scheme) = &req_scheme {
            let mut tys: FxHashMap<Symbol, Ty> = FxHashMap::default();
            for param in &scheme.params {
                tys.insert(
                    param.symbol,
                    Ty::Var(self.store.fresh_ty(self.level, func.id)),
                );
            }
            let mut effs = FxHashMap::default();
            for param in &scheme.eff_params {
                effs.insert(
                    *param,
                    EffTail::Var(self.store.fresh_eff(self.level, func.id)),
                );
            }
            let expected = scheme.ty.substitute(&tys, &effs, &Default::default());
            self.emit_eq(expected, inferred, func.id, CtReason::Annotation);
        }

        // The requirement's declared predicates are givens for the body
        // (they are already over Self = the protocol's own param).
        let givens = req_scheme.map(|s| s.predicates).unwrap_or_default();
        if !givens.is_empty() {
            let wanteds = self.wanteds.split_off(wanted_start);
            if !wanteds.is_empty() {
                self.wanteds.push(Constraint::Implic(Box::new(Implication {
                    level: self.level,
                    givens,
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
    }
}
