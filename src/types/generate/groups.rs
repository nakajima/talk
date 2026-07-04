use super::*;

impl<'s, 'a> BindingGroupChecker<'s, 'a> {
    pub(super) fn check(&mut self, collected: Collected<'a>) {
        let Collected {
            decls,
            stmts,
            destructuring_lets,
            extends,
            protocol_defaults,
        } = collected;

        // The closed set every top-level ambient row carries: core effects
        // (the runtime's implicit handler) plus effects a top-level
        // `@handle` covers. Prescanned because top-level `let`s are
        // group-checked before the statement walk; the lowerer still
        // diagnoses a perform that beats its handler's install order.
        self.ambient_effects = self
            .catalog
            .effects
            .keys()
            .filter(|symbol| symbol.external_module_id() == Some(ModuleId::Core))
            .copied()
            .collect();
        for stmt in &stmts {
            if let StmtKind::Handling { effect_name, .. } = &stmt.kind
                && let Ok(effect) = effect_name.symbol()
            {
                self.ambient_effects.insert(effect);
            }
        }

        for binders in binding_groups(&decls) {
            self.check_group(&binders, &decls);
        }

        for work in extends {
            self.check_extend(work);
        }

        for (protocol, requirement_symbol, func) in protocol_defaults {
            self.check_protocol_default(protocol, requirement_symbol, func);
        }

        self.level = GROUP_LEVEL;
        let top_eff = self.ambient_row();
        let top_ret = Ty::Var(self.store.fresh_ty(OUTER_LEVEL, NodeID::SYNTHESIZED));
        let top_ctx = Ctx::root().with_ret_eff(top_ret.clone(), top_eff);
        for decl in destructuring_lets {
            self.body().check_local_decl(decl, &top_ctx);
        }
        let mut last = StmtValue::Unit;
        let mut top_level_handler: Option<NodeID> = None;
        for stmt in stmts {
            if matches!(stmt.kind, StmtKind::Handling { .. }) {
                top_level_handler = Some(stmt.id);
            }
            last = self.body().infer_stmt(stmt, &top_ctx);
        }
        // A top-level handler can abort the rest of the program, so the
        // top-level scope's result (`top_ret`, which the Handling arm
        // constrained the handler body against) is the program value —
        // the final statement's.
        if let Some(handler_id) = top_level_handler {
            let program_ty = match last {
                StmtValue::Value(ty) => ty,
                StmtValue::Divergent { .. } => Ty::Nominal(Symbol::Never, vec![]),
                StmtValue::Unit => Ty::unit(),
            };
            if !program_ty.is_never() {
                self.body()
                    .emit_eq(top_ret, program_ty, handler_id, CtReason::Body);
            }
        }
        let wanteds = std::mem::take(self.wanteds);
        let residuals = self.run_solver(wanteds);
        self.report_unresolved_residuals(residuals);
        self.solve_deferred();
    }

    /// The ambient row for computation at the top of the program: closed
    /// over the implicitly-handled and top-level-handled effects, so an
    /// effect with no handler errors at the node where it tries to flow in.
    pub(super) fn ambient_row(&self) -> EffectRow {
        EffectRow {
            effects: self.ambient_effects.clone(),
            tail: None,
        }
    }

    pub(super) fn run_solver(&mut self, wanteds: Vec<Constraint>) -> Vec<Constraint> {
        self.run_solver_with(wanteds, false)
    }

    pub(super) fn run_solver_with(
        &mut self,
        wanteds: Vec<Constraint>,
        defaulting: bool,
    ) -> Vec<Constraint> {
        let mut solver = Solver {
            store: &mut *self.store,
            errors: &mut self.diagnostics.errors,
            catalog: &*self.catalog,
            schemes: &*self.schemes,
            mono: &*self.mono,
            instantiations: &mut self.artifacts.instantiations,
            member_resolutions: &mut self.artifacts.member_resolutions,
            coerce_clones: &mut self.artifacts.coerce_clones,
            level: self.level,
            defaulting,
            givens: vec![],
            touchable_level: None,
            local_params: vec![],
            derived_seen: Default::default(),
        };
        solver.solve(wanteds)
    }

    /// Residuals in a context that cannot generalize float out to the final
    /// solve (their heads may be solved by a later group).
    pub(super) fn report_unresolved_residuals(&mut self, residuals: Vec<Constraint>) {
        self.deferred.extend(residuals);
    }

    /// The final solve over everything that floated out of its group. After
    /// this, a variable-headed predicate really is unsolvable: improvement
    /// applies one last time (the solver owns every level now), then errors.
    pub(super) fn solve_deferred(&mut self) {
        let deferred = std::mem::take(self.deferred);
        if deferred.is_empty() {
            return;
        }
        self.level = OUTER_LEVEL;
        let leftover = self.run_solver_with(deferred, true);
        self.level = GROUP_LEVEL;
        for constraint in leftover {
            match constraint {
                Constraint::Conforms {
                    ty,
                    protocol,
                    origin,
                } => {
                    let rendered = self.store.render(&ty);
                    self.diagnostics.errors.push((
                        TypeError::NotConforming {
                            ty: rendered,
                            protocol: protocol.to_string(),
                        },
                        origin.node,
                    ));
                }
                Constraint::HasMember {
                    receiver,
                    label,
                    origin,
                    ..
                } => {
                    let receiver = self.store.render(&receiver);
                    self.diagnostics.errors.push((
                        TypeError::UnknownMember {
                            receiver,
                            label: label.to_string(),
                        },
                        origin.node,
                    ));
                }
                Constraint::Eq(a, b, origin) => {
                    // A projection equality that never reduced: unprovable.
                    let expected = self.store.render(&a);
                    let found = self.store.render(&b);
                    self.diagnostics
                        .errors
                        .push((TypeError::Mismatch { expected, found }, origin.node));
                }
                Constraint::EffEq(a, b, origin) => {
                    let expected = self.store.render_eff(&a);
                    let found = self.store.render_eff(&b);
                    self.diagnostics
                        .errors
                        .push((TypeError::Mismatch { expected, found }, origin.node));
                }
                _ => {}
            }
        }
    }

    // ----- Binding groups -------------------------------------------------

    /// Check one binding group: skeletons at the group's level, generate
    /// every binder's constraints, solve once, then generalize (THIH-style
    /// per-group quantification, value-restricted).
    pub(super) fn check_group(
        &mut self,
        binders: &[Symbol],
        decls: &IndexMap<Symbol, TopEntry<'a>>,
    ) {
        self.level = GROUP_LEVEL;
        debug_assert!(self.wanteds.is_empty());

        // (symbol, type, passes value restriction, was annotated, declared generics/predicates)
        let mut outputs: Vec<(Symbol, Ty, bool, bool, DeclaredSchemeContext)> = vec![];
        // Binders with a closed effect annotation (`func f() 'a -> ()`),
        // checked as an exact upper bound after the solve.
        let mut closed_annotations: Vec<(Symbol, &'a Func)> = vec![];
        // Nominal member bodies queued behind skeleton creation so members
        // can reference each other (and Lets in the same group) freely.
        let mut member_queue: Vec<(Ty, Vec<(Symbol, MemberWork<'a>)>)> = vec![];

        // Skeletons first: annotated binders use their annotation; the rest
        // get fresh variables at the group level so they generalize. A
        // variable may already exist if an earlier group referenced this
        // binder out of dependency order — reuse it (it sits at the outer
        // level, so this group conservatively won't generalize what it
        // touches).
        for binder in binders {
            match &decls[binder] {
                TopEntry::Let {
                    decl, annotation, ..
                } => {
                    if !self.mono.contains_key(binder) {
                        let skeleton = match annotation {
                            Some(annotation) => self.lower_annotation(annotation),
                            None => Ty::Var(self.store.fresh_ty(self.level, decl.id)),
                        };
                        self.mono.insert(*binder, skeleton);
                    }
                }
                TopEntry::Struct { decl } | TopEntry::Enum { decl } => {
                    let work = self.prepare_nominal_members(*binder, decl);
                    member_queue.push(work);
                }
            }
        }

        // The ambient effect row for top-level right-hand-side computation
        // is not part of any binder's type: it is the closed top-level set,
        // so nothing about it can be quantified or grown.
        let group_eff = self.ambient_row();
        let group_ret = Ty::Var(self.store.fresh_ty(OUTER_LEVEL, NodeID::SYNTHESIZED));
        let group_ctx = Ctx::root().with_ret_eff(group_ret, group_eff);

        for binder in binders {
            if let TopEntry::Let {
                decl: _,
                annotation,
                rhs,
            } = &decls[binder]
            {
                if let Some(rhs) = rhs {
                    let expected = self.mono[binder].clone();
                    self.body().check_expr(
                        rhs,
                        &expected,
                        CtReason::Recursion,
                        &group_ctx.with_binder(*binder),
                    );
                }
                // Value restriction (Wright 1995): only syntactic values of
                // unmutated binders generalize.
                let is_value = rhs.map(|rhs| rhs.kind.is_syntactic_value()).unwrap_or(true);
                let passes = is_value && !self.resolved.mutated_symbols.contains(binder);
                let declared = match rhs {
                    Some(Expr {
                        kind: ExprKind::Func(func),
                        ..
                    }) => self.declared_scheme_context(&func.generics, func.where_clause.as_ref()),
                    _ => DeclaredSchemeContext::default(),
                };
                if let Some(Expr {
                    kind: ExprKind::Func(func),
                    ..
                }) = rhs
                    && !func.effects.is_open
                {
                    closed_annotations.push((*binder, func));
                }
                outputs.push((
                    *binder,
                    self.mono[binder].clone(),
                    passes,
                    annotation.is_some(),
                    declared,
                ));
            }
        }

        for (self_ty, members) in member_queue {
            let nominal_givens = nominal_predicates_for(self.catalog, &self_ty);
            let nominal_wanted_start = self.wanteds.len();
            self.self_types.push(self_ty);
            for (symbol, work) in members {
                // A method's own declared generics quantify its scheme
                // (instantiated fresh at each call site, like any other
                // polymorphic binder).
                let declared = match &work {
                    MemberWork::Method(func) => {
                        self.register_func_bounds(func);
                        self.declared_scheme_context(&func.generics, func.where_clause.as_ref())
                    }
                    MemberWork::Init { .. } => DeclaredSchemeContext::default(),
                };
                let member_ctx = group_ctx.with_binder(symbol);
                let ty = match work {
                    MemberWork::Method(func) => self.body().infer_func(func, &member_ctx),
                    MemberWork::Init { params, body, node } => {
                        self.body()
                            .infer_callable(params, None, body, node, &member_ctx)
                    }
                };
                let skeleton = self.mono[&symbol].clone();
                self.emit_eq(
                    skeleton.clone(),
                    ty,
                    NodeID::SYNTHESIZED,
                    CtReason::Recursion,
                );
                // Member bodies are function literals: always values.
                outputs.push((symbol, skeleton, true, false, declared));
            }
            if !nominal_givens.is_empty() {
                let wanteds = self.wanteds.split_off(nominal_wanted_start);
                if !wanteds.is_empty() {
                    self.wanteds.push(Constraint::Implic(Box::new(Implication {
                        level: self.level,
                        givens: nominal_givens,
                        wanteds,
                        local_params: vec![],
                        touchable_level: None,
                    })));
                }
            }
            self.self_types.pop();
        }

        let wanteds = std::mem::take(self.wanteds);
        let residuals = self.run_solver(wanteds);

        // Closed effect annotations are exact upper bounds on the inferred
        // row, checked at the declaration site so arrow rows stay open
        // (a deliberate deviation from Koka's row-typed effect system).
        for (binder, func) in closed_annotations {
            let declared: Vec<Symbol> = func
                .effects
                .names
                .iter()
                .filter_map(|n| n.symbol().ok())
                .collect();
            let ty = self.mono[&binder].clone();
            if let Ty::Func(_, _, eff) = self.store.zonk_ty(&ty) {
                for effect in &eff.effects {
                    if !declared.contains(effect) {
                        self.diagnostics.errors.push((
                            TypeError::UndeclaredEffect {
                                effect: effect.to_string(),
                            },
                            func.id,
                        ));
                    }
                }
            }
        }

        // THIH's restricted-group rule: one restricted binder makes the
        // whole group monomorphic.
        let generalizable = outputs.iter().all(|(_, _, passes, ..)| *passes);

        // Residual variable-headed predicates become the qualified context
        // on the parameters about to be quantified: THIH section 11.6's
        // retained predicates, generalized from class predicates to Talk's
        // unified predicate language.
        let mut var_predicates: FxHashMap<u32, Vec<Predicate>> = FxHashMap::default();
        let mut held_members: Vec<(Ty, crate::label::Label, Ty, CtOrigin)> = vec![];
        for residual in residuals {
            match &residual {
                Constraint::Conforms { ty, protocol, .. } => {
                    let Ty::Var(v) = self.store.shallow(ty) else {
                        continue;
                    };
                    let root = self.store.find(v.0);
                    if self.store.level(root) <= OUTER_LEVEL || !generalizable {
                        // A later group may still solve this variable:
                        // float the obligation out to the final solve.
                        self.deferred.push(residual);
                        continue;
                    }
                    let receiver = self.store.zonk_ty(ty);
                    let predicates = var_predicates.entry(root).or_default();
                    let conformance = Predicate::Conforms {
                        ty: receiver.clone(),
                        protocol: *protocol,
                    };
                    if !predicates.contains(&conformance) {
                        predicates.push(conformance);
                    }
                }
                Constraint::HasMember {
                    receiver,
                    label,
                    member,
                    origin,
                } => {
                    // A member use stuck on a variable this group owns
                    // qualifies the binder's scheme (held here, attached
                    // after generalization — Jones, *Qualified Types*,
                    // 1994); anything else may be solved later and floats.
                    let group_owned = match self.store.shallow(receiver) {
                        Ty::Var(v) => {
                            let root = self.store.find(v.0);
                            self.store.level(root) > OUTER_LEVEL
                        }
                        _ => false,
                    };
                    if generalizable && group_owned {
                        held_members.push((
                            receiver.clone(),
                            label.clone(),
                            member.clone(),
                            *origin,
                        ));
                    } else {
                        self.deferred.push(residual)
                    }
                }
                Constraint::Eq(a, b, _) => {
                    let mut roots = vec![];
                    self.group_owned_roots(a, &mut roots);
                    self.group_owned_roots(b, &mut roots);
                    roots.sort_unstable();
                    roots.dedup();
                    if generalizable && let Some(root) = roots.first().copied() {
                        let predicate =
                            Predicate::TypeEq(self.store.zonk_ty(a), self.store.zonk_ty(b));
                        let predicates = var_predicates.entry(root).or_default();
                        if !predicates.contains(&predicate) {
                            predicates.push(predicate);
                        }
                    } else {
                        self.deferred.push(residual)
                    }
                }
                _ => {}
            }
        }

        if generalizable {
            let mut generalizer = Generalizer::new(
                self.store,
                self.symbols,
                self.module_id,
                OUTER_LEVEL,
                var_predicates,
            );
            for (symbol, ty, _, annotated, declared) in &outputs {
                let mut scheme = if *annotated {
                    Scheme::mono(generalizer.store.zonk_ty(ty))
                } else {
                    generalizer.generalize(ty, &declared.params)
                };
                let mut predicates = declared.predicates.clone();
                predicates.extend(scheme.predicates);
                scheme.predicates = predicates;
                self.diagnostics
                    .errors
                    .extend(Self::ambiguous_declared_predicate_errors(&scheme, declared));
                self.schemes.insert(*symbol, scheme);
            }
            // Held member uses: quantification turned their receivers'
            // variables into scheme parameters — attach each constraint
            // to every scheme of this group that mentions one of them;
            // constraints over nothing quantified float instead.
            for (receiver, label, member, origin) in held_members {
                let receiver = self.store.zonk_ty(&receiver);
                let member = self.store.zonk_ty(&member);
                let mut attached = false;
                for (symbol, ..) in &outputs {
                    let Some(scheme) = self.schemes.get(symbol) else {
                        continue;
                    };
                    let mentions = scheme.params.iter().any(|p| {
                        ty_mentions_param(&receiver, p.symbol)
                            || ty_mentions_param(&member, p.symbol)
                    });
                    if mentions {
                        let predicate = Predicate::HasMember {
                            receiver: receiver.clone(),
                            label: label.clone(),
                            member: member.clone(),
                        };
                        if let Some(scheme) = self.schemes.get_mut(symbol)
                            && !scheme.predicates.contains(&predicate)
                        {
                            scheme.predicates.push(predicate);
                            attached = true;
                        }
                    }
                }
                if !attached {
                    self.deferred.push(Constraint::HasMember {
                        receiver,
                        label,
                        member,
                        origin,
                    });
                }
            }
        } else {
            for (symbol, ty, ..) in &outputs {
                let zonked = self.store.zonk_ty(ty);
                self.schemes.insert(*symbol, Scheme::mono(zonked));
            }
        }

        for (symbol, ..) in &outputs {
            self.mono.remove(symbol);
        }
    }

    pub(super) fn declared_scheme_context(
        &mut self,
        generics: &[GenericDecl],
        where_clause: Option<&WhereClause>,
    ) -> DeclaredSchemeContext {
        let mut context = DeclaredSchemeContext::default();
        for generic in generics {
            let Ok(symbol) = generic.name.symbol() else {
                continue;
            };
            context.params.push(SchemeParam { symbol });
            context.param_nodes.push((symbol, generic.id));
        }
        context.predicates = self.declared_predicates(generics, where_clause);
        context
    }

    pub(super) fn ambiguous_declared_predicate_errors(
        scheme: &Scheme,
        declared: &DeclaredSchemeContext,
    ) -> Vec<(TypeError, NodeID)> {
        if declared.predicates.is_empty() || declared.params.is_empty() {
            return vec![];
        }

        let declared_symbols: FxHashSet<Symbol> =
            declared.params.iter().map(|param| param.symbol).collect();
        let mut constrained = FxHashSet::default();
        for predicate in &declared.predicates {
            collect_predicate_params(predicate, Some(&declared_symbols), &mut constrained);
        }

        let mut determined = FxHashSet::default();
        collect_ty_params(&scheme.ty, Some(&declared_symbols), &mut determined);

        let mut changed = true;
        while changed {
            changed = false;
            for predicate in &declared.predicates {
                let Predicate::TypeEq(lhs, rhs) = predicate else {
                    continue;
                };
                let mut lhs_params = FxHashSet::default();
                let mut rhs_params = FxHashSet::default();
                collect_ty_params(lhs, Some(&declared_symbols), &mut lhs_params);
                collect_ty_params(rhs, Some(&declared_symbols), &mut rhs_params);
                let lhs_known = lhs_params.iter().any(|param| determined.contains(param));
                let rhs_known = rhs_params.iter().any(|param| determined.contains(param));
                if lhs_known {
                    for param in rhs_params {
                        changed |= determined.insert(param);
                    }
                }
                if rhs_known {
                    for param in lhs_params {
                        changed |= determined.insert(param);
                    }
                }
            }
        }

        let mut errors = vec![];
        for (symbol, node) in &declared.param_nodes {
            if constrained.contains(symbol) && !determined.contains(symbol) {
                errors.push((
                    TypeError::AmbiguousTypeParameter {
                        param: symbol.to_string(),
                    },
                    *node,
                ));
            }
        }
        errors
    }

    /// Create member skeletons for a struct's methods and initializers and
    /// queue their bodies. Returns (Self type, member work list).
    pub(super) fn prepare_nominal_members(
        &mut self,
        symbol: Symbol,
        decl: &'a Decl,
    ) -> (Ty, Vec<(Symbol, MemberWork<'a>)>) {
        let params = self
            .catalog
            .structs
            .get(&symbol)
            .map(|info| info.params.clone())
            .or_else(|| {
                self.catalog
                    .enums
                    .get(&symbol)
                    .map(|info| info.params.clone())
            })
            .unwrap_or_default();
        let self_ty = Ty::Nominal(symbol, params.iter().map(|p| Ty::Param(*p)).collect());

        let mut work = vec![];
        let (DeclKind::Struct { body, .. } | DeclKind::Enum { body, .. }) = &decl.kind else {
            return (self_ty, work);
        };
        for member in &body.decls {
            match &member.kind {
                DeclKind::Method { func, .. } => {
                    if let Ok(method) = func.name.symbol() {
                        work.push((method, MemberWork::Method(func)));
                    }
                }
                DeclKind::Init { name, params, body } => {
                    if let Ok(init) = name.symbol() {
                        work.push((
                            init,
                            MemberWork::Init {
                                params,
                                body,
                                node: member.id,
                            },
                        ));
                    }
                }
                _ => {}
            }
        }
        for (member_symbol, _) in &work {
            if !self.mono.contains_key(member_symbol) {
                let var = Ty::Var(self.store.fresh_ty(self.level, decl.id));
                self.mono.insert(*member_symbol, var);
            }
        }
        (self_ty, work)
    }
}
