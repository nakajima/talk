use super::*;

impl<'s, 'a> BodyChecker<'s, 'a> {
    // ----- Functions ------------------------------------------------------

    /// Per-field generalization (rank-N field types): a func literal in a
    /// record field is solved and generalized as its own little binding
    /// group, so its quantified variables and predicates live on the
    /// field's own scheme — sibling fields' predicates never fuse into
    /// the enclosing record's type, and each projection of the field
    /// instantiates only this scheme (see `eliminate_forall`). The
    /// enclosing group treats the resulting `Forall` opaquely.
    pub(super) fn generalize_field_func(&mut self, func: &Func, expr: &Expr, ctx: &Ctx) -> Ty {
        // The closure's own variables live one level deeper than the
        // enclosing group, so local generalization quantifies exactly
        // them; captures' and siblings' variables (group level) stay
        // free, mirroring `check_group`'s discipline for one binder.
        let outer_level = self.level;
        self.level = outer_level.next();
        let wanted_start = self.wanteds.len();
        let ty = self.infer_func(func, ctx);
        let wanteds = self.wanteds.split_off(wanted_start);

        // Solve locally with the group's variables untouchable.
        let residuals = {
            let mut solver = Solver {
                store: &mut *self.store,
                errors: &mut self.diagnostics.errors,
                catalog: &*self.catalog,
                module_id: self.module_id,
                schemes: &*self.schemes,
                mono: &*self.mono,
                instantiations: &mut self.artifacts.instantiations,
                projection_instantiations: &mut self.artifacts.projection_instantiations,
                member_resolutions: &mut self.artifacts.member_resolutions,
                resolved_member_types: &mut self.artifacts.resolved_member_types,
                member_call_slots: &self.artifacts.member_call_slots,
                coerce_clones: &mut self.artifacts.coerce_clones,
                level: self.level,
                defaulting: false,
                givens: vec![],
                touchable_level: Some(self.level),
                local_params: vec![],
                conformance_edges: Default::default(),
            };
            solver.solve(wanteds)
        };
        self.level = outer_level;

        // Triage residuals like `check_group`: variable-headed
        // obligations on closure-owned variables qualify the field's
        // scheme; anything touching an outer variable floats back to
        // the enclosing group's wanteds.
        let mut var_predicates: FxHashMap<u32, Vec<Predicate>> = FxHashMap::default();
        let mut residual_roots: Vec<(u32, Constraint)> = vec![];
        for residual in residuals {
            let held = match &residual {
                // A conformance holds only when its receiver's head IS a
                // closure-owned variable; one stuck on a nested deeper
                // var floats like any outer-touching residual.
                Constraint::Conforms { ty, protocol, .. } => match self.store.shallow(ty) {
                    Ty::Var(v) => {
                        let root = self.store.find(v.0);
                        (self.store.level(root) > outer_level).then(|| {
                            (root, Predicate::Conforms {
                                ty: self.store.zonk_ty(ty),
                                protocol: protocol.clone(),
                            })
                        })
                    }
                    _ => None,
                },
                Constraint::Eq(a, b, ..) => self.min_deeper_root(&[a, b], outer_level).map(|root| {
                    (
                        root,
                        Predicate::TypeEq(self.store.zonk_ty(a), self.store.zonk_ty(b)),
                    )
                }),
                Constraint::HasMember {
                    receiver,
                    label,
                    member,
                    ..
                } => self
                    .min_deeper_root(&[receiver, member], outer_level)
                    .map(|root| {
                        (root, Predicate::HasMember {
                            receiver: self.store.zonk_ty(receiver),
                            label: label.clone(),
                            member: self.store.zonk_ty(member),
                        })
                    }),
                _ => None,
            };
            match held {
                Some((root, predicate)) => {
                    let predicates = var_predicates.entry(root).or_default();
                    if !predicates.contains(&predicate) {
                        predicates.push(predicate);
                    }
                    residual_roots.push((root, residual));
                }
                None => self.wanteds.push(residual),
            }
        }

        // Declared generics and where-clause bounds seed the scheme
        // exactly as they would for a let-bound function: the declared
        // rigid parameters are this group's own mints, and the declared
        // predicates lead the qualified context.
        let declared = {
            let mut context = DeclaredSchemeContext::default();
            context.params = self.declared_params(&func.generics);
            for generic in &func.generics {
                if let Ok(symbol) = generic.name.symbol() {
                    context.param_nodes.push((symbol, generic.id));
                }
            }
            context.predicates =
                self.declared_predicates(&func.generics, func.where_clause.as_ref());
            context
        };
        let mut generalizer = Generalizer::new(
            &mut *self.store,
            &mut *self.symbols,
            self.module_id,
            outer_level,
            var_predicates,
        );
        let mut scheme = generalizer.generalize(&ty, &declared.params);
        publish_inferred_param_names(&generalizer, self.resolved, self.artifacts);
        finish_scheme(&mut scheme, &declared, self.catalog, self.diagnostics);
        // Obligations whose root never quantified ride no scheme — they
        // mention something the field shares with the group, so they
        // float back to the enclosing wanteds.
        let leftover = generalizer.into_leftover_predicates();
        for (root, residual) in residual_roots {
            if leftover.contains(&root) {
                self.wanteds.push(residual);
            }
        }
        let ty = Ty::Forall(Box::new(scheme));
        self.artifacts.node_types.insert(expr.id, ty.clone());
        if func.id != expr.id {
            self.artifacts.node_types.insert(func.id, ty.clone());
        }
        ty
    }

    /// The smallest variable root in `tys` owned strictly below `level`
    /// (the local analogue of `group_owned_roots`, which is keyed to
    /// OUTER_LEVEL).
    fn min_deeper_root(&mut self, tys: &[&Ty], level: Level) -> Option<u32> {
        let mut roots = vec![];
        for ty in tys {
            let _ = self.store.query_resolved(ty, &mut |store, node| {
                if let TyNode::Ty(Ty::Var(v)) = node {
                    let root = store.find(v.0);
                    if store.level(root) > level {
                        roots.push(root);
                    }
                }
                std::ops::ControlFlow::<()>::Continue(())
            });
        }
        roots.into_iter().min()
    }

    /// Bind a parameter's type: into the mono environment for the body, and
    /// onto the parameter's node so downstream stages (typed-tree baking, the flow
    /// checker) see it without consulting the function's scheme.
    fn bind_param(&mut self, param: &Parameter, ty: &Ty) {
        self.artifacts.node_types.insert(param.id, ty.clone());
        if let Ok(symbol) = param.name.symbol() {
            self.mono.insert(symbol, ty.clone());
        }
    }

    /// Infer a function literal: parameters from annotations or fresh vars,
    /// a fresh open ambient effect row (Koka-style), body joined into the
    /// return type.
    /// The declared shape of a `func` for recursive-group skeletons:
    /// annotated parameters (modes applied) and return, fresh variables
    /// elsewhere. No binding and no body — the definition pass still
    /// checks the whole function against this skeleton. A bare-variable
    /// skeleton would let an in-group call bind a parameter to its
    /// argument's unborrowed type and then clash with the annotated
    /// definition (found porting the frontend, ADR 0043).
    pub(super) fn func_signature_skeleton(&mut self, func: &Func, node: NodeID) -> Ty {
        // A concrete skeleton makes in-group call sites check argument
        // labels immediately, so the label contract (ADR 0041) must be
        // registered with it — the same idempotent entry `infer_func`
        // makes later.
        if func.origin == crate::node_kinds::func::FuncOrigin::Decl
            && let Ok(symbol) = func.name.symbol()
        {
            self.catalog
                .callable_contracts
                .entry(symbol)
                .or_insert_with(|| crate::types::callables::CallableContract {
                    name: crate::types::callables::CallableName::from_params(
                        func.name.name_str(),
                        &func.params,
                        false,
                    ),
                    role: crate::types::callables::CallableRole::Function,
                });
        }
        let params: Vec<Ty> = func
            .params
            .iter()
            .map(|param| {
                let ty = match &param.type_annotation {
                    Some(annotation) => self.lower_annotation(annotation),
                    None => Ty::Var(self.store.fresh_ty(self.level, param.id)),
                };
                elaborate::apply_param_mode(self.catalog, param, ty, self.diagnostics)
            })
            .collect();
        let ret = match func.ret.as_ref() {
            Some(annotation) => self.lower_annotation(annotation),
            None => Ty::Var(self.store.fresh_ty(self.level, node)),
        };
        Ty::Func(
            params,
            Box::new(ret),
            EffectRow::open(self.store.fresh_eff(self.level, node)),
        )
    }

    pub(super) fn infer_func(&mut self, func: &Func, ctx: &Ctx) -> Ty {
        // A named `func` declaration publishes its argument-label contract
        // (ADR 0041). Closures never do, and collection-registered roles
        // (methods, requirements) already claimed their symbols.
        if func.origin == crate::node_kinds::func::FuncOrigin::Decl
            && let Ok(symbol) = func.name.symbol()
        {
            self.catalog
                .callable_contracts
                .entry(symbol)
                .or_insert_with(|| crate::types::callables::CallableContract {
                    name: crate::types::callables::CallableName::from_params(
                        func.name.name_str(),
                        &func.params,
                        false,
                    ),
                    role: crate::types::callables::CallableRole::Function,
                });
        }
        self.register_func_bounds(func);
        self.with_declared_givens(func.id, &func.generics, func.where_clause.as_ref(), |this| {
            let inferred =
                this.infer_callable(&func.params, func.ret.as_ref(), &func.body, func.id, ctx);
            if func.effects.is_open {
                return inferred;
            }

            let Ty::Func(params, ret, inferred_effects) = inferred else {
                return inferred;
            };
            let allowed = EffectRow::new(
                func.effects
                    .names
                    .iter()
                    .filter_map(|name| name.symbol().ok())
                    .map(EffectEntry::label)
                    .collect(),
                None,
            );
            this.wanteds.push(Constraint::EffectSubset {
                inferred: inferred_effects,
                allowed: allowed.clone(),
                origin: CtOrigin::new(func.id, CtReason::Effect),
            });
            Ty::Func(params, ret, allowed)
        })
    }

    pub(super) fn with_declared_givens<T>(
        &mut self,
        node: NodeID,
        generics: &[GenericDecl],
        where_clause: Option<&WhereClause>,
        f: impl FnOnce(&mut Self) -> T,
    ) -> T {
        let givens = self.declared_predicates(generics, where_clause);
        let start = self.wanteds.len();
        let result = f(self);
        if !givens.is_empty() {
            let wanteds = self.wanteds.split_off(start);
            if !wanteds.is_empty() {
                self.wanteds.push(Constraint::Implic(Box::new(Implication {
                    node,
                    level: self.level,
                    givens,
                    wanteds,
                    local_params: vec![],
                    touchable_level: None,
                })));
            }
        }
        result
    }

    pub(super) fn infer_callable(
        &mut self,
        params: &[Parameter],
        ret_annotation: Option<&TypeAnnotation>,
        body: &Block,
        node: NodeID,
        ctx: &Ctx,
    ) -> Ty {
        let params: Vec<Ty> = params
            .iter()
            .map(|param| {
                let ty = match &param.type_annotation {
                    Some(annotation) => self.lower_annotation(annotation),
                    // An inferred param's fresh var wraps per the stamped
                    // mode too (plan 3.3(b)): `func f(x)` and
                    // `func f<T>(x: T)` route through the same machinery,
                    // so the stored `ParamMode` and the solved type agree.
                    // Copy erasure (a payload that solves to Int) is the
                    // solver's deferred half of `copy_grade_head`.
                    None => Ty::Var(self.store.fresh_ty(self.level, param.id)),
                };
                let ty = elaborate::apply_param_mode(self.catalog, param, ty, self.diagnostics);
                self.bind_param(param, &ty);
                ty
            })
            .collect();

        let ret = match ret_annotation {
            Some(annotation) => self.lower_annotation(annotation),
            None => Ty::Var(self.store.fresh_ty(self.level, node)),
        };
        let eff = EffectRow::open(self.store.fresh_eff(self.level, node));

        // A nested function cannot resume an enclosing handler.
        let inner = ctx.enter_function(ret.clone(), eff.clone());
        let body_ty = if ret_annotation.is_some() {
            self.check_block_value(body, &ret, &inner);
            ret.clone()
        } else {
            self.infer_block_value(body, &inner)
        };

        if ret_annotation.is_none() && !body_ty.is_never() {
            self.emit_eq(ret.clone(), body_ty, body.id, CtReason::Body);
        }

        Ty::Func(params, Box::new(ret), eff)
    }

    /// Checking-mode function literal: expected parameter and return types
    /// are pushed into the body (the bidirectional payoff: unannotated
    /// closure params get their types from context).
    pub(super) fn infer_func_against(
        &mut self,
        func: &Func,
        expected_params: &[Ty],
        expected_ret: &Ty,
        expected_eff: &EffectRow,
        result_reason: CtReason,
        ctx: &Ctx,
    ) -> Ty {
        self.register_func_bounds(func);
        self.with_declared_givens(func.id, &func.generics, func.where_clause.as_ref(), |this| {
            this.infer_func_against_inner(
                func,
                expected_params,
                expected_ret,
                expected_eff,
                result_reason,
                ctx,
            )
        })
    }

    pub(super) fn infer_func_against_inner(
        &mut self,
        func: &Func,
        expected_params: &[Ty],
        expected_ret: &Ty,
        expected_eff: &EffectRow,
        result_reason: CtReason,
        ctx: &Ctx,
    ) -> Ty {
        let params: Vec<Ty> = func
            .params
            .iter()
            .zip(expected_params)
            .map(|(param, expected)| {
                let ty = match &param.type_annotation {
                    Some(annotation) => {
                        let annotated = self.lower_annotation(annotation);
                        let annotated = elaborate::apply_param_mode(
                            self.catalog,
                            param,
                            annotated,
                            self.diagnostics,
                        );
                        self.emit_eq(
                            expected.clone(),
                            annotated.clone(),
                            param.id,
                            CtReason::Annotation,
                        );
                        annotated
                    }
                    None => expected.clone(),
                };
                self.bind_param(param, &ty);
                ty
            })
            .collect();

        let ret = match &func.ret {
            Some(annotation) => {
                let annotated = self.lower_annotation(annotation);
                self.emit_borrow_downgrade_or_eq(
                    expected_ret.clone(),
                    annotated.clone(),
                    func.id,
                    CtReason::Annotation,
                );
                annotated
            }
            None => expected_ret.clone(),
        };

        // Check the body under its own latent row. Contextual effect
        // widening must not make closure creation require those effects;
        // the expected row is only an upper bound supplied to callers.
        let inferred_eff = EffectRow::open(self.store.fresh_eff(self.level, func.id));
        let inner = ctx.enter_function(ret.clone(), inferred_eff.clone());
        self.check_block_value_with_reason(&func.body, &ret, result_reason, &inner);
        self.wanteds.push(Constraint::EffectSubset {
            inferred: inferred_eff,
            allowed: expected_eff.clone(),
            origin: CtOrigin::new(
                func.id,
                if expected_eff.tail.is_none() {
                    CtReason::Effect
                } else {
                    CtReason::Apply
                },
            ),
        });

        Ty::Func(params, Box::new(ret), expected_eff.clone())
    }

    // ----- Blocks, statements, declarations -----------------------------

    /// A block's value is its final expression statement; a block ending in
    /// a divergent statement is `Never`; anything else is unit.
    /// Pre-bind every func-valued `let` binder in this block to a fresh
    /// monomorphic type variable (the checker's mirror of the resolver's
    /// fn-in-block hoisting): a local func's own body — and earlier
    /// funcs' bodies, for mutual recursion — unify their uses against
    /// the same variable that `check_local_decl` later ties to the
    /// definition's type.
    fn hoist_local_func_signatures(&mut self, block: &Block) {
        for node in &block.body {
            if let Node::Decl(Decl {
                id,
                kind:
                    DeclKind::Let {
                        lhs:
                            Pattern {
                                kind: PatternKind::Bind(name),
                                ..
                            },
                        rhs:
                            Some(Expr {
                                kind: ExprKind::Func(_),
                                ..
                            }),
                        ..
                    },
                ..
            }) = node
                && let Ok(symbol) = name.symbol()
                && !self.mono.contains_key(&symbol)
            {
                let ty = Ty::Var(self.store.fresh_ty(self.level, *id));
                self.mono.insert(symbol, ty);
            }
        }
    }

    pub(super) fn infer_block_value(&mut self, block: &Block, ctx: &Ctx) -> Ty {
        self.hoist_local_func_signatures(block);
        let mut last = StmtValue::Unit;
        let mut is_empty = true;
        let final_index = block.body.len().saturating_sub(1);
        // `#handle 'e` delimits the rest of its block: statements after it
        // check under an ambient row extended with `e`.
        let mut scoped: Option<Ctx> = None;
        for (index, node) in block.body.iter().enumerate() {
            let ctx = scoped.as_ref().unwrap_or(ctx);
            is_empty = false;
            last = match node {
                Node::Decl(decl) => {
                    self.check_local_decl(decl, ctx);
                    StmtValue::Unit
                }
                // A block-final `if/else` statement is the block's value
                // (joined like the expression form).
                Node::Stmt(Stmt {
                    kind: StmtKind::If(condition, then_block, Some(else_block)),
                    ..
                }) if index == final_index => {
                    let cond_ty = self.infer_expr(condition, ctx);
                    self.emit_eq(
                        Ty::Nominal(Symbol::Bool, vec![]),
                        cond_ty,
                        condition.id,
                        CtReason::Condition,
                    );
                    let then_ty = self.infer_block_value(then_block, ctx);
                    let else_ty = self.infer_block_value(else_block, ctx);
                    StmtValue::Value(self.join(then_ty, else_ty, node.node_id()))
                }
                Node::Stmt(stmt) => self.infer_stmt(stmt, ctx),
                // Desugared `||`/`&&` blocks hold bare expressions.
                Node::Expr(expr) => StmtValue::Value(self.infer_expr(expr, ctx)),
                _ => StmtValue::Unit,
            };
            if let Node::Stmt(Stmt {
                kind: StmtKind::Handling { effect_name, .. },
                ..
            }) = node
                && let Ok(effect) = effect_name.symbol()
            {
                scoped = Some(self.enter_handler_extent(ctx, effect, node.node_id()));
            }
            if last.reports_unreachable() {
                if let Some(next) = block.body.get(index + 1) {
                    self.unreachable_code(next.node_id());
                }
                break;
            }
        }
        if is_empty {
            return Ty::unit();
        }
        match last {
            StmtValue::Value(ty) => ty,
            StmtValue::Divergent { .. } => Ty::Nominal(Symbol::Never, vec![]),
            StmtValue::Unit => Ty::unit(),
        }
    }

    pub(super) fn check_block_value(&mut self, block: &Block, expected: &Ty, ctx: &Ctx) {
        self.check_block_value_with_reason(block, expected, CtReason::Body, ctx);
    }

    pub(super) fn check_block_value_with_reason(
        &mut self,
        block: &Block,
        expected: &Ty,
        reason: CtReason,
        ctx: &Ctx,
    ) {
        self.hoist_local_func_signatures(block);
        let final_index = block.body.len().saturating_sub(1);
        if block.body.is_empty() {
            self.emit_eq(expected.clone(), Ty::unit(), block.id, reason);
            return;
        }
        // `#handle 'e` delimits the rest of its block: statements after it
        // check under an ambient row extended with `e`.
        let mut scoped: Option<Ctx> = None;
        for (index, node) in block.body.iter().enumerate() {
            let ctx = scoped.as_ref().unwrap_or(ctx);
            if index != final_index {
                match node {
                    Node::Decl(decl) => self.check_local_decl(decl, ctx),
                    Node::Stmt(stmt) => {
                        let value = self.infer_stmt(stmt, ctx);
                        if value.reports_unreachable() {
                            if let Some(next) = block.body.get(index + 1) {
                                self.unreachable_code(next.node_id());
                            }
                            return;
                        }
                    }
                    Node::Expr(expr) => {
                        self.infer_expr(expr, ctx);
                    }
                    _ => {}
                }
                if let Node::Stmt(Stmt {
                    kind: StmtKind::Handling { effect_name, .. },
                    ..
                }) = node
                    && let Ok(effect) = effect_name.symbol()
                {
                    scoped = Some(self.enter_handler_extent(ctx, effect, node.node_id()));
                }
                continue;
            }

            match node {
                Node::Decl(decl) => {
                    self.check_local_decl(decl, ctx);
                    self.emit_eq(expected.clone(), Ty::unit(), node.node_id(), reason);
                }
                Node::Stmt(Stmt {
                    kind: StmtKind::Expr(expr),
                    ..
                }) => self.check_expr(expr, expected, reason, ctx),
                Node::Stmt(Stmt {
                    kind: StmtKind::If(condition, then_block, Some(else_block)),
                    ..
                }) => {
                    let cond_ty = self.infer_expr(condition, ctx);
                    self.emit_eq(
                        Ty::Nominal(Symbol::Bool, vec![]),
                        cond_ty,
                        condition.id,
                        CtReason::Condition,
                    );
                    self.check_block_value_with_reason(then_block, expected, reason, ctx);
                    self.check_block_value_with_reason(else_block, expected, reason, ctx);
                }
                Node::Stmt(stmt) => {
                    if !self.infer_stmt(stmt, ctx).is_divergent() {
                        self.emit_eq(expected.clone(), Ty::unit(), stmt.id, reason);
                    }
                }
                Node::Expr(expr) => self.check_expr(expr, expected, reason, ctx),
                _ => self.emit_eq(expected.clone(), Ty::unit(), node.node_id(), reason),
            }
        }
    }

    /// Enter a handler's extent: the rest of the scope checks under a
    /// fresh ambient row, connected to the current one by a label filter
    /// (`HandleEffect`) — the `#handle` discharges every occurrence of its
    /// effect, whatever the instantiation (label-scoped elimination —
    /// docs/effects.md).
    fn enter_handler_extent(&mut self, ctx: &Ctx, effect: Symbol, node: NodeID) -> Ctx {
        self.enter_effect_mask(ctx, effect, node)
    }

    /// Check a lexical body under an effect that is discharged at the
    /// boundary. Runtime handlers and compile-time `#unsafe` blocks share
    /// this row operation, but only handlers lower to runtime machinery.
    pub(super) fn enter_effect_mask(&mut self, ctx: &Ctx, effect: Symbol, node: NodeID) -> Ctx {
        let inner = EffectRow::open(self.store.fresh_eff(self.level, node));
        self.wanteds.push(Constraint::HandleEffect {
            inner: inner.clone(),
            effects: vec![effect],
            outer: ctx.eff.clone(),
            origin: CtOrigin::new(node, CtReason::Effect),
        });
        ctx.with_ret_eff(ctx.ret.clone(), inner)
    }

    fn unreachable_code(&mut self, node: NodeID) {
        self.diagnostics
            .errors
            .push((TypeError::UnreachableCode, node));
    }
}
