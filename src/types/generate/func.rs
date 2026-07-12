use super::*;

impl<'s, 'a> BodyChecker<'s, 'a> {
    // ----- Functions ------------------------------------------------------

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
    pub(super) fn infer_func(&mut self, func: &Func, ctx: &Ctx) -> Ty {
        self.register_func_bounds(func);
        self.with_declared_givens(&func.generics, func.where_clause.as_ref(), |this| {
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
                    Some(annotation) => {
                        let ty = self.lower_annotation(annotation);
                        elaborate::apply_param_mode(self.catalog, param.mode, ty)
                    }
                    None => Ty::Var(self.store.fresh_ty(self.level, param.id)),
                };
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
        ctx: &Ctx,
    ) -> Ty {
        self.register_func_bounds(func);
        self.with_declared_givens(&func.generics, func.where_clause.as_ref(), |this| {
            this.infer_func_against_inner(func, expected_params, expected_ret, expected_eff, ctx)
        })
    }

    pub(super) fn infer_func_against_inner(
        &mut self,
        func: &Func,
        expected_params: &[Ty],
        expected_ret: &Ty,
        expected_eff: &EffectRow,
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
                        let annotated =
                            elaborate::apply_param_mode(self.catalog, param.mode, annotated);
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

        // A nested function cannot resume an enclosing handler.
        let inner = ctx.enter_function(ret.clone(), expected_eff.clone());
        self.check_block_value(&func.body, &ret, &inner);

        Ty::Func(params, Box::new(ret), expected_eff.clone())
    }

    /// A trailing block treated as a closure: its labeled args are its
    /// parameters, its own return type and effect row.
    pub(super) fn infer_closure_block(&mut self, block: &Block, ctx: &Ctx) -> Ty {
        let params: Vec<Ty> = block
            .args
            .iter()
            .map(|param| {
                let ty = match &param.type_annotation {
                    Some(annotation) => {
                        let ty = self.lower_annotation(annotation);
                        elaborate::apply_param_mode(self.catalog, param.mode, ty)
                    }
                    None => Ty::Var(self.store.fresh_ty(self.level, param.id)),
                };
                self.bind_param(param, &ty);
                ty
            })
            .collect();

        let ret = Ty::Var(self.store.fresh_ty(self.level, block.id));
        let eff = EffectRow::open(self.store.fresh_eff(self.level, block.id));

        // A trailing block can resume an enclosing handler, so (unlike a
        // function literal) it keeps the handler context.
        let inner = ctx.with_ret_eff(ret.clone(), eff.clone());
        let body_ty = self.infer_block_value(block, &inner);

        if !body_ty.is_never() {
            self.emit_eq(ret.clone(), body_ty, block.id, CtReason::Body);
        }

        Ty::Func(params, Box::new(ret), eff)
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
        // `@handle 'e` delimits the rest of its block: statements after it
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
        // `@handle 'e` delimits the rest of its block: statements after it
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
    /// (`HandleEffect`) — the `@handle` discharges every occurrence of its
    /// effect, whatever the instantiation (label-scoped elimination —
    /// docs/generic-effects-plan.md).
    fn enter_handler_extent(&mut self, ctx: &Ctx, effect: Symbol, node: NodeID) -> Ctx {
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
