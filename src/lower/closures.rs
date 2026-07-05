use super::*;

impl<'a> Lowering<'a> {
    // ----- Function values (closures) ---------------------------------------

    /// A function literal: a λ_G function whose body sees the enclosing
    /// environment — free variables ARE the captures (paper §2.2's
    /// higher-order setting; the reference evaluator runs them by
    /// dependency-aware substitution, the scheduler closure-converts).
    /// The λ_G label for a function literal, from the checker's type at
    /// its node. A named local func's label is minted once per enclosing
    /// instantiation (`local_func_labels`), so block hoisting and the
    /// literal's own lowering agree on it.
    pub(super) fn func_literal_label(
        &mut self,
        func: &hir::Func,
        expr: &Expr,
        ctx: &Ctx,
    ) -> Option<Label> {
        let key = func
            .name
            .symbol()
            .ok()
            .filter(|s| matches!(s, Symbol::DeclaredLocal(..)))
            .map(|s| (s, theta_key(&ctx.theta)));
        if let Some(key) = &key
            && let Some(&label) = self.local_func_labels.get(key)
        {
            return Some(label);
        }
        let CheckTy::Func(param_check_tys, ret_check, _) = self.checker_ty(expr, ctx) else {
            self.diagnostics
                .push("lowering: function literal without a function type".into());
            return None;
        };
        let param_tys: Vec<TyId> = param_check_tys.iter().map(|t| self.map_ty(t)).collect();
        let ret_ty = self.map_ty(&ret_check);
        let bot = self.p.ty_bot();
        let ret_k_ty = self.p.ty_fn(ret_ty, bot);
        let mut dom_items = param_tys;
        dom_items.push(ret_k_ty);
        let dom = self.p.ty_tuple(&dom_items);
        let label = self.p.func("closure", dom, bot);
        self.escaping.insert(label);
        if let Some(key) = key {
            self.local_func_labels.insert(key, label);
        }
        Some(label)
    }

    pub(super) fn lower_func_value(
        &mut self,
        expr: &Expr,
        func: &hir::Func,
        ctx: &Ctx,
    ) -> Option<ExprId> {
        let label = self.func_literal_label(func, expr, ctx)?;

        let self_var = self.p.var(label);
        // The enclosing environment stays visible: references to it become
        // the closure's free variables.
        let mut inner = ctx.clone();
        inner.owner = None;
        inner.loops = vec![];
        inner.drop_stack = vec![];
        inner.initializing_self = None;
        let mut params = Vec::with_capacity(func.params.len());
        let mut prologue: Vec<(Symbol, ExprId)> = vec![];
        for (i, param) in func.params.iter().enumerate() {
            let extract = self.p.extract(self_var, i as u32);
            params.push(extract);
            if let Ok(symbol) = param.name.symbol() {
                if inner.cellable.contains(&symbol) {
                    prologue.push((symbol, extract));
                } else {
                    inner.env.insert(symbol, Binding::Value(extract));
                }
            }
        }
        inner.params = params;
        inner.ret_k = self.p.extract(self_var, func.params.len() as u32);
        inner.tail_k = inner.ret_k;
        inner.raw_ret_k = inner.ret_k;
        // A function value keeps the capabilities of its creation site —
        // its call sites are indirect and cannot thread them, so capture
        // is lexical (Effekt-style; ADR 0011 departure (d)). It cannot
        // resume an enclosing handler, though: the resumption does not
        // cross the closure boundary.
        inner.resume_k = None;
        inner.top_level = false;
        // The func sees itself: recursion through its own binder is a
        // value call to this same label (block hoisting covers the
        // mutual case; a celled binder keeps its late-bound cell).
        if let Ok(symbol) = func.name.symbol()
            && matches!(symbol, Symbol::DeclaredLocal(..))
            && !inner.cellable.contains(&symbol)
        {
            let self_ref = self.p.func_ref(label);
            inner.env.insert(symbol, Binding::Value(self_ref));
        }
        let body_block = &func.body;
        let body = self.with_cells(&prologue, &mut inner, |this, inner| {
            let ret_k = inner.ret_k;
            this.lower_block(body_block, &func.params, inner, ret_k)
        });
        self.p.set_body(label, body);
        Some(self.p.func_ref(label))
    }

    /// The callee's final declared parameter type (where a trailing block
    /// lands): for `Fn([params…, trailing, ret_k], ⊥)`, the
    /// second-to-last domain item.
    pub(super) fn final_param_ty(&self, callee_ty: TyId) -> Option<TyId> {
        let TyKind::Fn(dom, _) = *self.p.ty_kind(callee_ty) else {
            return None;
        };
        match self.p.ty_kind(dom) {
            TyKind::Tuple(items) if items.len() >= 2 => Some(items[items.len() - 2]),
            _ => None,
        }
    }

    /// A trailing block: a closure over the enclosing environment. Its
    /// shape comes from the callee's declared parameter type (`expected`,
    /// a λ_G Fn type) — the checker already typed the block's arguments
    /// against it; without one (no parameters), the block's value type
    /// suffices.
    pub(super) fn lower_block_closure(
        &mut self,
        block: &Block,
        expected: Option<TyId>,
        ctx: &Ctx,
    ) -> ExprId {
        let bot = self.p.ty_bot();
        let expected_dom = expected.and_then(|ty| match *self.p.ty_kind(ty) {
            TyKind::Fn(dom, _) => Some(dom),
            _ => None,
        });
        let dom = match expected_dom {
            Some(dom) => dom,
            _ => {
                if !block.args.is_empty() {
                    self.diagnostics.push(
                        "lowering: a parametered trailing block without a known callee parameter type"
                            .into(),
                    );
                }
                let ret_ty = block_value_ty(self, block, ctx);
                let ret_k_ty = self.p.ty_fn(ret_ty, bot);
                self.p.ty_tuple(&[ret_k_ty])
            }
        };
        let n_params = match self.p.ty_kind(dom) {
            TyKind::Tuple(items) => items.len().saturating_sub(1),
            _ => 0,
        };
        let label = self.p.func("trailing", dom, bot);
        self.escaping.insert(label);
        let self_var = self.p.var(label);
        let mut inner = ctx.clone();
        inner.owner = None;
        inner.loops = vec![];
        inner.drop_stack = vec![];
        inner.initializing_self = None;
        let mut params = Vec::with_capacity(n_params);
        let mut celled: Vec<(Symbol, ExprId)> = vec![];
        for (i, arg) in block.args.iter().enumerate().take(n_params) {
            let extract = self.p.extract(self_var, i as u32);
            params.push(extract);
            let Ok(symbol) = arg.name.symbol() else {
                continue;
            };
            if inner.cellable.contains(&symbol) {
                celled.push((symbol, extract));
            } else {
                inner.env.insert(symbol, Binding::Value(extract));
            }
        }
        inner.params = params;
        inner.ret_k = self.p.extract(self_var, n_params as u32);
        inner.tail_k = inner.ret_k;
        inner.raw_ret_k = inner.ret_k;
        inner.resume_k = None;
        inner.top_level = false;
        let block_id = block.id;
        let body = self.with_cells(&celled, &mut inner, |this, inner| {
            let ret_k = inner.ret_k;
            this.lower_sub_body_from_scaffold(block_id, inner, ret_k)
                .unwrap_or_else(|| this.lower_block(block, &[], inner, ret_k))
        });
        self.p.set_body(label, body);
        self.p.func_ref(label)
    }

    /// A call through a function VALUE (a local binding or a literal):
    /// apply the value's CPS function directly; the scheduler dispatches
    /// it indirectly.
    pub(super) fn lower_value_call(
        &mut self,
        callee: &Expr,
        args: &[hir::CallArg],
        trailing_block: Option<&Block>,
        ctx: &Ctx,
        k: ExprId,
    ) -> ExprId {
        let Some(callee_value) = self.try_pure(callee, ctx) else {
            self.diagnostics
                .push("lowering: computed callee expressions not yet supported".into());
            return self.dead_end("computed_callee");
        };
        let trailing_value = trailing_block.map(|b| {
            let expected = self.final_param_ty(self.p.expr_ty(callee_value));
            self.lower_block_closure(b, expected, ctx)
        });
        let arg_exprs: Vec<&Expr> = args.iter().map(|a| &a.value).collect();
        self.lower_args(&arg_exprs, ctx, vec![], &mut |this, mut values| {
            let k = this.release_temps_then(&arg_exprs, 0, &values, ctx, k);
            if let Some(trailing) = trailing_value {
                values.push(trailing);
            }
            values.push(k);
            let tuple = this.p.tuple(&values);
            this.p.app(callee_value, tuple)
        })
    }
}
