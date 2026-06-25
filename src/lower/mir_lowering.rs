use super::*;
use crate::mir;

#[derive(Clone, Copy)]
enum MirRestBinding {
    Bind(Symbol, bool),
    Discard,
    Deliver,
}

impl<'a> Lowering<'a> {
    pub(super) fn lower_mir_body(&mut self, body: &mir::Body<'_>, ctx: &Ctx, k: ExprId) -> ExprId {
        self.lower_mir_block(body, body.entry, ctx, k, &[])
    }

    fn lower_mir_block(
        &mut self,
        body: &mir::Body<'_>,
        block: mir::BlockId,
        ctx: &Ctx,
        k: ExprId,
        loops: &[(mir::BlockId, ExprId, mir::BlockId, ExprId)],
    ) -> ExprId {
        let basic_block = &body.blocks[block.0];
        self.lower_mir_statements(body, block, 0, &basic_block.statements, ctx, k, loops)
    }

    fn lower_mir_statements(
        &mut self,
        body: &mir::Body<'_>,
        block: mir::BlockId,
        index: usize,
        statements: &[mir::LocatedStatement<'_>],
        ctx: &Ctx,
        k: ExprId,
        loops: &[(mir::BlockId, ExprId, mir::BlockId, ExprId)],
    ) -> ExprId {
        let Some(statement) = statements.get(index) else {
            return self.lower_mir_terminator(body, block, ctx, k, loops);
        };
        let rest = |this: &mut Self, ctx: &Ctx, k: ExprId| {
            this.lower_mir_statements(body, block, index + 1, statements, ctx, k, loops)
        };
        match &statement.kind {
            mir::Statement::ScopeEnter { .. }
            | mir::Statement::ScopeExit { .. }
            | mir::Statement::StorageLive { .. }
            | mir::Statement::StorageDead { .. }
            | mir::Statement::Read { .. }
            | mir::Statement::AssignmentRootUse { .. }
            | mir::Statement::Call { .. }
            | mir::Statement::Perform
            | mir::Statement::Function { .. }
            | mir::Statement::DropCandidate { .. } => rest(self, ctx, k),
            mir::Statement::Handling {
                stmt,
                effect_name,
                body: handler_body,
            } => self.lower_mir_handling(
                stmt,
                effect_name,
                handler_body,
                body,
                block,
                index,
                statements,
                ctx,
                k,
                loops,
            ),
            mir::Statement::DeclBody { .. } => rest(self, ctx, k),
            mir::Statement::Bind { lhs, rhs, .. } => {
                self.lower_mir_bind(lhs, *rhs, body, block, index, statements, ctx, k, loops)
            }
            mir::Statement::Assign { lhs, rhs, .. } => {
                let drop_old_value = Self::assignment_drop_elaboration(statements, index)
                    == Some(mir::DropElaboration::Static);
                self.lower_mir_assignment(
                    lhs,
                    rhs,
                    drop_old_value,
                    body,
                    block,
                    index,
                    statements,
                    ctx,
                    k,
                    loops,
                )
            }
            mir::Statement::ConsumeValue { expr, .. } => {
                self.lower_mir_discard(expr, body, block, index, statements, ctx, k, loops)
            }
            mir::Statement::ReturnValue {
                expr, destination, ..
            } => {
                let target = match destination {
                    mir::ValueDestination::Continuation => k,
                    mir::ValueDestination::Return => {
                        self.wrap_cont_with_drop_bindings(ctx, ctx.ret_k, &ctx.drop_stack)
                    }
                };
                if let Some(done) = self.try_mir_effect_split(
                    expr,
                    MirRestBinding::Deliver,
                    body,
                    block,
                    index,
                    statements,
                    ctx,
                    target,
                    loops,
                ) {
                    return done;
                }
                self.lower_expr(expr, ctx, target)
            }
            mir::Statement::ContinueValue { expr, .. } if ctx.resume_k.is_some() => {
                let Some(resume_k) = ctx.resume_k else {
                    return self.dead_end("resume_linkage");
                };
                let value_ty = self.expr_lambda_ty(expr, ctx);
                let bot = self.p.ty_bot();
                let send = self.p.func("resume_value", value_ty, bot);
                let value = self.p.var(send);
                let pair = self.p.tuple(&[value, ctx.raw_ret_k]);
                let resume_body = self.p.app(resume_k, pair);
                let body = self.lower_drop_bindings_then(ctx, &ctx.drop_stack, resume_body);
                self.p.set_body(send, body);
                let send_ref = self.p.func_ref(send);
                self.lower_expr(expr, ctx, send_ref)
            }
            mir::Statement::ContinueValue { expr, .. } => {
                self.lower_mir_discard(expr, body, block, index, statements, ctx, k, loops)
            }
        }
    }

    fn lower_mir_bind(
        &mut self,
        lhs: &crate::node_kinds::pattern::Pattern,
        rhs: Option<&Expr>,
        body: &mir::Body<'_>,
        block: mir::BlockId,
        index: usize,
        statements: &[mir::LocatedStatement<'_>],
        ctx: &Ctx,
        k: ExprId,
        loops: &[(mir::BlockId, ExprId, mir::BlockId, ExprId)],
    ) -> ExprId {
        let Some(rhs) = rhs else {
            return self.lower_mir_statements(body, block, index + 1, statements, ctx, k, loops);
        };
        let PatternKind::Bind(name) = &lhs.kind else {
            let value_ty = self.expr_lambda_ty(rhs, ctx);
            let bot = self.p.ty_bot();
            let bind = self.p.func("let_destructure", value_ty, bot);
            let bound = self.p.var(bind);
            let check_ty = self.checker_ty(rhs, ctx);
            let mut binds: Vec<(Symbol, ExprId)> = vec![];
            patterns::collect_irrefutable_binds(self, lhs, bound, &check_ty, &mut binds);
            let mut inner = ctx.clone();
            let mut celled: Vec<(Symbol, ExprId)> = vec![];
            let mut drop_bindings: Vec<DropBinding> = vec![];
            for (symbol, value) in binds {
                if inner.cellable.contains(&symbol) {
                    celled.push((symbol, value));
                } else {
                    inner.env.insert(symbol, Binding::Value(value));
                }
                if let Some(ty) = self.symbol_check_ty(symbol, &ctx.theta)
                    && let Some(drop) = self.drop_binding_for_symbol(ctx.unit, symbol, ty)
                {
                    drop_bindings.push(drop);
                }
            }
            let rest_body = self.with_cells(&celled, &mut inner, |this, inner| {
                inner.drop_stack.extend(drop_bindings.clone());
                let scope_k = this.wrap_cont_with_drop_bindings(inner, k, &drop_bindings);
                inner.tail_k = scope_k;
                this.lower_mir_statements(body, block, index + 1, statements, inner, scope_k, loops)
            });
            self.p.set_body(bind, rest_body);
            let bind_ref = self.p.func_ref(bind);
            return self.lower_expr(rhs, ctx, bind_ref);
        };
        let Ok(symbol) = name.symbol() else {
            return self.lower_mir_statements(body, block, index + 1, statements, ctx, k, loops);
        };

        let mutated = ctx.cellable.contains(&symbol);
        if let Some(done) = self.try_mir_effect_split(
            rhs,
            MirRestBinding::Bind(symbol, mutated),
            body,
            block,
            index,
            statements,
            ctx,
            k,
            loops,
        ) {
            return done;
        }
        let value_ty = self.expr_lambda_ty(rhs, ctx);
        let bot = self.p.ty_bot();
        let bind = self
            .p
            .func(&format!("let_{}", name.name_str()), value_ty, bot);
        let bound = self.p.var(bind);
        let mut inner = ctx.clone();
        let binding_ty = self
            .symbol_check_ty(symbol, &ctx.theta)
            .unwrap_or_else(|| self.checker_ty(rhs, ctx));
        let drop_binding = self.drop_binding_for_symbol(ctx.unit, symbol, binding_ty);
        let rest_body = if mutated {
            self.with_cells(&[(symbol, bound)], &mut inner, |this, inner| {
                let drops = drop_binding.clone().into_iter().collect::<Vec<_>>();
                inner.drop_stack.extend(drops.clone());
                let scope_k = this.wrap_cont_with_drop_bindings(inner, k, &drops);
                inner.tail_k = scope_k;
                this.lower_mir_statements(body, block, index + 1, statements, inner, scope_k, loops)
            })
        } else {
            inner.env.insert(symbol, Binding::Value(bound));
            let drops = drop_binding.into_iter().collect::<Vec<_>>();
            inner.drop_stack.extend(drops.clone());
            let scope_k = self.wrap_cont_with_drop_bindings(&inner, k, &drops);
            inner.tail_k = scope_k;
            self.lower_mir_statements(body, block, index + 1, statements, &inner, scope_k, loops)
        };
        self.p.set_body(bind, rest_body);
        let bind_ref = self.p.func_ref(bind);
        self.lower_expr(rhs, ctx, bind_ref)
    }

    fn lower_mir_assignment(
        &mut self,
        lhs: &Expr,
        rhs: &Expr,
        drop_old_value: bool,
        body: &mir::Body<'_>,
        block: mir::BlockId,
        index: usize,
        statements: &[mir::LocatedStatement<'_>],
        ctx: &Ctx,
        k: ExprId,
        loops: &[(mir::BlockId, ExprId, mir::BlockId, ExprId)],
    ) -> ExprId {
        let target = self.assignment_target(lhs, ctx);
        let Some((cell, path)) = target else {
            return self.lower_mir_statements(body, block, index + 1, statements, ctx, k, loops);
        };
        let void_ty = self.p.ty_void();
        let bot = self.p.ty_bot();
        let after = self.p.func("after_set", void_ty, bot);
        let after_body =
            self.lower_mir_statements(body, block, index + 1, statements, ctx, k, loops);
        self.p.set_body(after, after_body);
        let after_ref = self.p.func_ref(after);

        let rhs_ty = self.expr_lambda_ty(rhs, ctx);
        let setter = self.p.func("set", rhs_ty, bot);
        let value = self.p.var(setter);
        let stored = if path.is_empty() {
            value
        } else {
            self.rebuilt_assignment_value(cell, &path, value)
        };
        let cell_set = self.p.primop(Op::CellSet, &[cell, stored], void_ty);
        let setter_body = {
            let after_set = self.p.app(after_ref, cell_set);
            let lhs_check_ty = self.checker_ty(lhs, ctx);
            if drop_old_value && self.needs_drop_type(ctx.unit, &lhs_check_ty) {
                let old_ty = self.map_ty(&lhs_check_ty);
                let old = self.assignment_old_value(cell, &path, old_ty);
                self.lower_drop_value_then(ctx, old, &lhs_check_ty, after_set)
            } else {
                after_set
            }
        };
        self.p.set_body(setter, setter_body);
        let setter_ref = self.p.func_ref(setter);
        self.lower_expr(rhs, ctx, setter_ref)
    }

    fn assignment_drop_elaboration(
        statements: &[mir::LocatedStatement<'_>],
        assignment_index: usize,
    ) -> Option<mir::DropElaboration> {
        let previous = assignment_index.checked_sub(1)?;
        let mir::Statement::DropCandidate {
            elaboration,
            reason: mir::DropReason::AssignmentReplace,
            ..
        } = &statements.get(previous)?.kind
        else {
            return None;
        };
        *elaboration
    }

    fn lower_mir_discard(
        &mut self,
        expr: &Expr,
        body: &mir::Body<'_>,
        block: mir::BlockId,
        index: usize,
        statements: &[mir::LocatedStatement<'_>],
        ctx: &Ctx,
        k: ExprId,
        loops: &[(mir::BlockId, ExprId, mir::BlockId, ExprId)],
    ) -> ExprId {
        if let Some(done) = self.try_mir_effect_split(
            expr,
            MirRestBinding::Discard,
            body,
            block,
            index,
            statements,
            ctx,
            k,
            loops,
        ) {
            return done;
        }
        let (value_ty, pure_value) = match self.try_pure(expr, ctx) {
            Some(value) => (self.p.expr_ty(value), Some(value)),
            None => (self.expr_lambda_ty(expr, ctx), None),
        };
        let bot = self.p.ty_bot();
        let drop_k = self.p.func("drop", value_ty, bot);
        let rest_body =
            self.lower_mir_statements(body, block, index + 1, statements, ctx, k, loops);
        self.p.set_body(drop_k, rest_body);
        let drop_ref = self.p.func_ref(drop_k);
        match pure_value {
            Some(value) => self.p.app(drop_ref, value),
            None => self.lower_expr(expr, ctx, drop_ref),
        }
    }

    fn lower_mir_handling(
        &mut self,
        stmt: &Stmt,
        effect_name: &crate::name::Name,
        handler_block: &Block,
        body: &mir::Body<'_>,
        block: mir::BlockId,
        index: usize,
        statements: &[mir::LocatedStatement<'_>],
        ctx: &Ctx,
        k: ExprId,
        loops: &[(mir::BlockId, ExprId, mir::BlockId, ExprId)],
    ) -> ExprId {
        if k != ctx.tail_k {
            self.diagnostics
                .push("lowering: @handle inside a nested block (not yet supported)".into());
            return self.dead_end("nested_handle");
        }
        let handler_sym = self.units[ctx.unit]
            .resolved
            .effect_handler_definitions
            .get(&stmt.id)
            .copied();
        let Some(handler_sym) = handler_sym else {
            self.diagnostics
                .push("lowering: @handle without a resolved handler".into());
            return self.dead_end("unresolved_handler");
        };
        let sig = effect_name.symbol().ok().and_then(|s| {
            self.units
                .iter()
                .find_map(|u| u.types.catalog.effects.get(&s).cloned())
        });
        let Some(sig) = sig else {
            self.diagnostics
                .push("lowering: @handle of an undeclared effect".into());
            return self.dead_end("undeclared_effect");
        };
        if !sig.generics.is_empty() {
            self.diagnostics
                .push("lowering: handlers for generic effects (not yet supported)".into());
            return self.dead_end("generic_effect_handler");
        }

        let handler_tys = self
            .units
            .iter()
            .find_map(|u| u.types.handler_payload_tys.get(&handler_sym).cloned());
        let mut payload_tys = Vec::with_capacity(sig.params.len());
        for (i, param) in sig.params.iter().enumerate() {
            let ty = handler_tys
                .as_ref()
                .and_then(|tys| tys.get(i))
                .unwrap_or(param);
            if matches!(ty, CheckTy::Var(_)) {
                self.diagnostics.push(
                    "lowering: effect parameter type unknown (annotate the effect declaration)"
                        .into(),
                );
                return self.dead_end("unknown_effect_parameter");
            }
            payload_tys.push(self.map_ty(ty));
        }
        if handler_block.args.len() > payload_tys.len() {
            self.diagnostics.push(
                "lowering: handler block takes more arguments than the effect declares".into(),
            );
            return self.dead_end("handler_arity");
        }

        let slot_ty = self.p.expr_ty(ctx.raw_ret_k);
        let bot = self.p.ty_bot();
        let resume_pair_ty = (!sig.ret.is_never()).then(|| {
            let resume_value_ty = self.map_ty(&sig.ret);
            self.p.ty_tuple(&[resume_value_ty, slot_ty])
        });
        let mut dom_items = payload_tys;
        if let Some(pair_ty) = resume_pair_ty {
            dom_items.push(self.p.ty_fn(pair_ty, bot));
        }
        dom_items.push(slot_ty);
        let dom = self.p.ty_tuple(&dom_items);
        let cap = self.p.func("handler", dom, bot);
        self.escaping.insert(cap);
        let cap_var = self.p.var(cap);
        let rk = self.p.extract(cap_var, (dom_items.len() - 1) as u32);
        let mut inner = self.rebase_into_closure(ctx, rk);
        if resume_pair_ty.is_some() {
            inner.resume_k = Some(self.p.extract(cap_var, (dom_items.len() - 2) as u32));
        }
        let mut celled: Vec<(Symbol, ExprId)> = vec![];
        for (i, arg) in handler_block.args.iter().enumerate() {
            let value = self.p.extract(cap_var, i as u32);
            let Ok(symbol) = arg.name.symbol() else {
                continue;
            };
            if inner.cellable.contains(&symbol) {
                celled.push((symbol, value));
            } else {
                inner.env.insert(symbol, Binding::Value(value));
            }
        }
        let handler_body_expr = self.with_cells(&celled, &mut inner, |this, inner| {
            let handler_k = inner.ret_k;
            this.lower_block(handler_block, inner, handler_k)
        });
        self.p.set_body(cap, handler_body_expr);

        let scope_result_ty = match *self.p.ty_kind(slot_ty) {
            TyKind::Fn(carried, _) => carried,
            _ => self.p.ty_void(),
        };
        let cap_ref = self.p.func_ref(cap);
        self.handler_caps.insert(
            handler_sym,
            HandlerCap {
                cap: cap_ref,
                scope_result_ty,
                resume_pair_ty,
            },
        );

        let mut scope_ctx = ctx.clone();
        scope_ctx.local_handlers.insert(handler_sym);
        self.lower_mir_statements(body, block, index + 1, statements, &scope_ctx, k, loops)
    }

    fn try_mir_effect_split(
        &mut self,
        expr: &Expr,
        binding: MirRestBinding,
        body: &mir::Body<'_>,
        block: mir::BlockId,
        index: usize,
        statements: &[mir::LocatedStatement<'_>],
        ctx: &Ctx,
        k: ExprId,
        loops: &[(mir::BlockId, ExprId, mir::BlockId, ExprId)],
    ) -> Option<ExprId> {
        if let ExprKind::CallEffect { args, .. } = &expr.kind
            && let Some(&handler_sym) = self.units[ctx.unit].resolved.effect_handlers.get(&expr.id)
            && let Some(cap) = self.handler_caps.get(&handler_sym).copied()
            && let Some(pair_ty) = cap.resume_pair_ty
        {
            let handler_reachable = ctx.abort_ok || ctx.local_handlers.contains(&handler_sym);
            if !handler_reachable || k != ctx.tail_k {
                self.diagnostics.push(
                    "lowering: a resumable perform outside the enclosing function's statement spine (not yet supported)"
                        .into(),
                );
                return Some(self.dead_end("resumable_perform_off_spine"));
            }
            let resume_ref = self.rest_mir_closure(
                "after_perform",
                pair_ty,
                binding,
                body,
                block,
                index,
                statements,
                ctx,
                k,
                loops,
            );
            let slot = ctx.raw_ret_k;
            let arg_exprs: Vec<&Expr> = args.iter().map(|a| &a.value).collect();
            return Some(
                self.lower_args(&arg_exprs, ctx, vec![], &mut |this, mut values| {
                    values.push(resume_ref);
                    values.push(slot);
                    let tuple = this.p.tuple(&values);
                    this.p.app(cap.cap, tuple)
                }),
            );
        }

        self.abortable_callee(expr, ctx)?;
        if !ctx.abort_ok || k != ctx.tail_k {
            self.diagnostics.push(
                "lowering: a call that can abort outside the enclosing function's statement spine (not yet supported)"
                    .into(),
            );
            return Some(self.dead_end("abort_call_off_spine"));
        }
        let ExprKind::Call {
            callee,
            args,
            trailing_block,
            ..
        } = &expr.kind
        else {
            return Some(self.dead_end("abort_call_shape"));
        };
        if trailing_block.is_some() {
            self.diagnostics.push(
                "lowering: trailing block on a call that can abort (not yet supported)".into(),
            );
            return Some(self.dead_end("abort_call_trailing_block"));
        }
        let target = self.resolve_callee(expr, callee, args, ctx);
        let Some((label, _, prefix)) = target else {
            return Some(self.dead_end("abort_call_unresolved"));
        };
        if !matches!(prefix, Prefix::None) {
            self.diagnostics
                .push("lowering: method or init calls that can abort (not yet supported)".into());
            return Some(self.dead_end("abort_call_method"));
        }

        let dom_ty = self.p.dom(label);
        let normal_k_ty = match self.p.ty_kind(dom_ty) {
            TyKind::Tuple(items) if items.len() >= 2 => items[items.len() - 2],
            _ => {
                self.diagnostics
                    .push("lowering: abort-capable callee without a normal-return slot".into());
                return Some(self.dead_end("abort_callee_shape"));
            }
        };
        let pair_ty = match *self.p.ty_kind(normal_k_ty) {
            TyKind::Fn(pair, _) => pair,
            _ => {
                self.diagnostics
                    .push("lowering: abort-capable callee without a paired normal return".into());
                return Some(self.dead_end("abort_callee_shape"));
            }
        };
        let callee_slot_ty = match self.p.ty_kind(pair_ty) {
            TyKind::Tuple(items) if items.len() == 2 => items[1],
            _ => {
                self.diagnostics
                    .push("lowering: abort-capable callee without a paired normal return".into());
                return Some(self.dead_end("abort_callee_shape"));
            }
        };
        if callee_slot_ty != self.p.expr_ty(ctx.raw_ret_k) {
            self.diagnostics.push(
                "lowering: abort linkage type mismatch (handler scope and call scope carry different value types)"
                    .into(),
            );
        }

        let rest_ref = self.rest_mir_closure(
            "after_abortable",
            pair_ty,
            binding,
            body,
            block,
            index,
            statements,
            ctx,
            k,
            loops,
        );
        let slot = ctx.raw_ret_k;
        let func_ref = self.p.func_ref(label);
        let arg_exprs: Vec<&Expr> = args.iter().map(|a| &a.value).collect();
        Some(
            self.lower_args(&arg_exprs, ctx, vec![], &mut |this, mut values| {
                values.push(rest_ref);
                values.push(slot);
                let tuple = this.p.tuple(&values);
                this.p.app(func_ref, tuple)
            }),
        )
    }

    fn rest_mir_closure(
        &mut self,
        name: &str,
        pair_ty: TyId,
        binding: MirRestBinding,
        body: &mir::Body<'_>,
        block: mir::BlockId,
        index: usize,
        statements: &[mir::LocatedStatement<'_>],
        ctx: &Ctx,
        k: ExprId,
        loops: &[(mir::BlockId, ExprId, mir::BlockId, ExprId)],
    ) -> ExprId {
        let bot = self.p.ty_bot();
        let rest_k = self.p.func(name, pair_ty, bot);
        self.escaping.insert(rest_k);
        let rest_var = self.p.var(rest_k);
        let value = self.p.extract(rest_var, 0);
        let rk = self.p.extract(rest_var, 1);
        let mut inner = self.rebase_into_closure(ctx, rk);
        let inner_k = inner.ret_k;
        let body_expr = match binding {
            MirRestBinding::Bind(symbol, mutated) => {
                let drop_binding = self
                    .symbol_check_ty(symbol, &ctx.theta)
                    .and_then(|ty| self.drop_binding_for_symbol(ctx.unit, symbol, ty));
                if mutated {
                    self.with_cells(&[(symbol, value)], &mut inner, |this, inner| {
                        let drops = drop_binding.clone().into_iter().collect::<Vec<_>>();
                        inner.drop_stack.extend(drops.clone());
                        let bound_k = inner.ret_k;
                        let scope_k = this.wrap_cont_with_drop_bindings(inner, bound_k, &drops);
                        inner.tail_k = scope_k;
                        this.lower_mir_statements(
                            body,
                            block,
                            index + 1,
                            statements,
                            inner,
                            scope_k,
                            loops,
                        )
                    })
                } else {
                    inner.env.insert(symbol, Binding::Value(value));
                    let drops = drop_binding.into_iter().collect::<Vec<_>>();
                    inner.drop_stack.extend(drops.clone());
                    let scope_k = self.wrap_cont_with_drop_bindings(&inner, inner_k, &drops);
                    inner.tail_k = scope_k;
                    self.lower_mir_statements(
                        body,
                        block,
                        index + 1,
                        statements,
                        &inner,
                        scope_k,
                        loops,
                    )
                }
            }
            MirRestBinding::Discard => self.lower_mir_statements(
                body,
                block,
                index + 1,
                statements,
                &inner,
                inner_k,
                loops,
            ),
            MirRestBinding::Deliver => self.p.app(inner_k, value),
        };
        let _ = k;
        self.p.set_body(rest_k, body_expr);
        self.p.func_ref(rest_k)
    }

    fn lower_mir_terminator(
        &mut self,
        body: &mir::Body<'_>,
        block: mir::BlockId,
        ctx: &Ctx,
        k: ExprId,
        loops: &[(mir::BlockId, ExprId, mir::BlockId, ExprId)],
    ) -> ExprId {
        match &body.blocks[block.0].terminator {
            mir::Terminator::Unset | mir::Terminator::Return => {
                let void = self.p.void();
                self.p.app(k, void)
            }
            mir::Terminator::ReturnVoid => {
                let void = self.p.void();
                let body = self.p.app(ctx.ret_k, void);
                self.lower_drop_bindings_then(ctx, &ctx.drop_stack, body)
            }
            mir::Terminator::Break => self.lower_mir_break(ctx, k),
            mir::Terminator::Continue => self.lower_mir_continue(ctx, k),
            mir::Terminator::Jump(target) => {
                if let Some((_, header, _, _)) = loops
                    .iter()
                    .rev()
                    .find(|(header_block, _, _, _)| header_block == target)
                {
                    let void = self.p.void();
                    let jump = self.p.app(*header, void);
                    let drops = self.loop_jump_drops(ctx, *header);
                    return self.lower_drop_bindings_then(ctx, &drops, jump);
                }
                if let Some((_, _, _, exit)) = loops
                    .iter()
                    .rev()
                    .find(|(_, _, exit_block, _)| exit_block == target)
                {
                    let void = self.p.void();
                    let jump = self.p.app(*exit, void);
                    let drops = self.loop_jump_drops(ctx, *exit);
                    return self.lower_drop_bindings_then(ctx, &drops, jump);
                }
                self.lower_mir_block(body, *target, ctx, k, loops)
            }
            mir::Terminator::Branch {
                condition,
                then_block,
                else_block,
            } => {
                let then_body = self.lower_mir_block(body, *then_block, ctx, k, loops);
                let else_body = self.lower_mir_block(body, *else_block, ctx, k, loops);
                self.branch(condition, then_body, else_body, ctx)
            }
            mir::Terminator::Switch {
                scrutinee,
                match_arms: Some(arms),
                ..
            } => self.lower_match(scrutinee, arms, ctx, k),
            mir::Terminator::Switch { .. } => self.dead_end("mir_switch_without_patterns"),
            mir::Terminator::Loop {
                condition,
                body_block,
                exit_block,
            } => {
                let void_ty = self.p.ty_void();
                let bot = self.p.ty_bot();
                let header = self.p.func("loop_head", void_ty, bot);
                let exit = self.p.func("loop_exit", void_ty, bot);
                let header_ref = self.p.func_ref(header);
                let exit_ref = self.p.func_ref(exit);
                let mut next_loops = loops.to_vec();
                next_loops.push((block, header_ref, *exit_block, exit_ref));
                let exit_body = self.lower_mir_block(body, *exit_block, ctx, k, loops);
                self.p.set_body(exit, exit_body);

                let mut loop_ctx = ctx.clone();
                loop_ctx.loops.push(LoopBinding {
                    header: header_ref,
                    exit: exit_ref,
                    drop_depth: ctx.drop_stack.len(),
                });
                let body_expr =
                    self.lower_mir_block(body, *body_block, &loop_ctx, header_ref, &next_loops);
                let header_body = match condition {
                    Some(condition) => {
                        let void = self.p.void();
                        let exit_jump = self.p.app(exit_ref, void);
                        self.branch(condition, body_expr, exit_jump, ctx)
                    }
                    None => body_expr,
                };
                self.p.set_body(header, header_body);
                let void = self.p.void();
                self.p.app(header_ref, void)
            }
        }
    }

    fn lower_mir_break(&mut self, ctx: &Ctx, k: ExprId) -> ExprId {
        match ctx.loops.last() {
            Some(loop_binding) => {
                let void = self.p.void();
                let drops: Vec<DropBinding> = ctx.drop_stack[loop_binding.drop_depth..].to_vec();
                let body = self.p.app(loop_binding.exit, void);
                self.lower_drop_bindings_then(ctx, &drops, body)
            }
            None => {
                self.diagnostics.push("lowering: break outside loop".into());
                let void = self.p.void();
                self.p.app(k, void)
            }
        }
    }

    fn loop_jump_drops(&self, ctx: &Ctx, target: ExprId) -> Vec<DropBinding> {
        let Some(loop_binding) = ctx
            .loops
            .iter()
            .rev()
            .find(|loop_binding| loop_binding.header == target || loop_binding.exit == target)
        else {
            return vec![];
        };
        ctx.drop_stack[loop_binding.drop_depth..].to_vec()
    }

    fn lower_mir_continue(&mut self, ctx: &Ctx, k: ExprId) -> ExprId {
        match ctx.loops.last() {
            Some(loop_binding) => {
                let void = self.p.void();
                let drops: Vec<DropBinding> = ctx.drop_stack[loop_binding.drop_depth..].to_vec();
                let body = self.p.app(loop_binding.header, void);
                self.lower_drop_bindings_then(ctx, &drops, body)
            }
            None => {
                self.diagnostics
                    .push("lowering: continue outside loop".into());
                let void = self.p.void();
                self.p.app(k, void)
            }
        }
    }
}
