use super::*;
use crate::mir;
use crate::ownership::{BodyKind, DropKind};

#[derive(Clone, Copy)]
enum MirRestBinding {
    Bind(Symbol, bool),
    Discard,
    Deliver,
}

struct PendingDrop {
    symbol: Symbol,
    key_path: OwnershipKeyPath,
    ty: CheckTy,
    has_dynamic_flags: bool,
    elaboration: Option<mir::DropElaboration>,
}

/// The position of a MIR→λ_G walk: the statement currently under the cursor
/// (`body.blocks[block].statements[index]`) plus the loops in scope. Threaded by
/// value through the statement lowerers so they share one positional argument
/// instead of `(body, block, index, statements, loops)`. The mutable block cache
/// and the per-continuation `ctx`/`k` stay as separate arguments.
#[derive(Clone, Copy)]
struct MirCursor<'b, 'ast> {
    body: &'b mir::Body<'ast>,
    block: mir::BlockId,
    index: usize,
    loops: &'b [MirLoop],
}

impl<'b, 'ast> MirCursor<'b, 'ast> {
    fn statements(self) -> &'b [mir::LocatedStatement<'ast>] {
        &self.body.blocks[self.block.0].statements
    }

    fn statement(self) -> &'b mir::LocatedStatement<'ast> {
        &self.statements()[self.index]
    }

    /// The next statement in the same block.
    fn advance(self) -> Self {
        MirCursor {
            index: self.index + 1,
            ..self
        }
    }

    /// The start of another block, keeping the same loops in scope.
    fn at_block(self, block: mir::BlockId) -> Self {
        MirCursor {
            block,
            index: 0,
            ..self
        }
    }

    fn with_loops(self, loops: &'b [MirLoop]) -> Self {
        MirCursor { loops, ..self }
    }
}

impl<'a> Lowering<'a> {
    pub(super) fn lower_mir_body(&mut self, body: &mir::Body<'_>, ctx: &Ctx, k: ExprId) -> ExprId {
        let mut cache = MirBlockCache::default();
        let cursor = MirCursor {
            body,
            block: body.entry,
            index: 0,
            loops: &[],
        };
        self.lower_mir_statements(cursor, ctx, k, &mut cache)
    }

    fn lower_mir_block(
        &mut self,
        cursor: MirCursor,
        ctx: &Ctx,
        k: ExprId,
        cache: &mut MirBlockCache,
    ) -> ExprId {
        let key = MirBlockKey {
            block: cursor.block,
            k,
            ctx: ctx.mir_key(),
            loops: cursor.loops.to_vec(),
        };
        if let Some(&entry) = cache.blocks.get(&key) {
            let void = self.p.void();
            return self.p.app(entry, void);
        }

        let void_ty = self.p.ty_void();
        let bot = self.p.ty_bot();
        let label = self.p.func("mir_bb", void_ty, bot);
        let entry = self.p.func_ref(label);
        cache.blocks.insert(key, entry);
        let body_expr = self.lower_mir_statements(cursor, ctx, k, cache);
        self.p.set_body(label, body_expr);
        let void = self.p.void();
        self.p.app(entry, void)
    }

    fn lower_mir_statements(
        &mut self,
        cursor: MirCursor,
        ctx: &Ctx,
        k: ExprId,
        cache: &mut MirBlockCache,
    ) -> ExprId {
        let Some(statement) = cursor.statements().get(cursor.index) else {
            return self.lower_mir_terminator(cursor, ctx, k, cache);
        };
        let mut rest = |this: &mut Self, ctx: &Ctx, k: ExprId| {
            this.lower_mir_statements(cursor.advance(), ctx, k, cache)
        };
        match &statement.kind {
            mir::Statement::ScopeEnter { .. }
            | mir::Statement::ScopeExit { .. }
            | mir::Statement::StorageLive { .. }
            | mir::Statement::Read { .. }
            | mir::Statement::AssignmentRootUse { .. }
            | mir::Statement::Perform
            | mir::Statement::DropCandidate { .. } => rest(self, ctx, k),
            mir::Statement::StorageDead { symbol, .. } => {
                self.lower_mir_storage_dead(*symbol, cursor, ctx, k, cache)
            }
            mir::Statement::Call { .. } | mir::Statement::Function { .. } => {
                let rest_body = rest(self, ctx, k);
                self.clear_moved_drop_flags_then(ctx, cursor.body, statement, rest_body)
            }
            mir::Statement::Handling {
                stmt,
                effect_name,
                body: handler_body,
            } => self.lower_mir_handling(stmt, effect_name, handler_body, cursor, ctx, k, cache),
            mir::Statement::DeclBody { .. } => rest(self, ctx, k),
            mir::Statement::Bind { lhs, rhs, .. } => {
                self.lower_mir_bind(lhs, *rhs, cursor, ctx, k, cache)
            }
            mir::Statement::Assign {
                lhs, rhs, target, ..
            } => self.lower_mir_assignment(lhs, rhs, target.as_ref(), cursor, ctx, k, cache),
            mir::Statement::ConsumeValue { expr, .. } => {
                self.lower_mir_discard(expr, cursor, ctx, k, cache)
            }
            mir::Statement::ReturnValue {
                expr, destination, ..
            } => {
                let target = match destination {
                    mir::ValueDestination::Continuation => {
                        self.wrap_cont_with_following_drops(ctx, cursor, k)
                    }
                    mir::ValueDestination::Return => {
                        self.wrap_cont_with_following_drops(ctx, cursor, ctx.ret_k)
                    }
                };
                let mut tail_ctx;
                let value_ctx = if target != ctx.tail_k {
                    tail_ctx = ctx.clone();
                    tail_ctx.tail_k = target;
                    &tail_ctx
                } else {
                    ctx
                };
                if let Some(done) = self.try_mir_effect_split(
                    expr,
                    MirRestBinding::Deliver,
                    cursor,
                    value_ctx,
                    target,
                    cache,
                ) {
                    return done;
                }
                let target = self.wrap_moved_value_cont(value_ctx, cursor.body, statement, target);
                self.lower_expr(expr, value_ctx, target)
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
                let resume_body = self.lower_drop_bindings_then(ctx, &ctx.drop_stack, resume_body);
                let resume_body =
                    self.clear_moved_drop_flags_then(ctx, cursor.body, statement, resume_body);
                self.p.set_body(send, resume_body);
                let send_ref = self.p.func_ref(send);
                self.lower_expr(expr, ctx, send_ref)
            }
            mir::Statement::ContinueValue { expr, .. } => {
                self.lower_mir_discard(expr, cursor, ctx, k, cache)
            }
        }
    }

    fn lower_mir_bind(
        &mut self,
        lhs: &crate::node_kinds::pattern::Pattern,
        rhs: Option<&Expr>,
        cursor: MirCursor,
        ctx: &Ctx,
        k: ExprId,
        cache: &mut MirBlockCache,
    ) -> ExprId {
        let Some(rhs) = rhs else {
            return self.lower_mir_statements(cursor.advance(), ctx, k, cache);
        };
        let PatternKind::Bind(name) = &lhs.kind else {
            let value_ty = self.expr_lambda_ty(rhs, ctx);
            let bot = self.p.ty_bot();
            let bind = self.p.func("let_destructure", value_ty, bot);
            let bound = self.p.var(bind);
            let binding_ty = self.checker_ty(rhs, ctx);
            let mut binds: Vec<(Symbol, ExprId)> = vec![];
            patterns::collect_irrefutable_binds(self, lhs, bound, &binding_ty, &mut binds);
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
                    && let Some(drop) =
                        self.drop_binding_for_mir_symbol(ctx, cursor.body, symbol, ty)
                {
                    drop_bindings.push(drop);
                }
            }
            let rest_body = self.with_cells(&celled, &mut inner, |this, inner| {
                this.with_drop_flags(&drop_bindings, inner, |this, inner| {
                    inner.drop_stack.extend(drop_bindings.clone());
                    let rest_body = this.lower_mir_statements(cursor.advance(), inner, k, cache);
                    this.clear_moved_drop_flags_then(
                        inner,
                        cursor.body,
                        cursor.statement(),
                        rest_body,
                    )
                })
            });
            self.p.set_body(bind, rest_body);
            let bind_ref = self.p.func_ref(bind);
            return self.lower_expr(rhs, ctx, bind_ref);
        };
        let Ok(symbol) = name.symbol() else {
            return self.lower_mir_statements(cursor.advance(), ctx, k, cache);
        };

        let mutated = ctx.cellable.contains(&symbol);
        if let Some(done) = self.try_mir_effect_split(
            rhs,
            MirRestBinding::Bind(symbol, mutated),
            cursor,
            ctx,
            k,
            cache,
        ) {
            return done;
        }
        let value_ty = self.expr_lambda_ty(rhs, ctx);
        let bot = self.p.ty_bot();
        let bind = self
            .p
            .func(&format!("let_{}", name.name_str()), value_ty, bot);
        let bound = self.p.var(bind);
        let binding_ty = self
            .symbol_check_ty(symbol, &ctx.theta)
            .unwrap_or_else(|| self.checker_ty(rhs, ctx));
        let drop_binding = self.drop_binding_for_mir_symbol(ctx, cursor.body, symbol, binding_ty);
        let mut inner = ctx.clone();
        let rest_body = if mutated {
            self.with_cells(&[(symbol, bound)], &mut inner, |this, inner| {
                let drops = drop_binding.clone().into_iter().collect::<Vec<_>>();
                this.with_drop_flags(&drops, inner, |this, inner| {
                    inner.drop_stack.extend(drops.clone());
                    let rest_body = this.lower_mir_statements(cursor.advance(), inner, k, cache);
                    this.clear_moved_drop_flags_then(
                        inner,
                        cursor.body,
                        cursor.statement(),
                        rest_body,
                    )
                })
            })
        } else {
            inner.env.insert(symbol, Binding::Value(bound));
            let drops = drop_binding.into_iter().collect::<Vec<_>>();
            self.with_drop_flags(&drops, &mut inner, |this, inner| {
                inner.drop_stack.extend(drops.clone());
                let rest_body = this.lower_mir_statements(cursor.advance(), inner, k, cache);
                this.clear_moved_drop_flags_then(inner, cursor.body, cursor.statement(), rest_body)
            })
        };
        self.p.set_body(bind, rest_body);
        let bind_ref = self.p.func_ref(bind);
        self.lower_expr(rhs, ctx, bind_ref)
    }

    fn drop_binding_for_mir_symbol(
        &self,
        ctx: &Ctx,
        body: &mir::Body<'_>,
        symbol: Symbol,
        ty: CheckTy,
    ) -> Option<DropBinding> {
        if !self.needs_drop_type(ctx.unit, &ty) {
            return None;
        }
        let dynamic_flags = self.drop_flag_keys_for_symbol(ctx, body, symbol);
        if dynamic_flags.is_empty() && self.symbol_has_move_fact(ctx.unit, symbol) {
            return None;
        }
        Some(DropBinding {
            symbol,
            key_path: OwnershipKeyPath::root(symbol),
            ty,
            dynamic_flags,
        })
    }

    fn drop_flag_keys_for_symbol(
        &self,
        ctx: &Ctx,
        body: &mir::Body<'_>,
        symbol: Symbol,
    ) -> Vec<OwnershipKeyPath> {
        let mut keys = Vec::new();
        let root = OwnershipKeyPath::root(symbol);
        let mut needs_root_flag = false;

        for obligation in &self.units[ctx.unit].ownership.drop_plan.obligations {
            if !self.ownership_point_matches_body(ctx, body, obligation.point) {
                continue;
            }
            if obligation.key_path.root != symbol {
                continue;
            }
            if !matches!(obligation.kind, DropKind::Conditional | DropKind::Open) {
                continue;
            }
            needs_root_flag = true;
            if !obligation.key_path.fields.is_empty() {
                Self::push_unique_drop_flag_key(&mut keys, obligation.key_path.clone());
            }
        }

        for fact in &self.units[ctx.unit].ownership.facts.moves {
            if !self.ownership_point_matches_body(ctx, body, fact.point) {
                continue;
            }
            if fact.source.root != symbol {
                continue;
            }
            needs_root_flag = true;
            if !fact.source.fields.is_empty() {
                Self::push_unique_drop_flag_key(&mut keys, fact.source.clone());
            }
        }

        if needs_root_flag {
            keys.insert(0, root);
        }
        keys
    }

    fn wrap_cont_with_following_drops(
        &mut self,
        ctx: &Ctx,
        cursor: MirCursor,
        k: ExprId,
    ) -> ExprId {
        let drops = self.following_drop_candidates(ctx, cursor);
        if drops.is_empty() {
            return k;
        }
        let TyKind::Fn(value_ty, _) = *self.p.ty_kind(self.p.expr_ty(k)) else {
            self.diagnostics
                .push("lowering: drop continuation target is not a function".into());
            return k;
        };
        let bot = self.p.ty_bot();
        let wrapper = self.p.func("drop_scope", value_ty, bot);
        let value = self.p.var(wrapper);
        let mut tail = self.p.app(k, value);
        for drop in drops.iter().rev() {
            tail = self.lower_candidate_drop_then(ctx, drop, tail);
        }
        self.p.set_body(wrapper, tail);
        self.p.func_ref(wrapper)
    }

    fn following_drop_candidates(&self, ctx: &Ctx, cursor: MirCursor) -> Vec<PendingDrop> {
        let body = cursor.body;
        let mut drops = Vec::new();
        for statement in cursor.statements().iter().skip(cursor.index + 1) {
            match &statement.kind {
                mir::Statement::DropCandidate {
                    reason: reason @ (mir::DropReason::ScopeExit | mir::DropReason::EarlyExit),
                    target:
                        mir::DropTarget::Symbol {
                            symbol: target_symbol,
                            ..
                        },
                    key_path,
                    elaboration,
                } => {
                    let Some(drop) = ctx
                        .drop_stack
                        .iter()
                        .rev()
                        .find(|drop| drop.symbol == *target_symbol)
                    else {
                        continue;
                    };
                    let key_path = key_path
                        .as_ref()
                        .and_then(|key_path| Self::ownership_key_path_from_mir(body, key_path))
                        .unwrap_or_else(|| drop.key_path.clone());
                    let elaboration = elaboration.or_else(|| {
                        self.drop_elaboration_at(ctx, body, statement.point, *reason, &key_path)
                    });
                    drops.push(PendingDrop {
                        symbol: drop.symbol,
                        key_path,
                        ty: drop.ty.clone(),
                        has_dynamic_flags: !drop.dynamic_flags.is_empty(),
                        elaboration,
                    });
                }
                mir::Statement::StorageDead { .. } | mir::Statement::ScopeExit { .. } => {}
                _ => break,
            }
        }
        drops
    }

    fn drop_elaboration_at(
        &self,
        ctx: &Ctx,
        body: &mir::Body<'_>,
        point: mir::StatementId,
        reason: mir::DropReason,
        key_path: &OwnershipKeyPath,
    ) -> Option<mir::DropElaboration> {
        let reason = match reason {
            mir::DropReason::ScopeExit => crate::ownership::DropReason::ScopeExit,
            mir::DropReason::AssignmentReplace => crate::ownership::DropReason::AssignmentReplace,
            mir::DropReason::EarlyExit => crate::ownership::DropReason::EarlyExit,
        };
        self.units[ctx.unit]
            .ownership
            .drop_plan
            .obligations
            .iter()
            .find(|obligation| {
                obligation.point.point == point.0 as u32
                    && self.ownership_point_matches_body(ctx, body, obligation.point)
                    && obligation.reason == reason
                    && obligation.key_path == *key_path
            })
            .map(|obligation| Self::drop_elaboration_of(obligation.kind))
    }

    fn lower_candidate_drop_then(&mut self, ctx: &Ctx, drop: &PendingDrop, next: ExprId) -> ExprId {
        let Some(value) = self.binding_value(ctx, drop.symbol) else {
            return next;
        };
        match drop.elaboration {
            Some(mir::DropElaboration::Dead) => next,
            Some(mir::DropElaboration::Conditional | mir::DropElaboration::Open) => {
                self.lower_dynamic_assignment_drop_then(ctx, &drop.key_path, value, &drop.ty, next)
            }
            Some(mir::DropElaboration::Static) | None if drop.has_dynamic_flags => {
                self.lower_dynamic_assignment_drop_then(ctx, &drop.key_path, value, &drop.ty, next)
            }
            Some(mir::DropElaboration::Static) | None => {
                self.lower_drop_value_then(ctx, value, &drop.ty, next)
            }
        }
    }

    fn push_unique_drop_flag_key(keys: &mut Vec<OwnershipKeyPath>, key: OwnershipKeyPath) {
        if !keys.iter().any(|existing| existing == &key) {
            keys.push(key);
        }
    }

    fn drop_elaboration_of(kind: DropKind) -> mir::DropElaboration {
        match kind {
            DropKind::Static => mir::DropElaboration::Static,
            DropKind::Dead => mir::DropElaboration::Dead,
            DropKind::Conditional => mir::DropElaboration::Conditional,
            DropKind::Open => mir::DropElaboration::Open,
        }
    }

    fn ownership_point_matches_body(
        &self,
        ctx: &Ctx,
        body: &mir::Body<'_>,
        point: crate::ownership::OwnershipPoint,
    ) -> bool {
        let Some(fact_body) = self.units[ctx.unit]
            .ownership
            .facts
            .bodies
            .get(point.body.0 as usize)
        else {
            return false;
        };
        if fact_body.owner != body.owner {
            return false;
        }
        if body.owner.is_some() {
            return true;
        }
        matches!(
            (&fact_body.kind, ctx.top_level),
            (BodyKind::TopLevel, true) | (BodyKind::Function, false)
        )
    }

    fn ownership_key_path_from_mir(
        body: &mir::Body<'_>,
        key_path: &mir::KeyPath,
    ) -> Option<OwnershipKeyPath> {
        let root = body.locals.get(key_path.root.0)?.symbol;
        let mut result = OwnershipKeyPath::root(root);
        for component in &key_path.components {
            match component {
                mir::KeyPathComponent::Field(field) => {
                    result = result.child(*field);
                }
                mir::KeyPathComponent::TupleField(_)
                | mir::KeyPathComponent::VariantPayload { .. }
                | mir::KeyPathComponent::DerefBorrow
                | mir::KeyPathComponent::Index(_) => return None,
            }
        }
        Some(result)
    }

    fn ownership_key_path_from_assignment_lhs(
        &self,
        ctx: &Ctx,
        lhs: &Expr,
    ) -> Option<OwnershipKeyPath> {
        match &lhs.kind {
            ExprKind::Variable(name) => name.symbol().ok().map(OwnershipKeyPath::root),
            ExprKind::Member(Some(receiver), ..) => {
                let base = self.ownership_key_path_from_assignment_lhs(ctx, receiver)?;
                let field =
                    crate::types::output::stored_field_symbol(self.units[ctx.unit].types, lhs)?;
                Some(base.child(field))
            }
            _ => None,
        }
    }

    fn assignment_drop_elaboration(
        &self,
        ctx: &Ctx,
        cursor: MirCursor,
    ) -> Option<mir::DropElaboration> {
        let previous = cursor.index.checked_sub(1)?;
        let previous = cursor.statements().get(previous)?;
        let mir::Statement::DropCandidate {
            reason: mir::DropReason::AssignmentReplace,
            ..
        } = &previous.kind
        else {
            return None;
        };
        self.units[ctx.unit]
            .ownership
            .drop_plan
            .obligations
            .iter()
            .find(|obligation| {
                obligation.point.point == previous.point.0 as u32
                    && self.ownership_point_matches_body(ctx, cursor.body, obligation.point)
                    && obligation.reason == crate::ownership::DropReason::AssignmentReplace
            })
            .map(|obligation| Self::drop_elaboration_of(obligation.kind))
    }

    fn lower_mir_storage_dead(
        &mut self,
        symbol: Symbol,
        cursor: MirCursor,
        ctx: &Ctx,
        k: ExprId,
        cache: &mut MirBlockCache,
    ) -> ExprId {
        let mut after = ctx.clone();
        after.env.remove(&symbol);
        after.drop_stack.retain(|drop| drop.symbol != symbol);
        after
            .drop_flags
            .retain(|key_path, _| key_path.root != symbol);
        if after.initializing_self == Some(symbol) {
            after.initializing_self = None;
        }

        let rest_body = self.lower_mir_statements(cursor.advance(), &after, k, cache);
        let Some(drop) = ctx
            .drop_stack
            .iter()
            .rev()
            .find(|drop| drop.symbol == symbol)
            .cloned()
        else {
            return rest_body;
        };
        let Some(value) = self.binding_value(ctx, symbol) else {
            return rest_body;
        };

        match self.storage_dead_drop_elaboration(ctx, cursor, symbol) {
            Some(mir::DropElaboration::Dead) => rest_body,
            Some(mir::DropElaboration::Conditional | mir::DropElaboration::Open) => self
                .lower_dynamic_assignment_drop_then(
                    ctx,
                    &drop.key_path,
                    value,
                    &drop.ty,
                    rest_body,
                ),
            Some(mir::DropElaboration::Static) | None => {
                self.lower_drop_value_then(ctx, value, &drop.ty, rest_body)
            }
        }
    }

    fn storage_dead_drop_elaboration(
        &self,
        ctx: &Ctx,
        cursor: MirCursor,
        symbol: Symbol,
    ) -> Option<mir::DropElaboration> {
        let body = cursor.body;
        let previous = cursor.index.checked_sub(1)?;
        let previous = cursor.statements().get(previous)?;
        let mir::Statement::DropCandidate {
            reason: reason @ (mir::DropReason::ScopeExit | mir::DropReason::EarlyExit),
            target:
                mir::DropTarget::Symbol {
                    symbol: target_symbol,
                    ..
                },
            key_path,
            elaboration,
        } = &previous.kind
        else {
            return None;
        };
        if *target_symbol != symbol {
            return None;
        }
        let key_path = key_path
            .as_ref()
            .and_then(|key_path| Self::ownership_key_path_from_mir(body, key_path))
            .unwrap_or_else(|| OwnershipKeyPath::root(symbol));
        elaboration
            .or_else(|| self.drop_elaboration_at(ctx, body, previous.point, *reason, &key_path))
    }

    fn moved_key_paths_at_statement(
        &self,
        ctx: &Ctx,
        body: &mir::Body<'_>,
        statement: &mir::LocatedStatement<'_>,
    ) -> Vec<OwnershipKeyPath> {
        let mut moved = Vec::new();
        for fact in &self.units[ctx.unit].ownership.facts.moves {
            if fact.point.point != statement.point.0 as u32 {
                continue;
            }
            if !self.ownership_point_matches_body(ctx, body, fact.point) {
                continue;
            }
            Self::push_unique_drop_flag_key(&mut moved, fact.source.clone());
        }
        moved
    }

    fn clear_moved_drop_flags_then(
        &mut self,
        ctx: &Ctx,
        body: &mir::Body<'_>,
        statement: &mir::LocatedStatement<'_>,
        next: ExprId,
    ) -> ExprId {
        let moved = self.moved_key_paths_at_statement(ctx, body, statement);
        let mut result = next;
        for key_path in moved.iter().rev() {
            result = self.set_drop_flags_under_then(ctx, key_path, false, result);
        }
        result
    }

    fn wrap_moved_value_cont(
        &mut self,
        ctx: &Ctx,
        body: &mir::Body<'_>,
        statement: &mir::LocatedStatement<'_>,
        target: ExprId,
    ) -> ExprId {
        if self
            .moved_key_paths_at_statement(ctx, body, statement)
            .is_empty()
        {
            return target;
        }
        let TyKind::Fn(value_ty, _) = *self.p.ty_kind(self.p.expr_ty(target)) else {
            self.diagnostics
                .push("lowering: moved-value target is not a function".into());
            return target;
        };
        let bot = self.p.ty_bot();
        let cont = self.p.func("after_move", value_ty, bot);
        let value = self.p.var(cont);
        let deliver = self.p.app(target, value);
        let body_expr = self.clear_moved_drop_flags_then(ctx, body, statement, deliver);
        self.p.set_body(cont, body_expr);
        self.p.func_ref(cont)
    }

    // lhs/rhs/target are the distinct pieces of the assignment; cursor/ctx/k/cache are the
    // walk state every statement lowerer threads.
    #[allow(clippy::too_many_arguments)]
    fn lower_mir_assignment(
        &mut self,
        lhs: &Expr,
        rhs: &Expr,
        target: Option<&mir::KeyPath>,
        cursor: MirCursor,
        ctx: &Ctx,
        k: ExprId,
        cache: &mut MirBlockCache,
    ) -> ExprId {
        let drop_elaboration = self.assignment_drop_elaboration(ctx, cursor);
        let lowered_target = self.assignment_target(lhs, ctx);
        let Some((cell, path)) = lowered_target else {
            return self.lower_mir_statements(cursor.advance(), ctx, k, cache);
        };
        let void_ty = self.p.ty_void();
        let bot = self.p.ty_bot();
        let after = self.p.func("after_set", void_ty, bot);
        let after_body = self.lower_mir_statements(cursor.advance(), ctx, k, cache);
        self.p.set_body(after, after_body);
        let after_ref = self.p.func_ref(after);
        let target_key_path = target
            .and_then(|target| Self::ownership_key_path_from_mir(cursor.body, target))
            .or_else(|| self.ownership_key_path_from_assignment_lhs(ctx, lhs));

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
            let void = self.p.void();
            let after_set = self.p.app(after_ref, void);
            let after_set = if let Some(target_key_path) = &target_key_path {
                self.set_drop_flags_under_then(ctx, target_key_path, true, after_set)
            } else {
                after_set
            };
            let after_set = self.sequence_void_effect(cell_set, after_set);
            let after_set =
                self.clear_moved_drop_flags_then(ctx, cursor.body, cursor.statement(), after_set);
            let lhs_check_ty = self.checker_ty(lhs, ctx);
            if matches!(drop_elaboration, Some(mir::DropElaboration::Static))
                && self.needs_drop_type(ctx.unit, &lhs_check_ty)
            {
                let old_ty = self.map_ty(&lhs_check_ty);
                let old = self.assignment_old_value(cell, &path, old_ty);
                self.lower_drop_value_then(ctx, old, &lhs_check_ty, after_set)
            } else if matches!(
                drop_elaboration,
                Some(mir::DropElaboration::Conditional | mir::DropElaboration::Open)
            ) && self.needs_drop_type(ctx.unit, &lhs_check_ty)
            {
                let Some(target_key_path) = &target_key_path else {
                    return self.dead_end("dynamic_assignment_drop_without_key_path");
                };
                let old_ty = self.map_ty(&lhs_check_ty);
                let old = self.assignment_old_value(cell, &path, old_ty);
                self.lower_dynamic_assignment_drop_then(
                    ctx,
                    target_key_path,
                    old,
                    &lhs_check_ty,
                    after_set,
                )
            } else {
                after_set
            }
        };
        self.p.set_body(setter, setter_body);
        let setter_ref = self.p.func_ref(setter);
        self.lower_expr(rhs, ctx, setter_ref)
    }

    fn lower_mir_discard(
        &mut self,
        expr: &Expr,
        cursor: MirCursor,
        ctx: &Ctx,
        k: ExprId,
        cache: &mut MirBlockCache,
    ) -> ExprId {
        if let Some(done) =
            self.try_mir_effect_split(expr, MirRestBinding::Discard, cursor, ctx, k, cache)
        {
            return done;
        }
        let (value_ty, pure_value) = match self.try_pure(expr, ctx) {
            Some(value) => (self.p.expr_ty(value), Some(value)),
            None => (self.expr_lambda_ty(expr, ctx), None),
        };
        let bot = self.p.ty_bot();
        let drop_k = self.p.func("drop", value_ty, bot);
        let rest_body = self.lower_mir_statements(cursor.advance(), ctx, k, cache);
        let rest_body =
            self.clear_moved_drop_flags_then(ctx, cursor.body, cursor.statement(), rest_body);
        self.p.set_body(drop_k, rest_body);
        let drop_ref = self.p.func_ref(drop_k);
        match pure_value {
            Some(value) => self.p.app(drop_ref, value),
            None => self.lower_expr(expr, ctx, drop_ref),
        }
    }

    // stmt/effect_name/handler_block are the distinct pieces of the @handle; cursor/ctx/k/cache
    // are the walk state every statement lowerer threads.
    #[allow(clippy::too_many_arguments)]
    fn lower_mir_handling(
        &mut self,
        stmt: &Stmt,
        effect_name: &crate::name::Name,
        handler_block: &Block,
        cursor: MirCursor,
        ctx: &Ctx,
        k: ExprId,
        cache: &mut MirBlockCache,
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
        inner.owner = None;
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
        self.lower_mir_statements(cursor.advance(), &scope_ctx, k, cache)
    }

    fn try_mir_effect_split(
        &mut self,
        expr: &Expr,
        binding: MirRestBinding,
        cursor: MirCursor,
        ctx: &Ctx,
        k: ExprId,
        cache: &mut MirBlockCache,
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
            let resume_ref =
                self.rest_mir_closure("after_perform", pair_ty, binding, cursor, ctx, cache);
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

        let rest_ref =
            self.rest_mir_closure("after_abortable", pair_ty, binding, cursor, ctx, cache);
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
        cursor: MirCursor,
        ctx: &Ctx,
        cache: &mut MirBlockCache,
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
                    .and_then(|ty| self.drop_binding_for_mir_symbol(ctx, cursor.body, symbol, ty));
                if mutated {
                    self.with_cells(&[(symbol, value)], &mut inner, |this, inner| {
                        let drops = drop_binding.clone().into_iter().collect::<Vec<_>>();
                        this.with_drop_flags(&drops, inner, |this, inner| {
                            inner.drop_stack.extend(drops.clone());
                            let rest_body = this.lower_mir_statements(
                                cursor.advance(),
                                inner,
                                inner.ret_k,
                                cache,
                            );
                            this.clear_moved_drop_flags_then(
                                inner,
                                cursor.body,
                                cursor.statement(),
                                rest_body,
                            )
                        })
                    })
                } else {
                    inner.env.insert(symbol, Binding::Value(value));
                    let drops = drop_binding.into_iter().collect::<Vec<_>>();
                    self.with_drop_flags(&drops, &mut inner, |this, inner| {
                        inner.drop_stack.extend(drops.clone());
                        let rest_body =
                            this.lower_mir_statements(cursor.advance(), inner, inner_k, cache);
                        this.clear_moved_drop_flags_then(
                            inner,
                            cursor.body,
                            cursor.statement(),
                            rest_body,
                        )
                    })
                }
            }
            MirRestBinding::Discard => {
                let rest_body = self.lower_mir_statements(cursor.advance(), &inner, inner_k, cache);
                self.clear_moved_drop_flags_then(&inner, cursor.body, cursor.statement(), rest_body)
            }
            MirRestBinding::Deliver => {
                let deliver = self.p.app(inner_k, value);
                self.clear_moved_drop_flags_then(&inner, cursor.body, cursor.statement(), deliver)
            }
        };
        self.p.set_body(rest_k, body_expr);
        self.p.func_ref(rest_k)
    }

    fn lower_mir_terminator(
        &mut self,
        cursor: MirCursor,
        ctx: &Ctx,
        k: ExprId,
        cache: &mut MirBlockCache,
    ) -> ExprId {
        match &cursor.body.blocks[cursor.block.0].terminator {
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
                if let Some(loop_) = cursor
                    .loops
                    .iter()
                    .rev()
                    .find(|loop_| loop_.header_block == *target)
                {
                    let void = self.p.void();
                    let jump = self.p.app(loop_.header, void);
                    let drops = self.loop_jump_drops(ctx, loop_.header);
                    return self.lower_drop_bindings_then(ctx, &drops, jump);
                }
                if let Some(loop_) = cursor
                    .loops
                    .iter()
                    .rev()
                    .find(|loop_| loop_.exit_block == *target)
                {
                    let void = self.p.void();
                    let jump = self.p.app(loop_.exit, void);
                    let drops = self.loop_jump_drops(ctx, loop_.exit);
                    return self.lower_drop_bindings_then(ctx, &drops, jump);
                }
                self.lower_mir_block(cursor.at_block(*target), ctx, k, cache)
            }
            mir::Terminator::Branch {
                condition,
                then_block,
                else_block,
            } => {
                let then_body = self.lower_mir_block(cursor.at_block(*then_block), ctx, k, cache);
                let else_body = self.lower_mir_block(cursor.at_block(*else_block), ctx, k, cache);
                self.branch(condition, then_body, else_body, ctx)
            }
            mir::Terminator::Switch {
                scrutinee,
                match_arms: Some(arms),
                arms: arm_blocks,
                default,
            } => {
                if let Some(join) = Self::switch_join_target(cursor.body, arm_blocks, *default) {
                    self.lower_mir_block(cursor.at_block(join), ctx, k, cache)
                } else {
                    self.lower_match(scrutinee, arms, ctx, k)
                }
            }
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
                let mut next_loops = cursor.loops.to_vec();
                next_loops.push(MirLoop {
                    header_block: cursor.block,
                    header: header_ref,
                    exit_block: *exit_block,
                    exit: exit_ref,
                });
                let exit_body = self.lower_mir_block(cursor.at_block(*exit_block), ctx, k, cache);
                self.p.set_body(exit, exit_body);

                let mut loop_ctx = ctx.clone();
                loop_ctx.loops.push(LoopBinding {
                    header: header_ref,
                    exit: exit_ref,
                    drop_depth: ctx.drop_stack.len(),
                });
                let body_expr = self.lower_mir_block(
                    cursor.at_block(*body_block).with_loops(&next_loops),
                    &loop_ctx,
                    header_ref,
                    cache,
                );
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

    fn switch_join_target(
        body: &mir::Body<'_>,
        arms: &[mir::BlockId],
        default: Option<mir::BlockId>,
    ) -> Option<mir::BlockId> {
        let mut join = None;
        for block in arms.iter().copied().chain(default) {
            let mir::Terminator::Jump(target) = body.blocks[block.0].terminator else {
                return None;
            };
            match join {
                Some(existing) if existing != target => return None,
                Some(_) => {}
                None => join = Some(target),
            }
        }
        join
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
