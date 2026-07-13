use super::*;
use crate::lower::mir;

struct PendingDrop {
    symbol: Symbol,
    key_path: Place,
    ty: CheckTy,
    has_dynamic_flags: bool,
    elaboration: Option<mir::DropElaboration>,
    /// Carried from the matched `DropBinding`: the deinit body's own
    /// `self`, whose drop is a no-op (the caller's glue owns teardown).
    is_deinit_self: bool,
}

/// What a `TemporaryEnd` candidate's elaboration means to lowering.
#[derive(Debug, PartialEq)]
pub(super) enum TempDropDisposition {
    /// `Static`: an unconsumed owned temp — release it here.
    Drop,
    /// `Dead` (consumed) or unelaborated (nothing droppable) — emit nothing.
    Skip,
    /// `Open` with a moved path: a consuming projection took one field
    /// path out of the temp — drop every field OFF that path here.
    DropExcept(Vec<crate::name_resolution::symbol::Symbol>),
    /// `Conditional` (or `Open` without a moved path): not a
    /// classification flow can produce for a temp (consumption is static
    /// per temp, so temps never need drop flags). An internal error — R6:
    /// silence here would be a silent leak the day flow's temp contract
    /// changes.
    Invalid(mir::DropElaboration),
}

#[derive(derive_visitor::Visitor)]
#[visitor(Expr(enter))]
struct TempCollector {
    temps: Vec<u32>,
}

impl TempCollector {
    fn enter_expr(&mut self, expr: &Expr) {
        if let ExprKind::Temp(temp) = expr.kind
            && !self.temps.contains(&temp)
        {
            self.temps.push(temp);
        }
    }
}

/// The position of a MIR→λ_G walk: the statement currently under the cursor
/// (`body.blocks[block].statements[index]`) plus the loops in scope. Threaded by
/// value through the statement lowerers so they share one positional argument
/// instead of `(body, block, index, statements, loops)`. The mutable block cache
/// and the per-continuation `ctx`/`k` stay as separate arguments.
#[derive(Clone, Copy)]
struct MirCursor<'b> {
    body: &'b mir::Body,
    block: mir::BlockId,
    index: usize,
    loops: &'b [MirLoop],
    /// The λ_G entry function for `block` when this cursor is lowering that
    /// block's own body. Loop back-edges target it so condition-evaluation
    /// statements run on every iteration.
    entry: Option<ExprId>,
    /// When lowering a scaffold arm with a value continuation: a jump to
    /// this block (the construct's join) delivers void to `k` instead of
    /// walking on — the join's statements belong to the enclosing walk.
    deliver_at: Option<mir::BlockId>,
}

impl<'b> MirCursor<'b> {
    fn statements(self) -> &'b [mir::LocatedStatement] {
        &self.body.blocks[self.block.0].statements
    }

    fn statement(self) -> &'b mir::LocatedStatement {
        &self.statements()[self.index]
    }

    /// The next statement in the same block.
    fn advance(self) -> Self {
        MirCursor {
            index: self.index + 1,
            ..self
        }
    }

    fn with_entry(self, entry: ExprId) -> Self {
        MirCursor {
            entry: Some(entry),
            ..self
        }
    }

    /// The start of another block, keeping the same loops in scope.
    fn at_block(self, block: mir::BlockId) -> Self {
        MirCursor {
            block,
            index: 0,
            entry: None,
            ..self
        }
    }

    fn with_loops(self, loops: &'b [MirLoop]) -> Self {
        MirCursor { loops, ..self }
    }
}

impl<'a> Lowering<'a> {
    pub(super) fn lower_mir_body(
        &mut self,
        body: &std::sync::Arc<mir::Body>,
        ctx: &Ctx,
        k: ExprId,
    ) -> ExprId {
        let mut cache = MirBlockCache::default();
        let cursor = MirCursor {
            body,
            block: body.entry,
            index: 0,
            loops: &[],
            entry: None,
            deliver_at: None,
        };
        // Expression lowering needs this body (and the loops in scope) to
        // lower expression-position constructs from their scaffold blocks.
        self.scaffold_ctx.push(ScaffoldCtx {
            body: std::sync::Arc::clone(body),
            loops: vec![],
        });
        let done = self.lower_mir_statements(cursor, ctx, k, &mut cache);
        self.scaffold_ctx.pop();
        done
    }

    /// The scaffold arm blocks of an expression-position match in the body
    /// being lowered, for the pattern compiler's arm bodies.
    pub(super) fn match_scaffold_arms(&self, expr: &Expr) -> Option<ScaffoldArms> {
        let scaffold = self.scaffold_ctx.last()?;
        let &switch_block = scaffold.body.scaffolds.get(&expr.id)?;
        let mir::Terminator::Switch { arms, default, .. } =
            &scaffold.body.blocks[switch_block.0].terminator
        else {
            return None;
        };
        let cursor = MirCursor {
            body: &scaffold.body,
            block: switch_block,
            index: 0,
            loops: &scaffold.loops,
            entry: None,
            deliver_at: None,
        };
        let join = Self::switch_join_target(cursor, arms, *default);
        Some(ScaffoldArms {
            blocks: arms.clone(),
            join,
        })
    }

    /// Lower a callee-invoked sub-body (a handler body, keyed by its
    /// handling statement's id, or a trailing block, keyed by the block's
    /// own id) from its scaffold blocks — the `Handler` terminator's
    /// `body_block` — delivering the body's tail value to `k` (the
    /// closure's return continuation); `continue v` statements lower as
    /// resume applications via `ctx.resume_k`. `None` means the checked MIR
    /// body did not publish the required scaffold.
    pub(super) fn lower_sub_body_from_scaffold(
        &mut self,
        key: crate::node_id::NodeID,
        ctx: &Ctx,
        k: ExprId,
    ) -> Option<ExprId> {
        let scaffold = self.scaffold_ctx.last()?;
        let &handling_block = scaffold.body.scaffolds.get(&key)?;
        let mir::Terminator::Handler { body_block, join } =
            scaffold.body.blocks[handling_block.0].terminator
        else {
            return None;
        };
        let body = std::sync::Arc::clone(&scaffold.body);
        let cursor = MirCursor {
            body: &body,
            block: body_block,
            index: 0,
            // The capability is its own function: enclosing loops are not
            // jump targets from inside it (matching the tree path's
            // closure rebase).
            loops: &[],
            entry: None,
            deliver_at: Some(join),
        };
        let mut cache = MirBlockCache::default();
        Some(self.lower_mir_statements(cursor, ctx, k, &mut cache))
    }

    /// Lower one scaffold arm block with the match's value continuation:
    /// the arm's tail delivers to `k`; jumps to the join deliver void;
    /// breaks/continues/returns are real edges.
    pub(super) fn lower_arm_from_scaffold(
        &mut self,
        arm_block: mir::BlockId,
        join: Option<mir::BlockId>,
        ctx: &Ctx,
        k: ExprId,
    ) -> Option<ExprId> {
        let scaffold = self.scaffold_ctx.last()?;
        let body = std::sync::Arc::clone(&scaffold.body);
        let loops = scaffold.loops.clone();
        let cursor = MirCursor {
            body: &body,
            block: arm_block,
            index: 0,
            loops: &loops,
            entry: None,
            deliver_at: join,
        };
        let mut cache = MirBlockCache::default();
        Some(self.lower_mir_statements(cursor, ctx, k, &mut cache))
    }

    fn temp_bindings_for_block(
        &self,
        body: &mir::Body,
        block: mir::BlockId,
        ctx: &Ctx,
    ) -> Vec<(u32, ExprId)> {
        let mut collector = TempCollector { temps: vec![] };
        for statement in &body.blocks[block.0].statements {
            self.collect_statement_temps(&statement.kind, &mut collector);
        }
        self.collect_terminator_temps(&body.blocks[block.0].terminator, &mut collector);
        collector.temps.sort_unstable();
        collector
            .temps
            .into_iter()
            .filter_map(|temp| ctx.temps.get(&temp).copied().map(|value| (temp, value)))
            .collect()
    }

    fn collect_statement_temps(&self, statement: &mir::Statement, collector: &mut TempCollector) {
        use derive_visitor::Drive;
        match statement {
            mir::Statement::ConsumeValue { expr }
            | mir::Statement::ReturnValue { expr, .. }
            | mir::Statement::ContinueValue { expr }
            | mir::Statement::Perform { expr, .. } => expr.drive(collector),
            mir::Statement::Bind { rhs: Some(rhs), .. } => rhs.drive(collector),
            mir::Statement::Assign { lhs, rhs, .. } => {
                lhs.drive(collector);
                rhs.drive(collector);
            }
            mir::Statement::DropCandidate {
                target: mir::DropTarget::Expr(expr),
                ..
            } => expr.drive(collector),
            mir::Statement::Call {
                expr, callee, args, ..
            } => {
                expr.drive(collector);
                callee.drive(collector);
                for arg in args {
                    arg.value.drive(collector);
                }
            }
            _ => {}
        }
    }

    fn collect_terminator_temps(
        &self,
        terminator: &mir::Terminator,
        collector: &mut TempCollector,
    ) {
        use derive_visitor::Drive;
        match terminator {
            mir::Terminator::Branch { condition, .. } => condition.drive(collector),
            mir::Terminator::Switch { scrutinee, .. } => scrutinee.drive(collector),
            mir::Terminator::Loop {
                condition: Some(condition),
                ..
            } => condition.drive(collector),
            _ => {}
        }
    }

    fn block_key(&self, cursor: MirCursor, ctx: &Ctx, k: ExprId) -> MirBlockKey {
        MirBlockKey {
            block: cursor.block,
            k,
            ctx: ctx.mir_key(),
            loops: cursor.loops.to_vec(),
            temps: self.temp_bindings_for_block(cursor.body, cursor.block, ctx),
        }
    }

    fn lower_mir_block(
        &mut self,
        cursor: MirCursor,
        ctx: &Ctx,
        k: ExprId,
        cache: &mut MirBlockCache,
    ) -> ExprId {
        let key = self.block_key(cursor, ctx, k);
        if let Some(&entry) = cache.blocks.get(&key) {
            let void = self.p.void();
            return self.p.app(entry, void);
        }

        let void_ty = self.p.ty_void();
        let bot = self.p.ty_bot();
        let label_name = if matches!(
            cursor.body.blocks[cursor.block.0].terminator,
            mir::Terminator::Loop { .. }
        ) {
            "loop_head"
        } else {
            "mir_bb"
        };
        let label = self.p.func(label_name, void_ty, bot);
        let entry = self.p.func_ref(label);
        cache.blocks.insert(key, entry);
        let body_expr = self.lower_mir_statements(cursor.with_entry(entry), ctx, k, cache);
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
        // Block entry: pre-bind this block's named func-valued binders to
        // their labels (the value-level mirror of the resolver's
        // fn-in-block hoisting), so local funcs can call themselves and
        // each other regardless of declaration order.
        let hoisted;
        let ctx = match (cursor.index == 0)
            .then(|| self.hoist_block_funcs(cursor, ctx))
            .flatten()
        {
            Some(with_funcs) => {
                hoisted = with_funcs;
                &hoisted
            }
            None => ctx,
        };
        // Skip contiguous runs of non-lowering statements ITERATIVELY:
        // flow-only bookkeeping (reads, scope markers) and symbol drop
        // candidates (read by their neighboring statements via cursor
        // lookaround, never lowered by the walk itself) would otherwise
        // each cost a recursion frame — with ADR 0027's per-suspension
        // `Unwind` candidates that depth overflowed the test stack.
        let mut cursor = cursor;
        loop {
            let Some(statement) = cursor.statements().get(cursor.index) else {
                return self.lower_mir_terminator(cursor, ctx, k, cache);
            };
            let skippable = match &statement.kind {
                mir::Statement::ScopeEnter { .. }
                | mir::Statement::ScopeExit { .. }
                | mir::Statement::StorageLive { .. }
                | mir::Statement::Read { .. }
                | mir::Statement::AssignmentRootUse { .. }
                | mir::Statement::DeclBody { .. } => true,
                // Only an Expr-targeted TemporaryEnd candidate lowers at
                // its own statement; every symbol-targeted candidate is
                // consumed by its neighbors' lookaround.
                mir::Statement::DropCandidate { reason, target, .. } => {
                    !(matches!(reason, mir::DropReason::TemporaryEnd)
                        && matches!(target, mir::DropTarget::Expr(_)))
                }
                _ => false,
            };
            if !skippable {
                break;
            }
            cursor = cursor.advance();
        }
        let statement = cursor.statement();
        let mut rest = |this: &mut Self, ctx: &Ctx, k: ExprId| {
            this.lower_mir_statements(cursor.advance(), ctx, k, cache)
        };
        match &statement.kind {
            mir::Statement::ScopeEnter { .. }
            | mir::Statement::ScopeExit { .. }
            | mir::Statement::StorageLive { .. }
            | mir::Statement::Read { .. }
            | mir::Statement::AssignmentRootUse { .. } => rest(self, ctx, k),
            // An unconsumed owned temporary releases at its full
            // expression's end; `Dead` (consumed) and unelaborated
            // (scalar) temps emit nothing. Symbol-rooted candidates are
            // read by their neighboring StorageDead/Assign/exit handling.
            mir::Statement::DropCandidate {
                reason: mir::DropReason::TemporaryEnd,
                target: mir::DropTarget::Expr(temp_expr),
                ..
            } => {
                let rest_body = rest(self, ctx, k);
                let moved_path =
                    match Self::temp_drop_disposition(statement.ownership.drop.as_ref()) {
                        TempDropDisposition::Skip => return rest_body,
                        TempDropDisposition::Invalid(kind) => {
                            // Flow classifies temps `Static`, `Dead`, or `Open`
                            // with a moved path (consumption is static per temp
                            // — no drop flags). Anything else means a stage
                            // upstream changed the contract; skipping it
                            // silently would be a silent leak, so it surfaces
                            // loudly instead.
                            debug_assert!(
                                false,
                                "TemporaryEnd candidate elaborated {kind:?}: flow \
                             classifies temps Static, Dead, or pathed Open only"
                            );
                            self.diagnostics.push(format!(
                                "lowering: temporary drop candidate elaborated {kind:?} \
                             (internal error: temps classify Static, Dead, or \
                             pathed Open only)"
                            ));
                            return rest_body;
                        }
                        TempDropDisposition::Drop => vec![],
                        TempDropDisposition::DropExcept(path) => path,
                    };
                let typed_ast::ExprKind::Temp(temp) = temp_expr.kind else {
                    return rest_body;
                };
                let Some(value) = ctx.temps.get(&temp).copied() else {
                    return rest_body;
                };
                if moved_path.is_empty() {
                    self.lower_drop_value_then(ctx, value, &temp_expr.ty, rest_body)
                } else {
                    self.lower_drop_value_except_then(
                        ctx,
                        value,
                        &temp_expr.ty,
                        &moved_path,
                        rest_body,
                    )
                }
            }
            mir::Statement::DropCandidate { .. } => rest(self, ctx, k),
            mir::Statement::StorageDead { symbol, .. } => {
                self.lower_mir_storage_dead(*symbol, cursor, ctx, k, cache)
            }
            mir::Statement::Function { .. } => {
                let rest_body = rest(self, ctx, k);
                self.clear_moved_drop_flags_then(ctx, statement, rest_body)
            }
            mir::Statement::Perform {
                expr,
                temp,
                result_ty,
            } => {
                // The perform evaluates HERE (a resumable one's temp
                // continuation IS its resumption). A Never-returning
                // perform aborts: the rest is unreachable.
                let result_ty = result_ty.clone().substitute(
                    &ctx.theta,
                    &Default::default(),
                    &Default::default(),
                );
                let result_ty = self.normalize_check_ty(result_ty, ctx.unit);
                if result_ty.is_never() {
                    return self.with_unwind_entry(ctx, cursor, cache, |this| {
                        this.lower_expr_unpacked(expr, ctx, k)
                    });
                }
                let value_ty = self.map_ty(&result_ty);
                let bot = self.p.ty_bot();
                let kf = self.p.func("perform_temp", value_ty, bot);
                let param = self.p.var(kf);
                let mut tctx = ctx.clone();
                tctx.temps.insert(*temp, param);
                let rest_body = self.lower_mir_statements(cursor.advance(), &tctx, k, cache);
                self.p.set_body(kf, rest_body);
                let kref = self.p.func_ref(kf);
                self.with_unwind_entry(ctx, cursor, cache, |this| {
                    this.lower_expr_unpacked(expr, ctx, kref)
                })
            }
            mir::Statement::Call {
                expr,
                temp,
                result_ty,
                ..
            } => {
                // The call evaluates HERE; its value binds the temp the
                // consuming statement reads. A callee's abort never
                // resumes this continuation — nothing to split.
                let result_ty = result_ty.clone().substitute(
                    &ctx.theta,
                    &Default::default(),
                    &Default::default(),
                );
                let result_ty = self.normalize_check_ty(result_ty, ctx.unit);
                let value_ty = self.map_ty(&result_ty);
                let bot = self.p.ty_bot();
                let kf = self.p.func("call_temp", value_ty, bot);
                let param = self.p.var(kf);
                let mut tctx = ctx.clone();
                tctx.temps.insert(*temp, param);
                let rest_body = self.lower_mir_statements(cursor.advance(), &tctx, k, cache);
                let rest_body = self.clear_moved_drop_flags_then(&tctx, statement, rest_body);
                self.p.set_body(kf, rest_body);
                let kref = self.p.func_ref(kf);
                // Raw evaluation: the pack / auto-clone the checker put on
                // this node applies where its Temp is read (the consuming
                // statement), exactly as for match temps — not twice.
                self.with_unwind_entry(ctx, cursor, cache, |this| {
                    this.lower_expr_unpacked(expr, ctx, kref)
                })
            }
            mir::Statement::Handling {
                stmt,
                effect_name,
                body: handler_body,
            } => self.lower_mir_handling(stmt, effect_name, handler_body, cursor, ctx, k, cache),
            mir::Statement::DeclBody { .. } => rest(self, ctx, k),
            mir::Statement::Bind { lhs, rhs, .. } => {
                self.lower_mir_bind(lhs, rhs.as_ref(), cursor, ctx, k, cache)
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
                if let mir::ValueDestination::TempThenContinue(temp) = destination {
                    return self.lower_mir_temp_delivery(expr, *temp, cursor, ctx, k, cache);
                }
                let target = match destination {
                    mir::ValueDestination::Continuation(_)
                    | mir::ValueDestination::Fallthrough
                    | mir::ValueDestination::TailReturn => {
                        self.wrap_cont_with_following_drops(ctx, cursor, k)
                    }
                    mir::ValueDestination::Return => {
                        self.wrap_cont_with_following_drops(ctx, cursor, ctx.ret_k)
                    }
                    mir::ValueDestination::TempThenContinue(_) => unreachable!(),
                };
                // Ledger rule E: a delivered place read tops up +1 BEFORE
                // the exit releases run (the receiving binding claims it as
                // an rvalue result). The initializing self is exempt — the
                // constructor's fresh +1 rides through to the caller.
                let returns_initializing_self = ctx
                    .initializing_self
                    .is_some_and(|self_symbol| Self::expr_root_symbol(expr) == Some(self_symbol));
                let target = if !self.rhs_is_rvalue(expr, ctx)
                    && !returns_initializing_self
                    && self.contains_object_type(&self.checker_ty(expr, ctx))
                {
                    self.acquire_before(target, expr, ctx)
                } else {
                    target
                };
                let mut tail_ctx;
                let value_ctx = if target != ctx.tail_k {
                    tail_ctx = ctx.clone();
                    tail_ctx.tail_k = target;
                    &tail_ctx
                } else {
                    ctx
                };
                let target = self.wrap_moved_value_cont(value_ctx, statement, target);
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
                let mut resume_body = self.p.app(resume_k, value);
                // Only the handler-scope suffix dies here: the MIR builder
                // emitted EarlyExit candidates from the handler's scope
                // depth. Enclosing-function locals stay live across the
                // resume (they drop at their own scope's exit).
                for drop in self.following_drop_candidates(ctx, cursor).iter().rev() {
                    resume_body = self.lower_candidate_drop_then(ctx, drop, resume_body);
                }
                let resume_body = self.clear_moved_drop_flags_then(ctx, statement, resume_body);
                self.p.set_body(send, resume_body);
                let send_ref = self.p.func_ref(send);
                self.lower_expr(expr, ctx, send_ref)
            }
            mir::Statement::ContinueValue { .. } => {
                // The checker lets a trailing block keep the handler
                // context, but the resume continuation does not cross the
                // closure boundary: without one, discarding the value would
                // silently break the perform site.
                self.diagnostics
                    .push("lowering: continue with a value outside an effect handler".into());
                self.dead_end("resume_outside_handler")
            }
        }
    }

    /// Bindings for every named func-valued `let` in this basic block:
    /// each binder resolves to its (pre-minted) label's value before any
    /// statement lowers. `None` when the block declares no local funcs.
    /// Celled binders are skipped — a mutated func binding stays
    /// late-bound through its cell.
    fn hoist_block_funcs(&mut self, cursor: MirCursor, ctx: &Ctx) -> Option<Ctx> {
        let mut hoisted: Option<Ctx> = None;
        for located in cursor.statements() {
            let mir::Statement::Bind {
                lhs,
                rhs: Some(rhs),
                ..
            } = &located.kind
            else {
                continue;
            };
            let typed_ast::ExprKind::Func(func) = &rhs.kind else {
                continue;
            };
            let typed_ast::PatternKind::Bind(name) = &lhs.kind else {
                continue;
            };
            let Ok(symbol) = name.symbol() else {
                continue;
            };
            if !matches!(symbol, Symbol::DeclaredLocal(..)) || ctx.cellable.contains(&symbol) {
                continue;
            }
            let Some(label) = self.func_literal_label(func, rhs, ctx) else {
                continue;
            };
            let func_ref = self.p.func_ref(label);
            hoisted
                .get_or_insert_with(|| ctx.clone())
                .env
                .insert(symbol, Binding::Value(func_ref));
        }
        hoisted
    }

    fn lower_mir_bind(
        &mut self,
        lhs: &typed_ast::Pattern,
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
            let mut acquires: Vec<ExprId> = vec![];
            for (symbol, value) in binds {
                if inner.cellable.contains(&symbol) {
                    celled.push((symbol, value));
                } else {
                    inner.env.insert(symbol, Binding::Value(value));
                }
                let binder_ty = self.units[ctx.unit]
                    .types
                    .local_tys
                    .get(&symbol)
                    .cloned()
                    .map(|raw| {
                        let substituted =
                            raw.substitute(&ctx.theta, &Default::default(), &Default::default());
                        self.normalize_check_ty(substituted, ctx.unit)
                    })
                    .or_else(|| self.symbol_check_ty(symbol, &ctx.theta));
                if let Some(ty) = binder_ty {
                    // Ledger: destructured binders own their components —
                    // each acquires (the rvalue rhs's carried +1s release
                    // below; a place-read rhs keeps its own).
                    if self.contains_object_type(&ty) {
                        let void_ty = self.p.ty_void();
                        acquires.push(self.p.primop(Op::RegionAcquire, &[value], void_ty));
                    }
                    if let Some(drop) =
                        self.drop_binding_for_mir_symbol(cursor.body, cache, symbol, ty)
                    {
                        drop_bindings.push(drop);
                    }
                }
            }
            let rhs_release = (self.rhs_is_rvalue(rhs, ctx)
                && self.contains_object_type(&binding_ty))
            .then(|| {
                let void_ty = self.p.ty_void();
                self.p.primop(Op::RegionRelease, &[bound], void_ty)
            });
            let rest_body = self.with_cells(&celled, &mut inner, |this, inner| {
                this.with_drop_flags(&drop_bindings, inner, |this, inner| {
                    inner.drop_stack.extend(drop_bindings.clone());
                    let rest_body = this.lower_mir_statements(cursor.advance(), inner, k, cache);
                    this.clear_moved_drop_flags_then(inner, cursor.statement(), rest_body)
                })
            });
            let mut rest_body = rest_body;
            if let Some(release) = rhs_release {
                rest_body = self.sequence_void_effect(release, rest_body);
            }
            for acquire in acquires.into_iter().rev() {
                rest_body = self.sequence_void_effect(acquire, rest_body);
            }
            self.p.set_body(bind, rest_body);
            let bind_ref = self.p.func_ref(bind);
            return self.lower_expr(rhs, ctx, bind_ref);
        };
        let Ok(symbol) = name.symbol() else {
            return self.lower_mir_statements(cursor.advance(), ctx, k, cache);
        };

        // A named local func binds directly to its label's value, with no
        // `let_…` continuation: funcs referencing it (mutual recursion)
        // then see the stable func_ref instead of a binder var that would
        // nest them under this let and cycle the nesting relation
        // (Property 2). Nothing droppable is skipped — a func value
        // carries no owned buffers.
        if let typed_ast::ExprKind::Func(func) = &rhs.kind
            && matches!(symbol, Symbol::DeclaredLocal(..))
            && !ctx.cellable.contains(&symbol)
            && !self.contains_object_type(&self.checker_ty(rhs, ctx))
            && let Some(value) = self.lower_func_value(rhs, func, ctx)
        {
            let mut inner = ctx.clone();
            inner.env.insert(symbol, Binding::Value(value));
            return self.lower_mir_statements(cursor.advance(), &inner, k, cache);
        }

        let mutated = ctx.cellable.contains(&symbol);
        let value_ty = self.expr_lambda_ty(rhs, ctx);
        let bot = self.p.ty_bot();
        let bind = self
            .p
            .func(&format!("let_{}", name.name_str()), value_ty, bot);
        let bound = self.p.var(bind);
        let binding_ty = self
            .symbol_check_ty(symbol, &ctx.theta)
            .unwrap_or_else(|| self.checker_ty(rhs, ctx));
        let drop_binding = self
            .drop_binding_for_mir_symbol(cursor.body, cache, symbol, binding_ty.clone())
            .map(|mut drop| {
                // `let s = self` inside a deinit body: the rebind inherits
                // the self param's drop suppression (transitively — the
                // stack entry it reads may itself be an inherited rebind).
                drop.is_deinit_self = Self::moves_deinit_self(ctx, rhs);
                drop
            });
        let mut inner = ctx.clone();
        // Ledger: a binding initialized from a place read takes references
        // into the value's regions (rvalues already carry their +1).
        let acquire = (!self.rhs_is_rvalue(rhs, ctx) && self.contains_object_type(&binding_ty))
            .then(|| {
                let void_ty = self.p.ty_void();
                self.p.primop(Op::RegionAcquire, &[bound], void_ty)
            });
        let rest_body = if mutated {
            self.with_cells(&[(symbol, bound)], &mut inner, |this, inner| {
                let drops = drop_binding.clone().into_iter().collect::<Vec<_>>();
                this.with_drop_flags(&drops, inner, |this, inner| {
                    inner.drop_stack.extend(drops.clone());
                    let rest_body = this.lower_mir_statements(cursor.advance(), inner, k, cache);
                    this.clear_moved_drop_flags_then(inner, cursor.statement(), rest_body)
                })
            })
        } else {
            inner.env.insert(symbol, Binding::Value(bound));
            let drops = drop_binding.into_iter().collect::<Vec<_>>();
            self.with_drop_flags(&drops, &mut inner, |this, inner| {
                inner.drop_stack.extend(drops.clone());
                let rest_body = this.lower_mir_statements(cursor.advance(), inner, k, cache);
                this.clear_moved_drop_flags_then(inner, cursor.statement(), rest_body)
            })
        };
        let rest_body = match acquire {
            Some(acquire) => self.sequence_void_effect(acquire, rest_body),
            None => rest_body,
        };
        self.p.set_body(bind, rest_body);
        let bind_ref = self.p.func_ref(bind);
        self.lower_expr(rhs, ctx, bind_ref)
    }

    fn drop_binding_for_mir_symbol(
        &self,
        body: &mir::Body,
        cache: &mut MirBlockCache,
        symbol: Symbol,
        ty: CheckTy,
    ) -> Option<DropBinding> {
        if !self.needs_release_type(&ty) {
            return None;
        }
        let facts = cache.symbol_facts(body);
        let dynamic_flags = facts.drop_flag_keys(symbol);
        // A statically-moved local usually needs no binding — but a local
        // that is LIVE at some suspension site before its move must stay
        // resolvable for that site's unwind entry (ADR 0027): flow's
        // per-point elaborations keep every normal-path drop `Dead`.
        if dynamic_flags.is_empty() && facts.has_move(symbol) && !facts.has_live_unwind(symbol) {
            return None;
        }
        Some(DropBinding {
            symbol,
            key_path: Place::root(symbol),
            ty,
            dynamic_flags,
            is_deinit_self: false,
        })
    }

    fn lower_mir_temp_delivery(
        &mut self,
        expr: &Expr,
        temp: u32,
        cursor: MirCursor,
        ctx: &Ctx,
        k: ExprId,
        cache: &mut MirBlockCache,
    ) -> ExprId {
        let value_ty = self.expr_lambda_ty(expr, ctx);
        let bot = self.p.ty_bot();
        let cont = self.p.func("block_temp", value_ty, bot);
        let value = self.p.var(cont);
        let mut tctx = ctx.clone();
        tctx.temps.insert(temp, value);
        let rest_body = self.lower_mir_statements(cursor.advance(), &tctx, k, cache);
        self.p.set_body(cont, rest_body);
        let target = self.p.func_ref(cont);

        let returns_initializing_self = ctx
            .initializing_self
            .is_some_and(|self_symbol| Self::expr_root_symbol(expr) == Some(self_symbol));
        let target = if !self.rhs_is_rvalue(expr, ctx)
            && !returns_initializing_self
            && self.contains_object_type(&self.checker_ty(expr, ctx))
        {
            self.acquire_before(target, expr, ctx)
        } else {
            target
        };
        let mut tail_ctx;
        let value_ctx = if target != ctx.tail_k {
            tail_ctx = ctx.clone();
            tail_ctx.tail_k = target;
            &tail_ctx
        } else {
            ctx
        };
        let target = self.wrap_moved_value_cont(value_ctx, cursor.statement(), target);
        self.lower_expr(expr, value_ctx, target)
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

    /// The `Unwind` candidates flow published immediately after this
    /// Call/Perform statement (ADR 0027), resolved against the live drop
    /// stack. Emission order (innermost scope first, reverse declaration
    /// order) is the order the entry's drops run.
    fn unwind_drop_candidates(&self, ctx: &Ctx, cursor: MirCursor) -> Vec<PendingDrop> {
        self.drop_candidates_following(
            ctx,
            cursor,
            |reason| matches!(reason, mir::DropReason::Unwind),
            false,
        )
    }

    /// Build this suspension site's unwind entry (ADR 0027): a
    /// `λ((), ⊥)` whose body is the site's scope-exit drops (the same
    /// `lower_candidate_drop_then` machinery normal drops use — deinit
    /// hooks, structural teardown, `RegionRelease`, drop-flag guards),
    /// terminated by `Op::UnwindDone`. `None` when nothing owned is live
    /// across the site (hash-consing makes "the body is just UnwindDone"
    /// an exact test).
    fn unwind_entry_for(
        &mut self,
        ctx: &Ctx,
        cursor: MirCursor,
        cache: &mut MirBlockCache,
    ) -> Option<ExprId> {
        let drops = self.unwind_drop_candidates(ctx, cursor);
        if drops.is_empty() {
            return None;
        }
        let bot = self.p.ty_bot();
        let done = self.p.primop(Op::UnwindDone, &[], bot);
        let mut body = done;
        for drop in drops.iter().rev() {
            body = self.lower_candidate_drop_then(ctx, drop, body);
        }
        if body == done {
            return None;
        }
        // Suspension sites with the same live drop set lower to the same
        // (hash-consed) chain: share one entry per body walk instead of
        // minting a fresh identical λ per site.
        if let Some(&entry) = cache.unwind_entries.get(&body) {
            return Some(entry);
        }
        let void_ty = self.p.ty_void();
        let entry = self.p.func("unwind_entry", void_ty, bot);
        self.p.set_body(entry, body);
        let entry_ref = self.p.func_ref(entry);
        cache.unwind_entries.insert(body, entry_ref);
        Some(entry_ref)
    }

    /// Install this suspension site's unwind entry (ADR 0027) around one
    /// expression lowering, restoring the enclosing statement's entry
    /// afterwards (so nested bodies cannot steal it).
    fn with_unwind_entry(
        &mut self,
        ctx: &Ctx,
        cursor: MirCursor,
        cache: &mut MirBlockCache,
        lower: impl FnOnce(&mut Self) -> ExprId,
    ) -> ExprId {
        let saved_unwind = self.pending_unwind.take();
        self.pending_unwind = self.unwind_entry_for(ctx, cursor, cache);
        let done = lower(self);
        self.pending_unwind = saved_unwind;
        done
    }

    fn following_drop_candidates(&self, ctx: &Ctx, cursor: MirCursor) -> Vec<PendingDrop> {
        self.drop_candidates_following(
            ctx,
            cursor,
            |reason| {
                matches!(
                    reason,
                    mir::DropReason::ScopeExit | mir::DropReason::EarlyExit
                )
            },
            true,
        )
    }

    /// The run of matching `DropCandidate` statements immediately after the
    /// cursor, resolved against the live drop stack. `skip_bookkeeping`
    /// lets the run continue across `StorageDead`/`ScopeExit` statements;
    /// any other statement ends it. Candidates whose reason does not match
    /// end the run too — they belong to a different consumer.
    fn drop_candidates_following(
        &self,
        ctx: &Ctx,
        cursor: MirCursor,
        reason_matches: impl Fn(&mir::DropReason) -> bool,
        skip_bookkeeping: bool,
    ) -> Vec<PendingDrop> {
        let mut drops = Vec::new();
        for statement in cursor.statements().iter().skip(cursor.index + 1) {
            match &statement.kind {
                mir::Statement::DropCandidate {
                    reason,
                    target:
                        mir::DropTarget::Symbol {
                            symbol: target_symbol,
                            ..
                        },
                    ..
                } if reason_matches(reason) => {
                    if let Some(drop) = self.pending_drop_at(ctx, statement, *target_symbol) {
                        drops.push(drop);
                    }
                }
                mir::Statement::StorageDead { .. } | mir::Statement::ScopeExit { .. }
                    if skip_bookkeeping => {}
                _ => break,
            }
        }
        drops
    }

    /// Resolve one ScopeExit/EarlyExit `DropCandidate` statement against the
    /// live drop stack, reading the flow-annotated elaboration off it.
    fn pending_drop_at(
        &self,
        ctx: &Ctx,
        statement: &mir::LocatedStatement,
        target_symbol: Symbol,
    ) -> Option<PendingDrop> {
        let mir::Statement::DropCandidate { key_path, .. } = &statement.kind else {
            return None;
        };
        let drop = ctx
            .drop_stack
            .iter()
            .rev()
            .find(|drop| drop.symbol == target_symbol)?;
        let key_path = key_path.clone().unwrap_or_else(|| drop.key_path.clone());
        let elaboration = self.drop_elaboration_at(statement, Some(&key_path));
        Some(PendingDrop {
            symbol: drop.symbol,
            key_path,
            ty: drop.ty.clone(),
            has_dynamic_flags: !drop.dynamic_flags.is_empty(),
            elaboration,
            is_deinit_self: drop.is_deinit_self,
        })
    }

    /// The trailing ScopeExit candidates a `Terminator::Return` block leaves
    /// unclaimed: a Void-ish tail (a body ending in a branch join) has no
    /// `ReturnValue` statement to run `wrap_cont_with_following_drops`, so
    /// owned PARAMETERS would silently leak (locals pair with a following
    /// `StorageDead`, which claims their candidate — those are skipped).
    fn unclaimed_scope_exit_drops(&self, ctx: &Ctx, cursor: MirCursor) -> Vec<PendingDrop> {
        let statements = cursor.statements();
        // The trailing run of scope-exit bookkeeping before the terminator.
        let mut start = statements.len();
        while start > 0 {
            match &statements[start - 1].kind {
                mir::Statement::DropCandidate {
                    reason: mir::DropReason::ScopeExit | mir::DropReason::EarlyExit,
                    target: mir::DropTarget::Symbol { .. },
                    ..
                }
                | mir::Statement::StorageDead { .. }
                | mir::Statement::ScopeExit { .. } => start -= 1,
                _ => break,
            }
        }
        let mut drops = Vec::new();
        for (index, statement) in statements.iter().enumerate().skip(start) {
            let mir::Statement::DropCandidate {
                reason: mir::DropReason::ScopeExit | mir::DropReason::EarlyExit,
                target:
                    mir::DropTarget::Symbol {
                        symbol: target_symbol,
                        ..
                    },
                ..
            } = &statement.kind
            else {
                continue;
            };
            // Claimed: an immediately-following StorageDead for the same
            // symbol drops it at its own statement (`lower_mir_storage_dead`
            // looks back exactly one statement).
            if let Some(mir::Statement::StorageDead { symbol, .. }) =
                statements.get(index + 1).map(|next| &next.kind)
                && symbol == target_symbol
            {
                continue;
            }
            let Some(drop) = self.pending_drop_at(ctx, statement, *target_symbol) else {
                continue;
            };
            drops.push(drop);
        }
        drops
    }

    /// Classify a `TemporaryEnd` candidate's annotated elaboration
    /// (`lower_mir_statements` acts on the result; unit-tested directly —
    /// no flow state can produce the `Invalid` inputs today).
    pub(super) fn temp_drop_disposition(
        elaboration: Option<&mir::DropElaborationResult>,
    ) -> TempDropDisposition {
        let Some(drop) = elaboration else {
            return TempDropDisposition::Skip;
        };
        match drop.kind {
            mir::DropElaboration::Static => TempDropDisposition::Drop,
            mir::DropElaboration::Dead => TempDropDisposition::Skip,
            mir::DropElaboration::Open if !drop.moved_path.is_empty() => {
                TempDropDisposition::DropExcept(drop.moved_path.clone())
            }
            kind @ (mir::DropElaboration::Conditional | mir::DropElaboration::Open) => {
                TempDropDisposition::Invalid(kind)
            }
        }
    }

    /// The drop elaboration the ownership pass annotated onto this `DropCandidate`
    /// statement (matching `key_path` when given). Lowering reads it straight off the
    /// statement; `following_drop_candidates`, `storage_dead_drop_elaboration`, and
    /// `assignment_drop_elaboration` all resolve through here.
    fn drop_elaboration_at(
        &self,
        statement: &mir::LocatedStatement,
        key_path: Option<&Place>,
    ) -> Option<mir::DropElaboration> {
        let drop = statement.ownership.drop.as_ref()?;
        key_path
            .is_none_or(|key_path| drop.key_path.as_ref() == Some(key_path))
            .then_some(drop.kind)
    }

    fn lower_candidate_drop_then(&mut self, ctx: &Ctx, drop: &PendingDrop, next: ExprId) -> ExprId {
        // The deinit body's own `self` elaborates to a NO-OP: the caller's
        // glue dispatches the hook and tears the fields down — the body
        // owns no teardown (Swift's deinitialization model).
        if drop.is_deinit_self {
            return next;
        }
        let Some(value) = self.binding_value(ctx, drop.symbol) else {
            return next;
        };
        match drop.elaboration {
            Some(mir::DropElaboration::Dead) => next,
            Some(mir::DropElaboration::Conditional | mir::DropElaboration::Open) => {
                self.lower_dynamic_assignment_drop_then(ctx, &drop.key_path, value, &drop.ty, next)
            }
            Some(mir::DropElaboration::Static) if drop.has_dynamic_flags => {
                self.lower_dynamic_assignment_drop_then(ctx, &drop.key_path, value, &drop.ty, next)
            }
            Some(mir::DropElaboration::Static) => {
                self.lower_drop_value_then(ctx, value, &drop.ty, next)
            }
            // Every candidate that reaches here passed lowering's
            // needs-release gate on the concrete type, and flow classifies
            // every such candidate — including generic ones (each
            // specialization elides per θ). A missing elaboration is a
            // missing annotation, not a license to guess: guessing "drop"
            // here is how a flow gap becomes a double free. Surface it
            // loudly and emit nothing (leak-safe), matching the
            // `TemporaryEnd` disposition's treatment of contract breaks.
            None => {
                debug_assert!(
                    false,
                    "drop candidate for {:?} reached lowering unelaborated",
                    drop.symbol
                );
                self.diagnostics.push(format!(
                    "lowering: drop candidate for {:?} has no flow elaboration \
                     (internal error: flow classifies every needs-release candidate)",
                    drop.symbol
                ));
                next
            }
        }
    }

    fn push_unique_drop_flag_key(keys: &mut Vec<Place>, key: Place) {
        if !keys.iter().any(|existing| existing == &key) {
            keys.push(key);
        }
    }

    fn assignment_drop_elaboration(&self, cursor: MirCursor) -> Option<mir::DropElaboration> {
        let previous = cursor.index.checked_sub(1)?;
        let previous = cursor.statements().get(previous)?;
        let mir::Statement::DropCandidate {
            reason: mir::DropReason::AssignmentReplace,
            ..
        } = &previous.kind
        else {
            return None;
        };
        self.drop_elaboration_at(previous, None)
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
        if drop.is_deinit_self {
            return rest_body;
        }
        let Some(value) = self.binding_value(ctx, symbol) else {
            return rest_body;
        };

        match self.storage_dead_drop_elaboration(cursor, symbol) {
            Some(mir::DropElaboration::Dead) => rest_body,
            Some(mir::DropElaboration::Conditional | mir::DropElaboration::Open) => self
                .lower_dynamic_assignment_drop_then(
                    ctx,
                    &drop.key_path,
                    value,
                    &drop.ty,
                    rest_body,
                ),
            Some(mir::DropElaboration::Static) => {
                self.lower_drop_value_then(ctx, value, &drop.ty, rest_body)
            }
            // The builder pairs every needs-release local's `StorageDead`
            // with an immediately-preceding `DropCandidate`, and flow
            // classifies every such candidate. Reaching here means the
            // pairing broke or the annotation is missing — dropping on a
            // guess is the double-free direction, so surface it and emit
            // nothing (leak-safe).
            None => {
                debug_assert!(
                    false,
                    "StorageDead for {symbol:?} has no elaborated drop candidate"
                );
                self.diagnostics.push(format!(
                    "lowering: StorageDead for {symbol:?} has no elaborated drop \
                     candidate (internal error: scope exits pair candidates with \
                     storage teardown)"
                ));
                rest_body
            }
        }
    }

    fn storage_dead_drop_elaboration(
        &self,
        cursor: MirCursor,
        symbol: Symbol,
    ) -> Option<mir::DropElaboration> {
        let previous = cursor.index.checked_sub(1)?;
        let previous = cursor.statements().get(previous)?;
        let mir::Statement::DropCandidate {
            reason: mir::DropReason::ScopeExit | mir::DropReason::EarlyExit,
            target:
                mir::DropTarget::Symbol {
                    symbol: target_symbol,
                    ..
                },
            key_path,
            ..
        } = &previous.kind
        else {
            return None;
        };
        if *target_symbol != symbol {
            return None;
        }
        let key_path = key_path.clone().unwrap_or_else(|| Place::root(symbol));
        self.drop_elaboration_at(previous, Some(&key_path))
    }

    fn moved_key_paths_at_statement(&self, statement: &mir::LocatedStatement) -> Vec<Place> {
        let mut moved = Vec::new();
        for source in &statement.ownership.moves {
            Self::push_unique_drop_flag_key(&mut moved, source.clone());
        }
        moved
    }

    fn clear_moved_drop_flags_then(
        &mut self,
        ctx: &Ctx,
        statement: &mir::LocatedStatement,
        next: ExprId,
    ) -> ExprId {
        let moved = self.moved_key_paths_at_statement(statement);
        let mut result = next;
        for key_path in moved.iter().rev() {
            result = self.set_drop_flags_under_then(ctx, key_path, false, result);
        }
        result
    }

    fn wrap_moved_value_cont(
        &mut self,
        ctx: &Ctx,
        statement: &mir::LocatedStatement,
        target: ExprId,
    ) -> ExprId {
        if self.moved_key_paths_at_statement(statement).is_empty() {
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
        let body_expr = self.clear_moved_drop_flags_then(ctx, statement, deliver);
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
        target: Option<&Place>,
        cursor: MirCursor,
        ctx: &Ctx,
        k: ExprId,
        cache: &mut MirBlockCache,
    ) -> ExprId {
        let drop_elaboration = self.assignment_drop_elaboration(cursor);
        let lowered_target = self.assignment_target(lhs, ctx);
        let Some((base, path)) = lowered_target else {
            return self.lower_mir_statements(cursor.advance(), ctx, k, cache);
        };
        if let crate::lower::statements::AssignBase::Object(handle) = base {
            return self.lower_object_assignment(
                lhs,
                rhs,
                target,
                handle,
                &path,
                drop_elaboration,
                cursor,
                ctx,
                k,
                cache,
            );
        }
        let crate::lower::statements::AssignBase::Cell(cell) = base else {
            unreachable!("object base handled above")
        };
        let void_ty = self.p.ty_void();
        let bot = self.p.ty_bot();
        let after = self.p.func("after_set", void_ty, bot);
        let after_body = self.lower_mir_statements(cursor.advance(), ctx, k, cache);
        self.p.set_body(after, after_body);
        let after_ref = self.p.func_ref(after);
        let target_key_path = target.cloned().or_else(|| crate::flow::place_for_expr(lhs));

        let rhs_ty = self.expr_lambda_ty(rhs, ctx);
        let setter = self.p.func("set", rhs_ty, bot);
        let value = self.p.var(setter);
        // Ledger rule B: a place-read rhs embedding `'heap` handles gains
        // +1 for the (re)assigned binding's value (the replaced old value's
        // release rides the AssignmentReplace schedule).
        let acquire = (!self.rhs_is_rvalue(rhs, ctx)
            && self.contains_object_type(&self.checker_ty(rhs, ctx)))
        .then(|| self.p.primop(Op::RegionAcquire, &[value], void_ty));
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
            let after_set = match acquire {
                Some(acquire) => self.sequence_void_effect(acquire, after_set),
                None => after_set,
            };
            let after_set = self.clear_moved_drop_flags_then(ctx, cursor.statement(), after_set);
            let lhs_check_ty = self.checker_ty(lhs, ctx);
            if matches!(drop_elaboration, Some(mir::DropElaboration::Static))
                && self.needs_release_type(&lhs_check_ty)
            {
                let old_ty = self.map_ty(&lhs_check_ty);
                let old = self.assignment_old_value(cell, &path, old_ty);
                self.lower_drop_value_then(ctx, old, &lhs_check_ty, after_set)
            } else if matches!(
                drop_elaboration,
                Some(mir::DropElaboration::Conditional | mir::DropElaboration::Open)
            ) && self.needs_release_type(&lhs_check_ty)
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

    /// Assignment whose nearest-to-leaf receiver is a `'heap` handle:
    /// in-place ObjectSet, no write-back above, old value released/dropped
    /// per the flow checker's elaboration.
    #[allow(clippy::too_many_arguments)]
    fn lower_object_assignment(
        &mut self,
        lhs: &Expr,
        rhs: &Expr,
        target: Option<&Place>,
        handle: ExprId,
        path: &[(u32, TyId)],
        drop_elaboration: Option<mir::DropElaboration>,
        cursor: MirCursor,
        ctx: &Ctx,
        k: ExprId,
        cache: &mut MirBlockCache,
    ) -> ExprId {
        let void_ty = self.p.ty_void();
        let bot = self.p.ty_bot();
        let after = self.p.func("after_object_set", void_ty, bot);
        let after_body = self.lower_mir_statements(cursor.advance(), ctx, k, cache);
        self.p.set_body(after, after_body);
        let after_ref = self.p.func_ref(after);
        let target_key_path = target.cloned().or_else(|| crate::flow::place_for_expr(lhs));

        let rhs_ty = self.expr_lambda_ty(rhs, ctx);
        let setter = self.p.func("object_set", rhs_ty, bot);
        let value = self.p.var(setter);
        let write = self.object_assignment_write(handle, path, value);
        let setter_body = {
            let void = self.p.void();
            let after_set = self.p.app(after_ref, void);
            let after_set = if let Some(target_key_path) = &target_key_path {
                self.set_drop_flags_under_then(ctx, target_key_path, true, after_set)
            } else {
                after_set
            };
            // Ledger: an rvalue rhs carried +1 per embedded handle; once
            // stored, the region owns them (place-read rhs carried none).
            let after_set = if self.rhs_is_rvalue(rhs, ctx)
                && self.contains_object_type(&self.checker_ty(rhs, ctx))
            {
                let release = self.p.primop(Op::RegionRelease, &[value], void_ty);
                self.sequence_void_effect(release, after_set)
            } else {
                after_set
            };
            let after_set = self.sequence_void_effect(write, after_set);
            let after_set = self.clear_moved_drop_flags_then(ctx, cursor.statement(), after_set);
            let lhs_check_ty = self.checker_ty(lhs, ctx);
            if matches!(drop_elaboration, Some(mir::DropElaboration::Static))
                && self.needs_release_type(&lhs_check_ty)
            {
                let old_ty = self.map_ty(&lhs_check_ty);
                let old = self.object_assignment_old_value(handle, path, old_ty);
                self.lower_drop_value_then(ctx, old, &lhs_check_ty, after_set)
            } else if matches!(
                drop_elaboration,
                Some(mir::DropElaboration::Conditional | mir::DropElaboration::Open)
            ) && self.needs_release_type(&lhs_check_ty)
            {
                let Some(target_key_path) = &target_key_path else {
                    return self.dead_end("dynamic_object_assignment_drop_without_key_path");
                };
                let old_ty = self.map_ty(&lhs_check_ty);
                let old = self.object_assignment_old_value(handle, path, old_ty);
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

    /// The root variable of a place-read chain, if any.
    fn expr_root_symbol(expr: &Expr) -> Option<Symbol> {
        match &expr.kind {
            ExprKind::Variable(name) => name.symbol().ok(),
            ExprKind::Member(Some(receiver), _) => Self::expr_root_symbol(receiver),
            _ => None,
        }
    }

    /// Wrap a value continuation so the value's regions acquire before it
    /// runs (rule E — the drops inside `target` must see the +1).
    fn acquire_before(&mut self, target: ExprId, expr: &Expr, ctx: &Ctx) -> ExprId {
        let value_ty = self.expr_lambda_ty(expr, ctx);
        let bot = self.p.ty_bot();
        let cont = self.p.func("acquire_result", value_ty, bot);
        let value = self.p.var(cont);
        let void_ty = self.p.ty_void();
        let acquire = self.p.primop(Op::RegionAcquire, &[value], void_ty);
        let deliver = self.p.app(target, value);
        let body = self.sequence_void_effect(acquire, deliver);
        self.p.set_body(cont, body);
        self.p.func_ref(cont)
    }

    fn lower_mir_discard(
        &mut self,
        expr: &Expr,
        cursor: MirCursor,
        ctx: &Ctx,
        k: ExprId,
        cache: &mut MirBlockCache,
    ) -> ExprId {
        let (value_ty, pure_value) = match self.try_pure(expr, ctx) {
            Some(value) => (self.p.expr_ty(value), Some(value)),
            None => (self.expr_lambda_ty(expr, ctx), None),
        };
        let bot = self.p.ty_bot();
        let drop_k = self.p.func("drop", value_ty, bot);
        let rest_body = self.lower_mir_statements(cursor.advance(), ctx, k, cache);
        let rest_body = self.clear_moved_drop_flags_then(ctx, cursor.statement(), rest_body);
        // Flow CONSUMED the discarded value (mir ConsumeValue): the
        // discard owns its teardown. Type-directed and no-op for
        // Copy/borrowed values; discarded `'heap` rvalues release their
        // region here (the constructor's +1 belonged to the binding that
        // never came).
        let delivered = self.p.var(drop_k);
        let drop_body = self.lower_drop_value_then(ctx, delivered, &expr.ty, rest_body);
        self.p.set_body(drop_k, drop_body);
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
        let Some(effect) = effect_name.symbol().ok() else {
            return self.dead_end("unresolved_effect_name");
        };
        if self
            .units
            .iter()
            .find_map(|u| u.types.catalog.effects.get(&effect))
            .is_none()
        {
            self.diagnostics
                .push("lowering: @handle of an undeclared effect".into());
            return self.dead_end("undeclared_effect");
        };
        // Register a capability TEMPLATE for the rest of the extent: the
        // closure materializes lazily, once per instantiation demanded
        // inside it, specializing the handler body with the effect's
        // generics bound (docs/generic-effects-plan.md). The template
        // captures this frame's context — the delimiter (`raw_ret_k`) the
        // materialized capability closes over.
        let scaffold = self
            .scaffold_ctx
            .last()
            .map(|scaffold| std::sync::Arc::clone(&scaffold.body));
        let Some(scaffold) = scaffold else {
            self.diagnostics
                .push("lowering: @handle outside a MIR body (lowerer bug)".into());
            return self.dead_end("handler_without_scaffold");
        };
        let index = self.handler_templates.len();
        self.handler_templates.push(HandlerTemplate {
            effect,
            handling_id: stmt.id,
            scaffold,
            handler_args: handler_block.args.clone(),
            install_ctx: ctx.clone(),
        });
        let mut scope_ctx = ctx.clone();
        scope_ctx.cap_templates.insert(effect, index);
        let rest = self.lower_mir_statements(cursor.advance(), &scope_ctx, k, cache);
        // ADR 0027: mark the install for the evaluator's extent stack (a
        // delimiter marker, popped when the delimiter is applied). The VM
        // scheduler compiles this to nothing.
        let void_ty = self.p.ty_void();
        let install = self.p.primop(Op::HandleInstall, &[ctx.raw_ret_k], void_ty);
        self.sequence_void_effect(install, rest)
    }

    fn lower_mir_terminator(
        &mut self,
        cursor: MirCursor,
        ctx: &Ctx,
        k: ExprId,
        cache: &mut MirBlockCache,
    ) -> ExprId {
        let body = self.lower_mir_terminator_inner(cursor, ctx, k, cache);
        let moves = cursor.body.blocks[cursor.block.0]
            .terminator_ownership
            .moves
            .clone();
        let mut result = body;
        for key_path in moves.iter().rev() {
            result = self.set_drop_flags_under_then(ctx, key_path, false, result);
        }
        result
    }

    fn lower_mir_terminator_inner(
        &mut self,
        cursor: MirCursor,
        ctx: &Ctx,
        k: ExprId,
        cache: &mut MirBlockCache,
    ) -> ExprId {
        match &cursor.body.blocks[cursor.block.0].terminator {
            mir::Terminator::Unset => {
                let void = self.p.void();
                self.p.app(k, void)
            }
            // A Void-ish tail (a body ending in a branch join) reaches
            // `Return` with its ScopeExit candidates unclaimed — there is
            // no `ReturnValue` statement to run
            // `wrap_cont_with_following_drops` — so the unclaimed trailing
            // candidates (owned PARAMETERS; locals pair with StorageDead)
            // drain here. Requires the rule-B buffer retain on place-read
            // `'heap`-constructor arguments: without it this drain
            // double-freed core `Dict.insert`'s consume params. The deinit
            // body's own `self` stays a no-op via
            // `DropBinding::is_deinit_self`.
            mir::Terminator::Return => {
                let void = self.p.void();
                let mut body = self.p.app(k, void);
                for drop in self.unclaimed_scope_exit_drops(ctx, cursor).iter().rev() {
                    body = self.lower_candidate_drop_then(ctx, drop, body);
                }
                body
            }
            mir::Terminator::ReturnVoid => {
                let void = self.p.void();
                let body = self.p.app(ctx.ret_k, void);
                self.lower_early_exit_then(ctx, cursor, body)
            }
            mir::Terminator::Break => self.lower_mir_break(cursor, ctx, k),
            mir::Terminator::Continue => self.lower_mir_continue(cursor, ctx, k),
            // The handler body's blocks are scaffolding — the capability
            // closure lowered them from the `Handling` statement; the walk
            // continues at the join.
            mir::Terminator::Handler { join, .. } => {
                self.lower_mir_block(cursor.at_block(*join), ctx, k, cache)
            }
            mir::Terminator::Jump(target) => {
                if cursor.deliver_at == Some(*target) {
                    let void = self.p.void();
                    return self.p.app(k, void);
                }
                if let Some(loop_) =
                    cursor.loops.iter().rev().find(|loop_| {
                        loop_.continue_block == *target || loop_.exit_block == *target
                    })
                {
                    let jump_to = if loop_.continue_block == *target {
                        loop_.header
                    } else {
                        loop_.exit
                    };
                    let void = self.p.void();
                    let jump = self.p.app(jump_to, void);
                    return self.lower_early_exit_then(ctx, cursor, jump);
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
                join,
                result,
                ..
            } => {
                // The arms are real blocks: compile the decision tree with
                // a value-carrying join continuation — arm tails deliver
                // the match's value, the join binds it as the temp the
                // consuming statement (in the join block) reads.
                let join = Some(*join);
                let k_arm = match (join, result) {
                    (Some(join_block), Some((temp, result_ty))) => {
                        // The stored type is the checker's raw (possibly
                        // generic) type: θ-substitute per instantiation.
                        let result_ty = result_ty.clone().substitute(
                            &ctx.theta,
                            &Default::default(),
                            &Default::default(),
                        );
                        let result_ty = self.normalize_check_ty(result_ty, ctx.unit);
                        let value_ty = self.map_ty(&result_ty);
                        let bot = self.p.ty_bot();
                        let jf = self.p.func("match_join", value_ty, bot);
                        let param = self.p.var(jf);
                        let mut jctx = ctx.clone();
                        jctx.temps.insert(*temp, param);
                        let body =
                            self.lower_mir_block(cursor.at_block(join_block), &jctx, k, cache);
                        self.p.set_body(jf, body);
                        self.p.func_ref(jf)
                    }
                    _ => k,
                };
                let scaffold_arms = ScaffoldArms {
                    blocks: arm_blocks.clone(),
                    join,
                };
                self.lower_match(scrutinee, arms, Some(scaffold_arms), ctx, k_arm)
            }
            mir::Terminator::Switch { .. } => self.dead_end("mir_switch_without_patterns"),
            mir::Terminator::Loop {
                condition,
                header_block,
                body_block,
                exit_block,
            } => {
                let header_ref = if *header_block == cursor.block {
                    cursor.entry
                } else {
                    let mut header_ctx = ctx.clone();
                    header_ctx.temps.clear();
                    let key = self.block_key(cursor.at_block(*header_block), &header_ctx, k);
                    cache.blocks.get(&key).copied()
                };
                let Some(header_ref) = header_ref else {
                    return self.dead_end("loop_header_without_block_entry");
                };
                let void_ty = self.p.ty_void();
                let bot = self.p.ty_bot();
                let exit = self.p.func("loop_exit", void_ty, bot);
                let exit_ref = self.p.func_ref(exit);
                let mut next_loops = cursor.loops.to_vec();
                next_loops.push(MirLoop {
                    continue_block: *header_block,
                    header: header_ref,
                    exit_block: *exit_block,
                    exit: exit_ref,
                });
                // An unconditional loop with no break never reaches its
                // exit block; lowering it anyway would deliver () to a
                // continuation expecting the function's value.
                let exit_body =
                    if condition.is_some() || Self::loop_exit_reachable(cursor.body, *exit_block) {
                        self.lower_mir_block(cursor.at_block(*exit_block), ctx, k, cache)
                    } else {
                        self.dead_end("loop_exit_unreachable")
                    };
                self.p.set_body(exit, exit_body);

                let mut loop_ctx = ctx.clone();
                loop_ctx.loops.push(LoopBinding {
                    header: header_ref,
                    exit: exit_ref,
                });
                // Mirror the loops-in-scope for expression lowering's
                // scaffold paths (breaks inside expression-position arms
                // resolve against them), restoring the parent's view after.
                if let Some(scaffold) = self.scaffold_ctx.last_mut() {
                    scaffold.loops = next_loops.clone();
                }
                let body_expr = self.lower_mir_block(
                    cursor.at_block(*body_block).with_loops(&next_loops),
                    &loop_ctx,
                    header_ref,
                    cache,
                );
                if let Some(scaffold) = self.scaffold_ctx.last_mut() {
                    scaffold.loops = cursor.loops.to_vec();
                }
                match condition {
                    Some(condition) => {
                        let void = self.p.void();
                        let exit_jump = self.p.app(exit_ref, void);
                        self.branch(condition, body_expr, exit_jump, ctx)
                    }
                    None => body_expr,
                }
            }
        }
    }

    /// Whether any terminator in the body transfers control INTO `exit`.
    /// The defining `Loop { exit_block }` field is not an inbound edge —
    /// an unconditional loop reaches its exit only through breaks (which
    /// are `Jump`s here). Bare `Break`s (scaffold paths that resolve
    /// against `ctx.loops` later) count conservatively.
    fn loop_exit_reachable(body: &mir::Body, exit: mir::BlockId) -> bool {
        body.blocks.iter().any(|block| match block.terminator {
            mir::Terminator::Jump(target) => target == exit,
            mir::Terminator::Break => true,
            mir::Terminator::Branch {
                then_block,
                else_block,
                ..
            } => then_block == exit || else_block == exit,
            mir::Terminator::Switch {
                ref arms,
                default,
                join,
                ..
            } => arms.contains(&exit) || default == Some(exit) || join == exit,
            mir::Terminator::Handler { body_block, join } => body_block == exit || join == exit,
            mir::Terminator::Loop {
                ref condition,
                body_block,
                exit_block,
                ..
            } => body_block == exit || (condition.is_some() && exit_block == exit),
            mir::Terminator::Unset
            | mir::Terminator::Return
            | mir::Terminator::ReturnVoid
            | mir::Terminator::Continue => false,
        })
    }

    fn switch_join_target(
        cursor: MirCursor,
        arms: &[mir::BlockId],
        default: Option<mir::BlockId>,
    ) -> Option<mir::BlockId> {
        let mut join = None;
        for block in arms.iter().copied().chain(default) {
            // Only arms that jump to the match's own join vote; a diverging
            // arm — return/break/continue, including a jump straight to an
            // enclosing loop's edge — never reaches it, and skipping the
            // join because of one would silently drop the match's binding
            // and every statement after it.
            let mir::Terminator::Jump(target) = cursor.body.blocks[block.0].terminator else {
                continue;
            };
            if cursor
                .loops
                .iter()
                .any(|loop_| loop_.continue_block == target || loop_.exit_block == target)
            {
                continue;
            }
            match join {
                Some(existing) if existing != target => return None,
                Some(_) => {}
                None => join = Some(target),
            }
        }
        join
    }

    fn lower_mir_break(&mut self, cursor: MirCursor, ctx: &Ctx, k: ExprId) -> ExprId {
        match ctx.loops.last() {
            Some(loop_binding) => {
                let void = self.p.void();
                let body = self.p.app(loop_binding.exit, void);
                self.lower_early_exit_then(ctx, cursor, body)
            }
            None => {
                self.diagnostics.push("lowering: break outside loop".into());
                let void = self.p.void();
                self.p.app(k, void)
            }
        }
    }

    /// The early-exit drop candidates ending this block (emitted just
    /// before its terminator), as pending drops matched against the drop
    /// stack for values and types.
    fn trailing_early_exit_drops(&self, ctx: &Ctx, cursor: MirCursor) -> Vec<PendingDrop> {
        let statements = cursor.statements();
        let mut start = statements.len();
        while start > 0 {
            match &statements[start - 1].kind {
                mir::Statement::DropCandidate {
                    reason: mir::DropReason::EarlyExit,
                    ..
                } => start -= 1,
                _ => break,
            }
        }
        statements[start..]
            .iter()
            .filter_map(|statement| {
                let mir::Statement::DropCandidate {
                    target: mir::DropTarget::Symbol { symbol, .. },
                    ..
                } = &statement.kind
                else {
                    return None;
                };
                self.pending_drop_at(ctx, statement, *symbol)
            })
            .collect()
    }

    /// Early-exit drops before `body` runs: the block's trailing `EarlyExit`
    /// candidates are the single drop authority (ADR 0010 stage 3) — flow
    /// classified each at its program point, and the drop stack only
    /// resolves a candidate's value-level metadata (type, drop flags,
    /// deinit-self). Lowering compensates for nothing here.
    fn lower_early_exit_then(&mut self, ctx: &Ctx, cursor: MirCursor, body: ExprId) -> ExprId {
        let mut body = body;
        for drop in self.trailing_early_exit_drops(ctx, cursor).iter().rev() {
            body = self.lower_candidate_drop_then(ctx, drop, body);
        }
        body
    }

    fn lower_mir_continue(&mut self, cursor: MirCursor, ctx: &Ctx, k: ExprId) -> ExprId {
        match ctx.loops.last() {
            Some(loop_binding) => {
                let void = self.p.void();
                let body = self.p.app(loop_binding.header, void);
                self.lower_early_exit_then(ctx, cursor, body)
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
