use super::*;

impl<'a> Lowering<'a> {
    // ----- Effects ------------------------------------------------------------

    /// A diagnosed, abandoned path: a call to a bodyless function. The
    /// scheduler emits the missing body as a `Trap`, the evaluator
    /// reports `UnsetBody` — honest if ever reached, and well-typed no
    /// matter what the abandoned expression's continuation expects
    /// (delivering `void` to an arbitrary continuation is ill-typed and
    /// trips the λ_G constructor's T-App check).
    pub(super) fn dead_end(&mut self, why: &str) -> ExprId {
        let void_ty = self.p.ty_void();
        let bot = self.p.ty_bot();
        let dead = self.p.func(why, void_ty, bot);
        let dead_ref = self.p.func_ref(dead);
        let void = self.p.void();
        self.p.app(dead_ref, void)
    }

    /// One unhandled perform: `'io(.sleep(ms))` and friends. The request
    /// must be a syntactic variant construction so the operation routes
    /// statically; its payloads become the primop's operands.
    pub(super) fn lower_perform(
        &mut self,
        expr: &Expr,
        effect_name: &crate::name::Name,
        args: &[hir::CallArg],
        ctx: &Ctx,
        k: ExprId,
    ) -> ExprId {
        let ret_ty = effect_name
            .symbol()
            .ok()
            .and_then(|symbol| {
                self.units
                    .iter()
                    .find_map(|u| u.types.catalog.effects.get(&symbol).cloned())
            })
            .map(|sig| self.map_ty(&sig.ret));
        let Some(ret_ty) = ret_ty else {
            self.diagnostics
                .push("lowering: perform of an undeclared effect".into());
            return self.dead_end("undeclared_effect");
        };

        // The request expression: a statically-known IORequest variant.
        // Payload-bearing variants parse as calls (`.read(...)`), while
        // payload-less variants parse as member values (`.cwd_len`).
        let operation = args.first().and_then(|request| match &request.value.kind {
            ExprKind::Con {
                enum_symbol,
                tag,
                args: payloads,
                ..
            } => {
                let name = self
                    .enum_info(*enum_symbol)?
                    .variants
                    .get_index(*tag as usize)
                    .map(|(name, _)| name.clone())?;
                Some((name, payloads.iter().collect::<Vec<&Expr>>()))
            }
            _ => None,
        });
        let Some((operation, payloads)) = operation else {
            self.diagnostics.push(
                "lowering: perform with a computed request (not yet supported — operations route statically)"
                    .into(),
            );
            return self.dead_end("computed_request");
        };

        let op = match operation.as_str() {
            "read" => Op::IoRead,
            "write" => Op::IoWrite,
            "open" => Op::IoOpen,
            "close" => Op::IoClose,
            "sleep" => Op::IoSleep,
            "poll" => Op::IoPoll,
            "ctl" => Op::IoCtl,
            "socket" => Op::IoSocket,
            "bind" => Op::IoBind,
            "listen" => Op::IoListen,
            "connect" => Op::IoConnect,
            "accept" => Op::IoAccept,
            "cwd_len" => Op::IoCwdLen,
            "cwd_copy" => Op::IoCwdCopy,
            "getenv_len" => Op::IoGetenvLen,
            "getenv_copy" => Op::IoGetenvCopy,
            "argc" => Op::IoArgc,
            "arg_len" => Op::IoArgLen,
            "arg_copy" => Op::IoArgCopy,
            "dir_count" => Op::IoDirCount,
            "dir_entry_kind" => Op::IoDirEntryKind,
            "dir_entry_len" => Op::IoDirEntryLen,
            "dir_entry_copy" => Op::IoDirEntryCopy,
            "exit" => Op::IoExit,
            other => {
                self.diagnostics
                    .push(format!("lowering: unknown io operation '{other}'"));
                return self.dead_end("unknown_io_operation");
            }
        };
        let _ = expr;
        self.lower_args(&payloads, ctx, vec![], &mut |this, values| {
            let result = this.p.primop(op, &values, ret_ty);
            this.p.app(k, result)
        })
    }

    // ----- Lexical effect handlers (M7: aborts) -----------------------------

    /// The result type carried by an abort-capable function's
    /// normal-return continuation (`Fn([result, slot], ⊥)` → result).
    pub(super) fn normal_result_ty(&mut self, normal_k: ExprId) -> TyId {
        let normal_k_ty = self.p.expr_ty(normal_k);
        if let TyKind::Fn(pair_ty, _) = *self.p.ty_kind(normal_k_ty)
            && let TyKind::Tuple(items) = self.p.ty_kind(pair_ty)
            && items.len() == 2
        {
            return items[0];
        }
        self.diagnostics
            .push("lowering: abort-capable function without a paired normal return".into());
        self.p.ty_void()
    }

    /// Clone a context for code that moves into an escaping closure: `rk`,
    /// the closure's own return slot, replaces the function's return
    /// linkage, and normal completions are re-pointed at it — directly, or
    /// through the enclosing abort-capable function's normal-return
    /// parameter (which the closure captures as an ordinary value).
    pub(super) fn rebase_into_closure(&mut self, ctx: &Ctx, rk: ExprId) -> Ctx {
        let mut inner = ctx.clone();
        inner.loops = vec![];
        inner.raw_ret_k = rk;
        inner.ret_k = match ctx.normal_k {
            None => rk,
            Some(normal_k) => {
                let result_ty = self.normal_result_ty(normal_k);
                let bot = self.p.ty_bot();
                let wrap = self.p.func("ret_normal", result_ty, bot);
                let value = self.p.var(wrap);
                let pair = self.p.tuple(&[value, rk]);
                let body = self.p.app(normal_k, pair);
                self.p.set_body(wrap, body);
                self.p.func_ref(wrap)
            }
        };
        inner.tail_k = inner.ret_k;
        inner
    }

    /// A perform routed to a lexical handler: call the capability with
    /// the payloads and our own return slot. The handler's value rides
    /// the Ret chain back through every frame between here and the
    /// handled scope's caller; nothing after the perform is emitted on
    /// this path (the effect returns Never).
    pub(super) fn lower_routed_perform(
        &mut self,
        handler_sym: Symbol,
        args: &[hir::CallArg],
        ctx: &Ctx,
        k: ExprId,
    ) -> ExprId {
        if !ctx.abort_ok && !ctx.local_handlers.contains(&handler_sym) {
            self.diagnostics
                .push("lowering: perform inside a function value (not yet supported)".into());
            let _ = k;
            return self.dead_end("perform_in_function_value");
        }
        let Some(cap) = self.handler_caps.get(&handler_sym).copied() else {
            self.diagnostics.push(
                "lowering: perform reached before its handler was installed (not yet supported)"
                    .into(),
            );
            return self.dead_end("perform_before_handler");
        };
        // Resumable performs are handled by the MIR statement-spine
        // splitter, where the rest of the block can become the
        // resumption; reaching one here means it sits in an expression
        // position the split cannot reach yet.
        if cap.resume_pair_ty.is_some() {
            self.diagnostics.push(
                "lowering: a resumable perform in expression position (not yet supported)".into(),
            );
            return self.dead_end("resumable_perform_in_expression");
        }
        let slot = ctx.raw_ret_k;
        let arg_exprs: Vec<&Expr> = args.iter().map(|a| &a.value).collect();
        self.lower_args(&arg_exprs, ctx, vec![], &mut |this, mut values| {
            values.push(slot);
            let tuple = this.p.tuple(&values);
            this.p.app(cap.cap, tuple)
        })
    }

    /// Is this expression a direct call to an abort-capable function?
    pub(super) fn abortable_callee(&self, expr: &Expr, ctx: &Ctx) -> Option<Symbol> {
        let ExprKind::Call { callee, .. } = &expr.kind else {
            return None;
        };
        let ExprKind::Variable(name) = &callee.kind else {
            return None;
        };
        let symbol = name.symbol().ok()?;
        if ctx.env.contains_key(&symbol) {
            return None;
        }
        self.abort_shape(symbol).then_some(symbol)
    }
}
