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

    /// One unhandled perform: `'io(.sleep(ms))` and friends. Only the core
    /// effects reach here (the runtime is their implicit handler); a user
    /// effect without a capability in scope beat its handler's install
    /// order. The request must be a syntactic variant construction so the
    /// operation routes statically; its payloads become the primop's
    /// operands.
    pub(super) fn lower_perform(
        &mut self,
        expr: &Expr,
        effect_name: &crate::name::Name,
        args: &[hir::CallArg],
        ctx: &Ctx,
        k: ExprId,
    ) -> ExprId {
        let effect = effect_name.symbol().ok();
        if let Some(effect) = effect
            && effect.external_module_id() != Some(crate::compiling::module::ModuleId::Core)
        {
            self.diagnostics.push(format!(
                "lowering: perform of '{effect} before its handler is installed"
            ));
            return self.dead_end("perform_before_handler");
        }
        let ret_ty = effect
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

    // ----- Lexical effect handlers ------------------------------------------

    /// Clone a context for code that moves into an escaping closure: `rk`,
    /// the closure's own return linkage, replaces the function's.
    pub(super) fn rebase_into_closure(&mut self, ctx: &Ctx, rk: ExprId) -> Ctx {
        let mut inner = ctx.clone();
        inner.loops = vec![];
        inner.raw_ret_k = rk;
        inner.ret_k = rk;
        inner.tail_k = rk;
        inner
    }

    /// The dead resumption a Never-effect perform passes: the capability's
    /// calling convention still wants a final continuation, but the
    /// handler can never invoke it (the checker rejects `continue` for a
    /// Never effect). Bodyless, so reaching it is an honest trap.
    fn dead_resume_k(&mut self, resume_value_ty: TyId) -> ExprId {
        let bot = self.p.ty_bot();
        let dead = self.p.func("unreachable_resume", resume_value_ty, bot);
        self.p.func_ref(dead)
    }

    /// A perform whose capability is a value in scope: call it with the
    /// payloads and our own continuation as the resumption (`continue v`
    /// in the handler applies it — in machine terms, the capability
    /// returning). An abort handler instead finishes into its captured
    /// delimiter; the resumption is simply never invoked and nothing
    /// after the perform runs.
    pub(super) fn lower_capped_perform(
        &mut self,
        cap: ExprId,
        effect_name: &crate::name::Name,
        args: &[hir::CallArg],
        ctx: &Ctx,
        k: ExprId,
    ) -> ExprId {
        let sig = effect_name.symbol().ok().and_then(|symbol| {
            self.units
                .iter()
                .find_map(|u| u.types.catalog.effects.get(&symbol).cloned())
        });
        let Some(sig) = sig else {
            self.diagnostics
                .push("lowering: perform of an undeclared effect".into());
            return self.dead_end("undeclared_effect");
        };
        let resume_k = if sig.ret.is_never() {
            let resume_value_ty = self.map_ty(&sig.ret);
            self.dead_resume_k(resume_value_ty)
        } else {
            k
        };
        let arg_exprs: Vec<&Expr> = args.iter().map(|a| &a.value).collect();
        self.lower_args(&arg_exprs, ctx, vec![], &mut |this, mut values| {
            values.push(resume_k);
            let tuple = this.p.tuple(&values);
            this.p.app(cap, tuple)
        })
    }

}
