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

    /// The effect-generic instantiation of one perform site, from the
    /// node's baked instantiation, θ-substituted for the current
    /// specialization.
    pub(super) fn perform_instantiation(
        &mut self,
        effect: Symbol,
        expr: &Expr,
        ctx: &Ctx,
    ) -> Option<Vec<CheckTy>> {
        let sig = self
            .units
            .iter()
            .find_map(|u| u.types.catalog.effects.get(&effect).cloned())?;
        if sig.generics.is_empty() {
            return Some(vec![]);
        }
        let instantiation = expr.instantiation.as_ref()?;
        sig.generics
            .iter()
            .map(|generic| {
                instantiation
                    .iter()
                    .find(|(symbol, _)| symbol == generic)
                    .map(|(_, ty)| {
                        ty.substitute(&ctx.theta, &Default::default(), &Default::default())
                    })
            })
            .collect()
    }

    /// The capability for (effect, instantiation) in this scope: an exact
    /// capability parameter, or a closure materialized from the nearest
    /// `@handle` template for the label.
    pub(super) fn resolve_cap(
        &mut self,
        ctx: &Ctx,
        effect: Symbol,
        args: &[CheckTy],
    ) -> Option<ExprId> {
        if let Some(&cap) = ctx.caps.get(&(effect, args.to_vec())) {
            return Some(cap);
        }
        let &template = ctx.cap_templates.get(&effect)?;
        self.materialize_cap(template, args)
    }

    /// Materialize one capability closure from a handler template at a
    /// concrete instantiation, memoized: the handler body lowers with the
    /// effect's generics bound in θ — the generic-function specialization
    /// machinery applied to a handler block.
    pub(super) fn materialize_cap(&mut self, index: usize, args: &[CheckTy]) -> Option<ExprId> {
        let key = (index, args.to_vec());
        if let Some(&cap) = self.materialized_caps.get(&key) {
            return Some(cap);
        }
        let template = &self.handler_templates[index];
        let effect = template.effect;
        let handling_id = template.handling_id;
        let scaffold = std::sync::Arc::clone(&template.scaffold);
        let handler_block = template.handler_block.clone();
        let install_ctx = template.install_ctx.clone();

        let sig = self.effect_sig_at(effect, args)?;
        let dom_items = self.cap_dom_items(effect, args)?;
        if handler_block.args.len() + 1 > dom_items.len() {
            self.diagnostics.push(
                "lowering: handler block takes more arguments than the effect declares".into(),
            );
            return None;
        }
        let bot = self.p.ty_bot();
        let resumable = !sig.ret.is_never();
        let dom = self.p.ty_tuple(&dom_items);
        let cap = self.p.func("handler", dom, bot);
        self.escaping.insert(cap);
        let cap_ref = self.p.func_ref(cap);
        // Memoize before lowering the body: a handler body performing its
        // own effect resolves to this same capability.
        self.materialized_caps.insert(key, cap_ref);

        let cap_var = self.p.var(cap);
        // The delimiter: the handled scope's own return continuation,
        // captured by the capability closure. An abort applies it
        // directly; the frames between a perform and this scope simply
        // never resume.
        let mut inner = self.rebase_into_closure(&install_ctx, install_ctx.raw_ret_k);
        inner.owner = None;
        let generics = self
            .units
            .iter()
            .find_map(|u| u.types.catalog.effects.get(&effect).map(|s| s.generics.clone()))
            .unwrap_or_default();
        for (generic, arg) in generics.iter().zip(args) {
            inner.theta.insert(*generic, arg.clone());
        }
        if resumable {
            inner.resume_k = Some(self.p.extract(cap_var, (dom_items.len() - 1) as u32));
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
        // The handler body lowers from ITS OWN scaffold (the installing
        // frame's MIR body), whatever body is currently being lowered.
        self.scaffold_ctx.push(ScaffoldCtx {
            body: scaffold,
            loops: vec![],
        });
        let handler_body_expr = self.with_cells(&celled, &mut inner, |this, inner| {
            let handler_k = inner.ret_k;
            this.lower_sub_body_from_scaffold(handling_id, inner, handler_k)
                .unwrap_or_else(|| this.lower_block(&handler_block, &[], inner, handler_k))
        });
        self.scaffold_ctx.pop();
        self.p.set_body(cap, handler_body_expr);
        Some(cap_ref)
    }

    /// A named effectful function taken as a VALUE: its specialization
    /// wants capability parameters, but value call sites cannot thread
    /// them. Eta-expand instead — a plain-shaped wrapper closure that
    /// captures the capabilities in scope HERE (lexical capture, exactly
    /// like a function literal's — ADR 0011) and forwards them.
    pub(super) fn eta_expand_effectful_value(
        &mut self,
        symbol: Symbol,
        label: Label,
        cap_entries: &[(Symbol, Vec<CheckTy>)],
        ctx: &Ctx,
    ) -> Option<ExprId> {
        let mut caps = Vec::with_capacity(cap_entries.len());
        for (effect, args) in cap_entries {
            let Some(cap) = self.resolve_cap(ctx, *effect, args) else {
                self.diagnostics.push(format!(
                    "lowering: taking {symbol} as a value needs a handler for '{effect} in scope"
                ));
                return None;
            };
            caps.push(cap);
        }
        // The wrapper's shape is the value's own CPS type: the
        // specialization's domain with the capability slice cut out.
        let spec_items = match self.p.ty_kind(self.p.dom(label)) {
            TyKind::Tuple(items) => items.to_vec(),
            _ => return None,
        };
        let n_source = spec_items.len() - 1 - cap_entries.len();
        let mut wrap_items: Vec<TyId> = spec_items[..n_source].to_vec();
        wrap_items.push(spec_items[spec_items.len() - 1]);
        let bot = self.p.ty_bot();
        let wrap_dom = self.p.ty_tuple(&wrap_items);
        let wrapper = self.p.func("as_value", wrap_dom, bot);
        self.escaping.insert(wrapper);
        let wvar = self.p.var(wrapper);
        let mut call_items: Vec<ExprId> = (0..n_source)
            .map(|i| self.p.extract(wvar, i as u32))
            .collect();
        call_items.extend(caps.iter().copied());
        call_items.push(self.p.extract(wvar, n_source as u32));
        let tuple = self.p.tuple(&call_items);
        let spec_ref = self.p.func_ref(label);
        let body = self.p.app(spec_ref, tuple);
        self.p.set_body(wrapper, body);
        Some(self.p.func_ref(wrapper))
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

    /// A perform whose capability is in scope (a parameter, or
    /// materialized from a template at this perform's instantiation):
    /// call it with the payloads and our own continuation as the
    /// resumption (`continue v` in the handler applies it — in machine
    /// terms, the capability returning). An abort handler instead
    /// finishes into its captured delimiter; the resumption is simply
    /// never invoked and nothing after the perform runs.
    pub(super) fn lower_capped_perform(
        &mut self,
        effect: Symbol,
        expr: &Expr,
        args: &[hir::CallArg],
        ctx: &Ctx,
        k: ExprId,
    ) -> ExprId {
        let Some(instantiation) = self.perform_instantiation(effect, expr, ctx) else {
            self.diagnostics
                .push(format!("lowering: perform of '{effect} without its instantiation"));
            return self.dead_end("missing_perform_instantiation");
        };
        let Some(cap) = self.resolve_cap(ctx, effect, &instantiation) else {
            self.diagnostics.push(format!(
                "lowering: perform of '{effect} with no capability in scope"
            ));
            return self.dead_end("capability_not_in_scope");
        };
        let Some(sig) = self.effect_sig_at(effect, &instantiation) else {
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
