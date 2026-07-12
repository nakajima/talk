use super::*;

impl<'a> Lowering<'a> {
    // ----- Function lowering ----------------------------------------------

    pub(super) fn lower_function(&mut self, symbol: Symbol, theta: Theta, label: Label) {
        let Some(source) = self.sources.get(&symbol) else {
            self.diagnostics.push(format!(
                "lowering: no body found for {symbol} (not yet supported)"
            ));
            return;
        };
        let unit = source.unit;
        let source_params = source.params;
        let source_body = source.body;

        let is_mutating = self.mutating.contains(&symbol);
        let is_init = self.is_init(symbol);
        // An init's self is constructed and delivered to the caller, never
        // dropped in the body — the flow checker seeds no init params.
        let self_symbol = source_params
            .first()
            .and_then(|param| param.name.symbol().ok());

        // Symbols that must live in cells: assigned-to (resolver) plus
        // receivers of mutating-method calls (write-back targets). A mutating
        // method's own `self` must always be cell-backed so its inout return
        // wrapper can deliver the current receiver, even if the body mutates
        // through raw storage rather than assigning a `self` field.
        let mut cellable = self.cellable_symbols(unit, source_body);
        if is_mutating && let Some(self_symbol) = self_symbol {
            cellable.insert(self_symbol);
        }

        let self_var = self.p.var(label);
        let mut env = FxHashMap::default();
        let mut params = Vec::with_capacity(source_params.len());
        let mut mutated_params: Vec<(Symbol, ExprId)> = vec![];
        for (i, param) in source_params.iter().enumerate() {
            let extract = self.p.extract(self_var, i as u32);
            params.push(extract);
            if let Ok(param_symbol) = param.name.symbol() {
                if cellable.contains(&param_symbol) {
                    mutated_params.push((param_symbol, extract));
                } else {
                    env.insert(param_symbol, Binding::Value(extract));
                }
            }
        }
        // Capability parameters sit between the source parameters and the
        // return continuation, one per user-effect instantiation in the
        // latent row — the same order `demand` appended them.
        let cap_entries = self.cap_entries_of(symbol, &theta);
        let mut caps = FxHashMap::default();
        for (i, entry) in cap_entries.iter().enumerate() {
            let extract = self.p.extract(self_var, (source_params.len() + i) as u32);
            caps.insert(entry.clone(), extract);
        }
        let ret_k = self
            .p
            .extract(self_var, (source_params.len() + cap_entries.len()) as u32);
        let mut param_names: Vec<String> =
            source_params.iter().map(|p| p.name.name_str()).collect();
        param_names.extend(
            cap_entries
                .iter()
                .map(|(effect, _)| format!("cap_{effect}")),
        );
        param_names.push("k".into());
        let name_refs: Vec<&str> = param_names.iter().map(String::as_str).collect();
        self.p.name_params(label, &name_refs);

        let mut ctx = Ctx {
            unit,
            owner: Some(symbol),
            theta,
            env,
            local_evidence: FxHashMap::default(),
            temps: FxHashMap::default(),
            ret_k,
            tail_k: ret_k,
            raw_ret_k: ret_k,
            resume_k: None,
            top_level: false,
            caps,
            cap_templates: FxHashMap::default(),
            params,
            loops: vec![],
            drop_stack: vec![],
            drop_flags: FxHashMap::default(),
            initializing_self: None,
            cellable,
        };
        // Mutated parameters are assignment-converted: box each into a cell
        // bound through a continuation before the body runs.
        let mut prologue: Vec<(Symbol, ExprId)> = vec![];
        for (symbol, extract) in mutated_params {
            prologue.push((symbol, extract));
        }
        if is_init {
            ctx.initializing_self = self_symbol;
        }
        // The checked MIR body (the same one `lower_block` reuses below): a
        // parameter moved on only some paths has Conditional drops recorded
        // here, which need flag cells like a let-bind's.
        let Some(mir_body) = self.checked_body(source_body, &ctx) else {
            self.diagnostics.push(format!(
                "lowering: missing checked MIR body for block {:?}",
                source_body.id
            ));
            let body = self.dead_end("missing_checked_mir_function_body");
            self.p.set_body(label, body);
            return;
        };
        // Owned by-value parameters: consumed arguments' drops ride the
        // callee, so the flow checker schedules them at body exit — seed
        // the drop stack so those candidates resolve (`'heap`-carrying
        // params are exempt: the ledger never counts parameters).
        let signature_params = self
            .symbol_check_ty(symbol, &ctx.theta)
            .and_then(|sig| match sig {
                CheckTy::Func(params, ..) => Some(params),
                _ => None,
            })
            .unwrap_or_default();
        let mut param_drops: Vec<DropBinding> = vec![];
        for (index, param) in source_params.iter().enumerate() {
            let Ok(param_symbol) = param.name.symbol() else {
                continue;
            };
            let Some(raw) = param
                .ty
                .clone()
                .or_else(|| self.units[unit].types.node_types.get(&param.id).cloned())
                .or_else(|| signature_params.get(index).cloned())
            else {
                continue;
            };
            let substituted = raw.substitute(&ctx.theta, &Default::default(), &Default::default());
            let param_ty = self.normalize_check_ty(substituted, unit);
            if matches!(param_ty, CheckTy::Borrow(..))
                || !self.needs_drop_type(&param_ty)
                || self.contains_object_type(&param_ty)
            {
                continue;
            }
            param_drops.push(DropBinding {
                symbol: param_symbol,
                key_path: Place::root(param_symbol),
                ty: param_ty,
                dynamic_flags: self.drop_flag_keys_for_symbol(&mir_body, param_symbol),
            });
        }
        ctx.drop_stack.extend(param_drops.clone());
        let body = self.with_drop_flags(&param_drops, &mut ctx, |this, ctx| {
            this.with_cells(&prologue, ctx, |this, ctx| {
                // Construction semantics: an init's caller receives self, not
                // the body's final value — wrap the ret continuation to drop
                // the value and deliver self's current state.
                if is_init && let Some(self_symbol) = self_symbol {
                    let self_now = match ctx.env.get(&self_symbol).copied() {
                        Some(Binding::Cell(cell)) => match *this.p.ty_kind(this.p.expr_ty(cell)) {
                            TyKind::Cell(inner) => this.p.primop(Op::CellGet, &[cell], inner),
                            _ => {
                                this.diagnostics
                                    .push("lowering: init self cell without a cell type".into());
                                this.p.void()
                            }
                        },
                        Some(Binding::Value(value)) => value,
                        None => {
                            this.diagnostics
                                .push("lowering: init without a self binding".into());
                            this.p.void()
                        }
                    };
                    let body_value_ty = block_value_ty(this, source_body, ctx);
                    let bot = this.p.ty_bot();
                    let wrap = this.p.func("init_ret", body_value_ty, bot);
                    let orig_ret = ctx.ret_k;
                    // A `'heap` init attaches the instantiation's finalizer
                    // thunk to the fresh object before delivering it (the thunk
                    // rides as a function value so its captures resolve here).
                    let owner = this.units.iter().find_map(|u| {
                        u.types
                            .catalog
                            .structs
                            .iter()
                            .find(|(_, info)| info.inits.contains(&symbol))
                            .map(|(owner, info)| (*owner, info.params.clone()))
                    });
                    let finalizer = owner.and_then(|(head, params)| {
                        if !this.symbol_is_heap(head) {
                            return None;
                        }
                        let args: Vec<CheckTy> = params
                            .iter()
                            .map(|param| {
                                ctx.theta
                                    .get(param)
                                    .cloned()
                                    .unwrap_or(CheckTy::Param(*param))
                            })
                            .collect();
                        this.finalizer_thunk(ctx, head, &args)
                    });
                    let wrap_body = match finalizer {
                        Some(thunk) => {
                            let self_ty = this.p.expr_ty(self_now);
                            let deliver = this.p.func("attach_finalizer", self_ty, bot);
                            let bound_self = this.p.var(deliver);
                            let void_ty = this.p.ty_void();
                            let thunk_ref = this.p.func_ref(thunk);
                            let attach =
                                this.p
                                    .primop(Op::SetFinalizer, &[bound_self, thunk_ref], void_ty);
                            let done = this.p.app(orig_ret, bound_self);
                            let body = this.sequence_void_effect(attach, done);
                            this.p.set_body(deliver, body);
                            let deliver_ref = this.p.func_ref(deliver);
                            this.p.app(deliver_ref, self_now)
                        }
                        None => this.p.app(orig_ret, self_now),
                    };
                    this.p.set_body(wrap, wrap_body);
                    ctx.ret_k = this.p.func_ref(wrap);
                    ctx.tail_k = ctx.ret_k;
                }
                // Inout self: wrap the ret continuation so every return
                // delivers [result, current Self] (read from self's cell).
                if is_mutating && let Some(self_symbol) = self_symbol {
                    let Some(Binding::Cell(self_cell)) = ctx.env.get(&self_symbol).copied() else {
                        this.diagnostics
                            .push("lowering: mutating method without a self cell".into());
                        let ret_k = ctx.ret_k;
                        return this.lower_block(source_body, ctx, ret_k);
                    };
                    let TyKind::Fn(pair_ty, _) = *this.p.ty_kind(this.p.expr_ty(ctx.ret_k)) else {
                        unreachable!("ret continuation is not a function");
                    };
                    let TyKind::Tuple(items) = this.p.ty_kind(pair_ty) else {
                        unreachable!("mutating ret payload is not a tuple");
                    };
                    let result_ty = items[0];
                    let self_ty = items[1];
                    let bot = this.p.ty_bot();
                    let wrap = this.p.func("ret_inout", result_ty, bot);
                    let result = this.p.var(wrap);
                    let self_now = this.p.primop(Op::CellGet, &[self_cell], self_ty);
                    let pair = this.p.tuple(&[result, self_now]);
                    let orig_ret = ctx.ret_k;
                    let wrap_body = this.p.app(orig_ret, pair);
                    this.p.set_body(wrap, wrap_body);
                    ctx.ret_k = this.p.func_ref(wrap);
                    ctx.tail_k = ctx.ret_k;
                }
                let ret_k = ctx.ret_k;
                this.lower_block(source_body, ctx, ret_k)
            })
        });
        self.p.set_body(label, body);
    }

    /// Symbols in this body that must be assignment-converted: those the
    /// resolver saw assigned, plus roots of mutating-method receivers
    /// (`c.bump()` and `person.name.bump()` both write back through `c` /
    /// `person`).
    pub(super) fn cellable_symbols<D: derive_visitor::Drive>(
        &self,
        unit: usize,
        body: &D,
    ) -> FxHashSet<Symbol> {
        use derive_visitor::Visitor;

        #[derive(Visitor)]
        #[visitor(Expr(enter), Stmt(enter))]
        struct ReceiverScan<'s> {
            mutating: &'s FxHashSet<Symbol>,
            found: FxHashSet<Symbol>,
        }
        impl ReceiverScan<'_> {
            // Any assignment target needs a cell. User assignments are
            // already in `mutated_symbols` (resolution tracks them); this
            // catches assignments elaborated after resolution (`for x in
            // mut xs` restores its source with one).
            fn enter_stmt(&mut self, stmt: &crate::typed_ast::Stmt) {
                if let crate::typed_ast::StmtKind::Assignment(lhs, _) = &stmt.kind
                    && let Some(root) = receiver_root_symbol(lhs)
                {
                    self.found.insert(root);
                }
            }

            fn enter_expr(&mut self, expr: &Expr) {
                let ExprKind::Call { callee, args, .. } = &expr.kind else {
                    return;
                };
                match &callee.kind {
                    ExprKind::Member(Some(receiver), ..) | ExprKind::Proj(receiver, ..) => {
                        let Some(symbol) = receiver_root_symbol(receiver) else {
                            return;
                        };
                        let target = match &callee.member_resolution {
                            Some(crate::types::output::MemberResolution::Direct(s)) => *s,
                            Some(crate::types::output::MemberResolution::ViaConformance {
                                witness,
                                ..
                            }) => *witness,
                            None => return,
                        };
                        if self.mutating.contains(&target) {
                            self.found.insert(symbol);
                        }
                    }
                    // A mutating free function (`mut` first parameter,
                    // ADR 0018) writes back through its first argument.
                    ExprKind::Variable(name) => {
                        if let Ok(symbol) = name.symbol()
                            && self.mutating.contains(&symbol)
                            && let Some(arg) = args.first()
                            && let Some(root) = receiver_root_symbol(&arg.value)
                        {
                            self.found.insert(root);
                        }
                    }
                    _ => {}
                }
            }
        }

        let mut scan = ReceiverScan {
            mutating: &self.mutating,
            found: FxHashSet::default(),
        };
        body.drive(&mut scan);
        let mut cellable = scan.found;
        cellable.extend(self.units[unit].resolved.mutated_symbols.iter().copied());
        cellable
    }

    /// Bind each (symbol, initial value) as a fresh cell, threading through
    /// continuations so each cell is created exactly once.
    pub(super) fn with_cells(
        &mut self,
        bindings: &[(Symbol, ExprId)],
        ctx: &mut Ctx,
        finish: impl FnOnce(&mut Self, &mut Ctx) -> ExprId,
    ) -> ExprId {
        let Some(((symbol, init), rest)) = bindings.split_first() else {
            return finish(self, ctx);
        };
        let init_ty = self.p.expr_ty(*init);
        let cell_ty = self.p.ty_cell(init_ty);
        let bot = self.p.ty_bot();
        let bind = self.p.func("cell", cell_ty, bot);
        let cell_var = self.p.var(bind);
        ctx.env.insert(*symbol, Binding::Cell(cell_var));
        if ctx.top_level {
            self.top_level_cells.insert(*symbol, cell_var);
        }
        let body = self.with_cells(rest, ctx, finish);
        self.p.set_body(bind, body);
        let bind_ref = self.p.func_ref(bind);
        let cell = self.p.primop(Op::CellNew, &[*init], cell_ty);
        self.p.app(bind_ref, cell)
    }
}
