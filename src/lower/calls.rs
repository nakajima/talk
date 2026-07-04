use super::*;

impl<'a> Lowering<'a> {
    // ----- Calls -----------------------------------------------------------

    pub(super) fn lower_call(
        &mut self,
        expr: &Expr,
        callee: &Expr,
        args: &[hir::CallArg],
        trailing_block: Option<&Block>,
        ctx: &Ctx,
        k: ExprId,
    ) -> ExprId {
        // Calls through function VALUES — local bindings, function
        // literals, and function-typed record fields — dispatch
        // indirectly (M6 closures).
        let is_value_callee = matches!(&callee.kind, ExprKind::Func(_))
            || matches!(&callee.kind, ExprKind::Variable(name)
                if name.symbol().ok().is_some_and(|s| ctx.env.contains_key(&s)))
            || self.is_field_value_callee(callee, ctx);
        if is_value_callee {
            return self.lower_value_call(callee, args, trailing_block, ctx, k);
        }
        if let Some(done) =
            self.try_lower_existential_member_call(callee, args, trailing_block, ctx, k)
        {
            return done;
        }
        if let Some(done) =
            self.try_lower_local_evidence_member_call(callee, args, trailing_block, ctx, k)
        {
            return done;
        }

        // Resolve the target specialization.
        let target = self.resolve_callee(expr, callee, args, ctx);
        let Some((label, symbol, prefix, callee_theta)) = target else {
            return self.dead_end("unresolved_callee");
        };
        // The capabilities this callee's row demands, from our own scope
        // (our own cap parameters, or materialized from an installed
        // `@handle` template at the callee's instantiations).
        let cap_entries = self.cap_entries_of(symbol, &callee_theta);
        let mut cap_values = Vec::with_capacity(cap_entries.len());
        for (effect, args) in &cap_entries {
            let Some(cap) = self.resolve_cap(ctx, *effect, args) else {
                self.diagnostics.push(format!(
                    "lowering: call needs a handler for '{effect} that is not installed yet"
                ));
                return self.dead_end("capability_not_in_scope");
            };
            cap_values.push(cap);
        }
        let trailing_value = trailing_block.map(|b| {
            // The trailing block's declared parameter type: the domain item
            // before the callee's capability parameters and continuation.
            let expected = match self.p.ty_kind(self.p.dom(label)) {
                TyKind::Tuple(items) if items.len() >= 2 + cap_entries.len() => {
                    Some(items[items.len() - 2 - cap_entries.len()])
                }
                _ => None,
            };
            self.lower_block_closure(b, expected, ctx)
        });

        let mut arg_exprs: Vec<&Expr> = vec![];
        let mut done: Vec<ExprId> = vec![];
        match prefix {
            Prefix::None => {}
            Prefix::Receiver(receiver) => arg_exprs.push(receiver),
            Prefix::Value(value) => done.push(value),
        }
        arg_exprs.extend(args.iter().map(|a| &a.value));

        // Inout self: the callee's ret carries [result, Self]; write Self
        // back into the receiver's cell, then deliver the result to k.
        let k = if self.mutating.contains(&symbol) {
            match self.writeback_cont(&prefix, label, ctx, k) {
                Some(adapter) => adapter,
                None => {
                    self.diagnostics.push(
                        "lowering: mutating method on a non-writable receiver (not yet supported)"
                            .into(),
                    );
                    k
                }
            }
        } else {
            k
        };

        // Ledger rule D: an rvalue argument carrying `'heap` handles dies
        // with the call — release its +1 once the call returns (place-read
        // arguments carried nothing; the callee's params neither acquire
        // nor release).
        let done_len = done.len();
        let func_ref = self.p.func_ref(label);
        self.lower_args(&arg_exprs, ctx, done, &mut |this, values| {
            let k = this.release_temps_then(&arg_exprs, done_len, &values, ctx, k);
            let mut tuple_items = values;
            if let Some(trailing) = trailing_value {
                tuple_items.push(trailing);
            }
            tuple_items.extend(cap_values.iter().copied());
            tuple_items.push(k);
            let arg_tuple = this.p.tuple(&tuple_items);
            this.p.app(func_ref, arg_tuple)
        })
    }

    /// Shared tail for dispatching a protocol-requirement call through an
    /// erased witness: builds the CPS witness type from `signature`, lowers the
    /// trailing block and arguments, then assembles the call. `build_witness`
    /// produces the witness expression for the resolved receiver (and may
    /// rewrite `values[0]`, e.g. to repack a payload); returning `Err` aborts
    /// the call with that expression (a `dead_end`).
    #[allow(clippy::too_many_arguments)]
    pub(super) fn lower_requirement_call(
        &mut self,
        receiver: &Expr,
        args: &[hir::CallArg],
        trailing_block: Option<&Block>,
        ctx: &Ctx,
        k: ExprId,
        signature: CheckTy,
        not_a_function: &str,
        dead_end_label: &str,
        mut build_witness: impl FnMut(&mut Self, &mut Vec<ExprId>, TyId) -> Result<ExprId, ExprId>,
    ) -> Option<ExprId> {
        let CheckTy::Func(params, ret, _) = signature else {
            self.diagnostics.push(not_a_function.into());
            return Some(self.dead_end(dead_end_label));
        };
        let mut dom_items: Vec<TyId> = params.iter().map(|param| self.map_ty(param)).collect();
        let ret_ty = self.map_ty(&ret);
        let bot = self.p.ty_bot();
        let ret_k_ty = self.p.ty_fn(ret_ty, bot);
        dom_items.push(ret_k_ty);
        let dom = self.p.ty_tuple(&dom_items);
        let witness_ty = self.p.ty_fn(dom, bot);
        let trailing_value = trailing_block.map(|block| {
            let expected = self.final_param_ty(witness_ty);
            self.lower_block_closure(block, expected, ctx)
        });

        let mut arg_exprs: Vec<&Expr> = vec![receiver];
        arg_exprs.extend(args.iter().map(|arg| &arg.value));
        Some(
            self.lower_args(&arg_exprs, ctx, vec![], &mut |this, mut values| {
                let k = this.release_temps_then(&arg_exprs, 0, &values, ctx, k);
                let witness = match build_witness(this, &mut values, witness_ty) {
                    Ok(witness) => witness,
                    Err(early) => return early,
                };
                if let Some(trailing) = trailing_value {
                    values.push(trailing);
                }
                values.push(k);
                let tuple = this.p.tuple(&values);
                this.p.app(witness, tuple)
            }),
        )
    }

    pub(super) fn try_lower_existential_member_call(
        &mut self,
        callee: &Expr,
        args: &[hir::CallArg],
        trailing_block: Option<&Block>,
        ctx: &Ctx,
        k: ExprId,
    ) -> Option<ExprId> {
        let ExprKind::Member(Some(receiver), label) = &callee.kind else {
            return None;
        };
        let receiver_ty = self.checker_ty(receiver, ctx);
        let (protocol, assoc) = match receiver_ty {
            CheckTy::Any { protocol, assoc } => (protocol, assoc),
            CheckTy::Borrow(_, inner) => match *inner {
                CheckTy::Any { protocol, assoc } => (protocol, assoc),
                _ => return None,
            },
            _ => return None,
        };
        let label_str = label.to_string();
        let (owner, requirement) = self.units[ctx.unit]
            .types
            .catalog
            .requirement_in(protocol, &label_str)
            .map(|(owner, requirement)| (owner, requirement.clone()))?;
        let index =
            self.existential_requirement_index(protocol, &label_str, requirement.symbol, ctx.unit)?;
        let signature =
            self.erased_requirement_signature(protocol, &assoc, owner, &requirement, ctx.unit)?;
        self.lower_requirement_call(
            receiver,
            args,
            trailing_block,
            ctx,
            k,
            signature,
            "lowering: existential requirement is not a function",
            "existential_requirement",
            |this, values, witness_ty| {
                let receiver_value = values[0];
                Ok(this.p.primop(
                    Op::ExistentialWitness(index as u32),
                    &[receiver_value],
                    witness_ty,
                ))
            },
        )
    }

    pub(super) fn try_lower_local_evidence_member_call(
        &mut self,
        callee: &Expr,
        args: &[hir::CallArg],
        trailing_block: Option<&Block>,
        ctx: &Ctx,
        k: ExprId,
    ) -> Option<ExprId> {
        let ExprKind::Member(Some(receiver), label) = &callee.kind else {
            return None;
        };
        let CheckTy::Param(param) = self.checker_ty(receiver, ctx) else {
            return None;
        };
        let resolution = callee.member_resolution.clone();
        let protocol = match resolution {
            Some(crate::types::output::MemberResolution::ViaConformance { protocol, .. }) => {
                protocol
            }
            _ => return None,
        };
        let evidence = self.local_evidence_for(ctx, param, protocol)?;
        let label_str = label.to_string();
        let (owner, requirement) = self.units[ctx.unit]
            .types
            .catalog
            .requirement_in(protocol, &label_str)
            .map(|(owner, requirement)| (owner, requirement.clone()))?;
        let source_requirements = self.units[ctx.unit]
            .types
            .catalog
            .requirements_for_conformance(evidence.protocol);
        let index = source_requirements
            .iter()
            .position(|(_, _, source)| source.symbol == requirement.symbol)?;
        let signature =
            self.erased_requirement_signature(protocol, &[], owner, &requirement, ctx.unit)?;
        self.lower_requirement_call(
            receiver,
            args,
            trailing_block,
            ctx,
            k,
            signature,
            "lowering: local-evidence requirement is not a function",
            "local_evidence_requirement",
            |this, values, _witness_ty| {
                let payload = values[0];
                let Some(package) =
                    this.existential_pack_from_local_evidence(protocol, &[], param, payload, ctx)
                else {
                    return Err(this.dead_end("local_evidence_pack"));
                };
                values[0] = package;
                Ok(this.p.extract(evidence.table, index as u32))
            },
        )
    }

    /// The write-back adapter for a mutating-method call: receives
    /// [result, Self], writes Self back through the receiver's assignment
    /// target, and passes the result on (the "caller performs the
    /// write-back" half of inout — Racordon et al., JOT 2022).
    pub(super) fn writeback_cont(
        &mut self,
        prefix: &Prefix<'_>,
        label: Label,
        ctx: &Ctx,
        k: ExprId,
    ) -> Option<ExprId> {
        let Prefix::Receiver(receiver) = prefix else {
            return None;
        };
        // An rvalue receiver has no home: the updated Self dies with the
        // call (e.g. `xs.iter().index(..)`) — unpack the pair and pass the
        // result on without a store.
        if !Self::receiver_is_place(receiver) {
            let pair_ty = self.mutating_pair_ty(label)?;
            let bot = self.p.ty_bot();
            let unpack = self.p.func("discard_writeback", pair_ty, bot);
            let pair = self.p.var(unpack);
            let result = self.p.extract(pair, 0);
            let unpack_body = self.p.app(k, result);
            self.p.set_body(unpack, unpack_body);
            return Some(self.p.func_ref(unpack));
        }
        let (base, path) = self.assignment_target(receiver, ctx)?;
        let crate::lower::statements::AssignBase::Cell(cell) = base else {
            // Heap receivers mutate in place: no write-back.
            return None;
        };

        let pair_ty = self.mutating_pair_ty(label)?;
        let bot = self.p.ty_bot();
        let void_ty = self.p.ty_void();
        let unpack = self.p.func("writeback", pair_ty, bot);
        let pair = self.p.var(unpack);
        let result = self.p.extract(pair, 0);
        let new_self = self.p.extract(pair, 1);
        let stored = self.rebuilt_assignment_value(cell, &path, new_self);

        let after = self.p.func("after_writeback", void_ty, bot);
        let after_body = self.p.app(k, result);
        self.p.set_body(after, after_body);
        let after_ref = self.p.func_ref(after);

        let cell_set = self.p.primop(Op::CellSet, &[cell, stored], void_ty);
        let unpack_body = self.p.app(after_ref, cell_set);
        self.p.set_body(unpack, unpack_body);
        Some(self.p.func_ref(unpack))
    }

    /// A place expression a write-back can land in: a variable, or a
    /// member/field path rooted at one. Anything else (a call result, a
    /// literal) is an rvalue whose post-call Self has no home.
    fn receiver_is_place(expr: &Expr) -> bool {
        match &expr.kind {
            ExprKind::Variable(_) => true,
            ExprKind::Member(Some(receiver), ..) | ExprKind::Proj(receiver, ..) => {
                Self::receiver_is_place(receiver)
            }
            _ => false,
        }
    }

    /// The `[result, Self]` payload type of a mutating callee's ret
    /// continuation, read off the demanded function's signature.
    fn mutating_pair_ty(&mut self, label: Label) -> Option<TyId> {
        let TyKind::Tuple(dom_items) = self.p.ty_kind(self.p.dom(label)) else {
            return None;
        };
        let ret_k_ty = *dom_items.last()?;
        let TyKind::Fn(pair_ty, _) = *self.p.ty_kind(ret_k_ty) else {
            return None;
        };
        Some(pair_ty)
    }

    /// Sequentially lower argument expressions, chaining continuations for
    /// the impure ones; `finish` receives the value expressions.
    pub(super) fn lower_args(
        &mut self,
        exprs: &[&Expr],
        ctx: &Ctx,
        mut done: Vec<ExprId>,
        finish: &mut dyn FnMut(&mut Self, Vec<ExprId>) -> ExprId,
    ) -> ExprId {
        let Some((first, rest)) = exprs.split_first() else {
            return finish(self, done);
        };
        if let Some(value) = self.try_pure(first, ctx) {
            done.push(value);
            return self.lower_args(rest, ctx, done, finish);
        }
        let value_ty = self.expr_lambda_ty(first, ctx);
        let bot = self.p.ty_bot();
        let arg_k = self.p.func("arg", value_ty, bot);
        let value = self.p.var(arg_k);
        done.push(value);
        let rest_owned: Vec<&Expr> = rest.to_vec();
        let body = self.lower_args(&rest_owned, ctx, done, finish);
        self.p.set_body(arg_k, body);
        let arg_ref = self.p.func_ref(arg_k);
        self.lower_expr(first, ctx, arg_ref)
    }

    /// Resolve a callee to a demanded specialization label. Returns the
    /// label plus an optional receiver to prepend (instance member calls).
    pub(super) fn resolve_callee<'e>(
        &mut self,
        expr: &Expr,
        callee: &'e Expr,
        args: &[hir::CallArg],
        ctx: &Ctx,
    ) -> Option<(Label, Symbol, Prefix<'e>, Theta)> {
        match &callee.kind {
            ExprKind::Variable(name) => {
                let symbol = name.symbol().ok()?;
                if ctx.env.contains_key(&symbol) {
                    self.diagnostics
                        .push("lowering: calling local function values not yet supported".into());
                    return None;
                }
                let theta = self.call_theta(symbol, callee.instantiation.as_ref(), ctx);
                let label = self.demand(symbol, theta.clone());
                Some((label, symbol, Prefix::None, theta))
            }
            // `Person(args…)`: construction is a call to the (explicit or
            // memberwise-synthesized) initializer with a blank record as
            // self; the init body fills the fields and returns self.
            ExprKind::Constructor(name) => {
                let struct_symbol = name.symbol().ok()?;
                let resolution = callee.member_resolution.clone();
                let Some(crate::types::output::MemberResolution::Direct(init)) = resolution else {
                    self.diagnostics.push(format!(
                        "lowering: unresolved initializer for {struct_symbol}"
                    ));
                    return None;
                };
                let constructed = self.checker_ty(expr, ctx);
                let blank = self.blank_record(struct_symbol)?;
                let mut theta = self.call_theta(init, expr.instantiation.as_ref(), ctx);
                self.owner_theta(init, &constructed, &mut theta);
                let label = self.demand(init, theta.clone());
                Some((label, init, Prefix::Value(blank), theta))
            }
            // Protocol-static (operators) or instance member calls: resolve
            // through member_resolutions + the conformance table.
            ExprKind::Member(receiver, label) => {
                let resolution = callee.member_resolution.clone();
                let receiver_expr: Option<&'e Expr> = match receiver {
                    Some(r) if !matches!(r.kind, ExprKind::Constructor(_)) => Some(r.as_ref()),
                    _ => None,
                };
                let prefix = match receiver_expr {
                    Some(r) => Prefix::Receiver(r),
                    None => Prefix::None,
                };
                // The dispatch head: the (θ-substituted) type of the first
                // value argument (receiver for instance calls; lhs for
                // operator protocol-static calls).
                let head_expr = receiver_expr.or_else(|| args.first().map(|a| &a.value));
                let head_ty = head_expr.map(|h| Self::borrow_erased_ty(self.checker_ty(h, ctx)));
                match resolution {
                    Some(crate::types::output::MemberResolution::ViaConformance {
                        protocol,
                        witness,
                    }) => {
                        let head_ty = head_ty?;
                        // Method-level generics (`map<U>`) ride the callee's
                        // recorded instantiation; the head derives only the
                        // Self/assoc entries.
                        let generics = self.instantiation_at(callee.instantiation.as_ref(), ctx);
                        let (target, target_symbol, witness_theta) = self.resolve_witness(
                            protocol,
                            witness,
                            label.to_string(),
                            &head_ty,
                            &generics,
                        )?;
                        Some((target, target_symbol, prefix, witness_theta))
                    }
                    Some(crate::types::output::MemberResolution::Direct(member)) => {
                        let mut theta = self.call_theta(member, callee.instantiation.as_ref(), ctx);
                        if let Some(head) = &head_ty {
                            self.owner_theta(member, head, &mut theta);
                        }
                        let target = self.demand(member, theta.clone());
                        Some((target, member, prefix, theta))
                    }
                    None => {
                        // No resolution at this node: the member use rode
                        // its binder's scheme (qualified types — Jones
                        // 1994) and the checker discharged it per call
                        // site. The θ-substituted head is concrete here,
                        // so resolve the label the way the solver's
                        // try_member does: the type's own methods first,
                        // then protocol witnesses.
                        if let Some(CheckTy::Nominal(symbol, _)) = &head_ty {
                            let label_str = label.to_string();
                            let catalog = &self.units[self.entry].types.catalog;
                            let method = catalog
                                .structs
                                .get(symbol)
                                .and_then(|i| i.methods.get(&label_str))
                                .or_else(|| {
                                    catalog
                                        .enums
                                        .get(symbol)
                                        .and_then(|i| i.methods.get(&label_str))
                                })
                                .copied();
                            if let Some(member) = method {
                                let head = head_ty.clone()?;
                                let mut theta =
                                    self.call_theta(member, callee.instantiation.as_ref(), ctx);
                                self.owner_theta(member, &head, &mut theta);
                                let target = self.demand(member, theta.clone());
                                return Some((target, member, prefix, theta));
                            }
                            let protocols: Vec<Symbol> = catalog
                                .member_owners
                                .get(&label_str)
                                .into_iter()
                                .flatten()
                                .filter_map(|owner| match owner {
                                    crate::types::catalog::MemberOwner::Protocol(p) => Some(*p),
                                    _ => None,
                                })
                                .filter(|p| {
                                    catalog.conformances.contains_key(&(*symbol, *p))
                                        || self
                                            .units
                                            .iter()
                                            .any(|u| u.types.catalog.derivable.contains(p))
                                })
                                .collect();
                            for protocol in protocols {
                                let Some((_, requirement)) = self.units[self.entry]
                                    .types
                                    .catalog
                                    .requirement_in(protocol, &label_str)
                                else {
                                    continue;
                                };
                                let witness = requirement.symbol;
                                let head = head_ty.clone()?;
                                let generics =
                                    self.instantiation_at(callee.instantiation.as_ref(), ctx);
                                if let Some((target, target_symbol, witness_theta)) = self
                                    .resolve_witness(
                                        protocol,
                                        witness,
                                        label_str.clone(),
                                        &head,
                                        &generics,
                                    )
                                {
                                    return Some((target, target_symbol, prefix, witness_theta));
                                }
                            }
                        }
                        self.diagnostics.push(format!(
                            "lowering: unresolved member call '{label}' at {:?}",
                            expr.id
                        ));
                        None
                    }
                }
            }
            other => {
                self.diagnostics
                    .push(format!("lowering: callee not yet supported: {other:?}"));
                None
            }
        }
    }

    /// A blank record for `struct_symbol`: every field Void until the init
    /// body assigns it (Void poison keeps a partial init honest at
    /// runtime).
    pub(super) fn blank_record(&mut self, struct_symbol: Symbol) -> Option<ExprId> {
        let field_count = self
            .units
            .iter()
            .find_map(|u| u.types.catalog.structs.get(&struct_symbol))
            .map(|info| info.fields.len())?;
        let void = self.p.void();
        let fields = vec![void; field_count];
        if self.symbol_is_heap(struct_symbol) {
            let ty = self.p.ty(TyKind::Object(struct_symbol));
            return Some(self.p.primop(Op::ObjectNew, &fields, ty));
        }
        let ty = self.p.ty(TyKind::Boxed(struct_symbol));
        Some(self.p.primop(Op::RecordNew(struct_symbol), &fields, ty))
    }

    /// The finalizer thunk for a `'heap` instantiation: `λ(self, k)` that
    /// dispatches the `Deinit` witness (if any), drops owned *value* fields
    /// (buffer frees etc. — object fields are the region's own members and
    /// are skipped), then continues. `None` when nothing needs doing.
    pub(super) fn finalizer_thunk(
        &mut self,
        ctx: &Ctx,
        symbol: Symbol,
        args: &[CheckTy],
    ) -> Option<Label> {
        let theta = self.nominal_theta(symbol, args);
        let key = (symbol, theta_key(&theta));
        if let Some(&label) = self.finalizer_thunks.get(&key) {
            return Some(label);
        }
        let fields = self.field_types_for(symbol, args);
        let witness = self.deinit_witness(symbol);
        let any_owned = fields
            .iter()
            .any(|(_, field_ty)| self.needs_drop_type(field_ty));
        if witness.is_none() && !any_owned {
            return None;
        }
        let obj_ty = self.p.ty(TyKind::Object(symbol));
        let void_ty = self.p.ty_void();
        let bot = self.p.ty_bot();
        let k_ty = self.p.ty_fn(void_ty, bot);
        let dom = self.p.ty_tuple(&[obj_ty, k_ty]);
        let thunk = self.p.func(&format!("finalize_{symbol}"), dom, bot);
        self.finalizer_thunks.insert(key, thunk);
        let vthunk = self.p.var(thunk);
        let self_value = self.p.extract(vthunk, 0);
        let k = self.p.extract(vthunk, 1);
        let unit_value = self.p.void();
        let mut body = self.p.app(k, unit_value);
        for (index, (_, field_ty)) in fields.iter().enumerate().rev() {
            if !self.needs_drop_type(field_ty) {
                continue;
            }
            let field_lambda_ty = self.map_ty(field_ty);
            let field_value =
                self.p
                    .primop(Op::ObjectGet(index as u32), &[self_value], field_lambda_ty);
            body = self.lower_drop_value_then(ctx, field_value, field_ty, body);
        }
        if let Some(witness) = witness {
            let label = self.demand(witness, theta);
            let fn_ref = self.p.func_ref(label);
            let cont = self.p.func("after_heap_deinit", void_ty, bot);
            self.p.set_body(cont, body);
            let cont_ref = self.p.func_ref(cont);
            let args_tuple = self.p.tuple(&[self_value, cont_ref]);
            body = self.p.app(fn_ref, args_tuple);
        }
        self.p.set_body(thunk, body);
        Some(thunk)
    }

    /// Ledger rule D: rvalue arguments carrying `'heap` handles die with
    /// the call — wrap the continuation to release their +1s once the call
    /// returns. `values[offset + i]` corresponds to `arg_exprs[i]`.
    pub(super) fn release_temps_then(
        &mut self,
        arg_exprs: &[&Expr],
        offset: usize,
        values: &[ExprId],
        ctx: &Ctx,
        k: ExprId,
    ) -> ExprId {
        let temp_indices: Vec<usize> = arg_exprs
            .iter()
            .enumerate()
            .filter(|(_, arg)| {
                self.rhs_is_rvalue(arg, ctx)
                    && self.contains_object_type(&self.checker_ty(arg, ctx))
            })
            .map(|(i, _)| offset + i)
            .collect();
        if temp_indices.is_empty() {
            return k;
        }
        let TyKind::Fn(result_ty, _) = *self.p.ty_kind(self.p.expr_ty(k)) else {
            return self.dead_end("call_continuation_not_a_function");
        };
        let bot = self.p.ty_bot();
        let relk = self.p.func("release_call_temps", result_ty, bot);
        let result = self.p.var(relk);
        let mut body = self.p.app(k, result);
        let void_ty = self.p.ty_void();
        for &index in &temp_indices {
            let release = self.p.primop(Op::RegionRelease, &[values[index]], void_ty);
            body = self.sequence_void_effect(release, body);
        }
        self.p.set_body(relk, body);
        self.p.func_ref(relk)
    }

    /// Ledger rule B: a `'heap` handle read from a place and embedded into
    /// a constructed value (tuple/variant/record element) gains +1 — the
    /// constructed rvalue then carries it, and its consumer (a claiming
    /// binding, a store, a temp release) accounts for it.
    pub(super) fn embed_acquires_then(
        &mut self,
        elems: &[&Expr],
        values: &[ExprId],
        ctx: &Ctx,
        mut body: ExprId,
    ) -> ExprId {
        let void_ty = self.p.ty_void();
        for (elem, &value) in elems.iter().zip(values.iter()) {
            if !self.rhs_is_rvalue(elem, ctx)
                && self.contains_object_type(&self.checker_ty(elem, ctx))
            {
                let acquire = self.p.primop(Op::RegionAcquire, &[value], void_ty);
                body = self.sequence_void_effect(acquire, body);
            }
        }
        body
    }

    /// Whether any element forces the impure path so rule-B acquires can
    /// be emitted (pure construction has no effect slot).
    pub(super) fn embeds_object_place_read(&mut self, elems: &[&Expr], ctx: &Ctx) -> bool {
        elems.iter().any(|elem| {
            !self.rhs_is_rvalue(elem, ctx) && self.contains_object_type(&self.checker_ty(elem, ctx))
        })
    }

    /// Declared `'heap` in any unit's catalog: values are object handles.
    pub(super) fn symbol_is_heap(&self, symbol: Symbol) -> bool {
        self.units.iter().any(|u| u.types.catalog.is_heap(symbol))
    }

    /// Witness selection (Wadler & Blott's instance method lookup, made
    /// static by monomorphization): a concrete head + protocol picks the
    /// conformance row; its witness function, or the protocol default body
    /// specialized at Self := head.
    pub(super) fn resolve_witness(
        &mut self,
        protocol: Symbol,
        requirement_or_witness: Symbol,
        label: String,
        head: &CheckTy,
        generics: &Theta,
    ) -> Option<(Label, Symbol, Theta)> {
        let head_for_witness = match head {
            CheckTy::Nominal(..) => head,
            CheckTy::Borrow(_, inner) => inner,
            _ => head,
        };
        let CheckTy::Nominal(head_symbol, head_args) = head_for_witness else {
            self.diagnostics.push(format!(
                "lowering: protocol dispatch on non-nominal head {head:?} (not yet supported)"
            ));
            return None;
        };
        let catalog = &self.units[self.entry].types.catalog;
        let conformance = catalog.conformances.get(&(*head_symbol, protocol)).cloned();

        if let Some(conformance) = conformance {
            // Bind the row's rigid params against the concrete head args —
            // the same binding the solver performed at discharge (instances
            // with contexts, Hall et al., TOPLAS 1996; the context itself
            // needs no re-check: the checker proved it).
            let mut row_theta = Theta::default();
            for (pattern, actual) in conformance.self_args.iter().zip(head_args) {
                crate::types::solve::bind_param_pattern(pattern, actual, &mut row_theta);
            }
            row_theta.extend(generics.iter().map(|(s, t)| (*s, t.clone())));
            if let Some(&witness) = conformance.witnesses.get(&label) {
                let target = self.demand(witness, row_theta.clone());
                return Some((target, witness, row_theta));
            }
            // Default body: specialize at Self := head, with the
            // conformance's associated bindings (substituted through the
            // row's params for conditional rows).
            let mut theta = Theta::default();
            theta.insert(protocol, head_for_witness.clone());
            for (assoc, ty) in &conformance.assoc {
                let bound = ty.substitute(&row_theta, &Default::default(), &Default::default());
                theta.insert(*assoc, bound);
            }
            theta.extend(generics.iter().map(|(s, t)| (*s, t.clone())));
            let target = self.demand(requirement_or_witness, theta.clone());
            return Some((target, requirement_or_witness, theta));
        }
        // No explicit row: an auto-derived protocol (today: Showable)
        // synthesizes its witness in λ_G — the checker discharged the
        // conformance structurally (`solve/conformance.rs::try_derive`).
        let derivable = self
            .units
            .iter()
            .any(|u| u.types.catalog.derivable.contains(&protocol));
        if derivable
            && label == "show"
            && let Some(synth) =
                self.demand_derived_show(protocol, requirement_or_witness, head_for_witness)
        {
            return Some((synth, requirement_or_witness, Theta::default()));
        }
        self.diagnostics.push(format!(
            "lowering: no conformance ({head_symbol}, {protocol}) for '{label}'"
        ));
        None
    }
}
