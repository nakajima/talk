use super::*;

impl<'a> Lowering<'a> {
    // ----- Match -------------------------------------------------------------

    /// Match compilation: bind the scrutinee to a pure value, then build
    /// the decision tree (Maranget, ML 2008 — `patterns.rs`).
    pub(super) fn lower_match(
        &mut self,
        scrutinee: &Expr,
        arms: &[MatchArm],
        scaffold_arms: Option<ScaffoldArms>,
        ctx: &Ctx,
        k: ExprId,
    ) -> ExprId {
        let scrutinee_check_ty = self.checker_ty(scrutinee, ctx);
        let scrutinee_borrowed = matches!(scrutinee_check_ty, CheckTy::Borrow(..));
        let pattern_scrutinee_ty = Self::borrow_erased_ty(scrutinee_check_ty.clone());
        // Ledger rule D analog: an rvalue scrutinee's carried +1 dies with
        // the match — release once the match delivers. (A call-result temp
        // is pure to read but still an rvalue.)
        let release_rvalue =
            self.rhs_is_rvalue(scrutinee, ctx) && self.contains_object_type(&scrutinee_check_ty);
        let release_wrapped = |this: &mut Self, value: ExprId, k: ExprId| {
            if !release_rvalue {
                return Some(k);
            }
            let bot = this.p.ty_bot();
            let TyKind::Fn(result_ty, _) = *this.p.ty_kind(this.p.expr_ty(k)) else {
                return None;
            };
            let relk = this.p.func("release_scrutinee", result_ty, bot);
            let result = this.p.var(relk);
            let deliver = this.p.app(k, result);
            let void_ty = this.p.ty_void();
            let release = this.p.primop(Op::RegionRelease, &[value], void_ty);
            let body = this.sequence_void_effect(release, deliver);
            this.p.set_body(relk, body);
            Some(this.p.func_ref(relk))
        };
        match self.try_pure(scrutinee, ctx) {
            Some(value) => {
                let Some(k) = release_wrapped(self, value, k) else {
                    return self.dead_end("match_continuation_not_a_function");
                };
                patterns::compile_match(
                    self,
                    value,
                    pattern_scrutinee_ty,
                    arms,
                    scaffold_arms,
                    scrutinee_borrowed,
                    ctx,
                    k,
                )
            }
            None => {
                let scrutinee_ty = self.expr_lambda_ty(scrutinee, ctx);
                let bot = self.p.ty_bot();
                let cont = self.p.func("scrut", scrutinee_ty, bot);
                let value = self.p.var(cont);
                let Some(k) = release_wrapped(self, value, k) else {
                    return self.dead_end("match_continuation_not_a_function");
                };
                let body = patterns::compile_match(
                    self,
                    value,
                    pattern_scrutinee_ty,
                    arms,
                    scaffold_arms,
                    scrutinee_borrowed,
                    ctx,
                    k,
                );
                self.p.set_body(cont, body);
                let cont_ref = self.p.func_ref(cont);
                self.lower_expr(scrutinee, ctx, cont_ref)
            }
        }
    }

    /// Pure expressions evaluate without continuations: literals, bound
    /// variables, field reads on pure receivers, and @_ir splices over
    /// pure operands.
    pub(super) fn try_pure(&mut self, expr: &Expr, ctx: &Ctx) -> Option<ExprId> {
        // An auto-cloned value must retain its buffers — an effect — so it
        // takes the continuation path (`lower_expr` wraps k with the retains).
        if expr.ownership.auto_clone {
            return None;
        }
        if let Some(pack) = self.existential_pack_at(expr.existential_pack.as_ref(), ctx) {
            if let CheckTy::Any { protocol, .. } = &pack.payload
                && protocol.protocol
                    == self
                        .any_protocol(&pack.existential)
                        .unwrap_or(protocol.protocol)
            {
                return self.try_pure_unpacked(expr, ctx);
            }
            let payload = self.try_pure_unpacked(expr, ctx)?;
            return self.existential_pack_value(expr.id, payload, &pack, ctx);
        }
        self.try_pure_unpacked(expr, ctx)
    }

    pub(super) fn try_pure_unpacked(&mut self, expr: &Expr, ctx: &Ctx) -> Option<ExprId> {
        match &expr.kind {
            ExprKind::Lit(hir::Literal::Int(text)) => Some(self.p.int(text.parse().ok()?)),
            ExprKind::Lit(hir::Literal::Float(text)) => Some(self.p.float(text.parse().ok()?)),
            ExprKind::Lit(hir::Literal::Bool(value)) => Some(self.p.bool(*value)),
            // A string literal is a String record over interned static
            // bytes: {storage, length, capacity}.
            ExprKind::Lit(hir::Literal::String(text)) => {
                // The lexer rejects invalid escapes, so this only fails on
                // literals that never went through it.
                let Ok(unescaped) = crate::parsing::lexing::unescape(text) else {
                    self.diagnostics
                        .push("lowering: string literal with invalid escape".into());
                    return None;
                };
                let bytes = unescaped.into_bytes();
                let offset = self.intern_static(&bytes);
                let CheckTy::Nominal(string_symbol, _) =
                    Self::borrow_erased_ty(self.checker_ty(expr, ctx))
                else {
                    self.diagnostics
                        .push("lowering: string literal with a non-nominal type".into());
                    return None;
                };
                let ptr_ty = self.p.ty_ptr();
                let base = self.p.constant(Const::StaticPtr(offset), ptr_ty);
                let len = self.p.int(bytes.len() as i64);
                let ty = self.p.ty(TyKind::Boxed(string_symbol));
                let Some(storage) = self.string_storage_value(string_symbol, base) else {
                    return Some(self.dead_end("invalid_string_storage_wrapper"));
                };
                Some(
                    self.p
                        .primop(Op::RecordNew(string_symbol), &[storage, len, len], ty),
                )
            }
            // Field read on a pure receiver: GetField (records are pure
            // values). A member that resolves to a payload-less enum case
            // (`.none`, `Optional.none`) is a variant value instead.
            ExprKind::Proj(receiver, ..) => {
                let receiver_value = self.try_pure(receiver, ctx)?;
                self.field_read(expr, receiver, receiver_value, ctx)
            }
            ExprKind::Member(receiver, _) => {
                let receiver = receiver.as_deref()?;
                let receiver_value = self.try_pure(receiver, ctx)?;
                self.field_read(expr, receiver, receiver_value, ctx)
            }
            // Variant construction over pure payloads (`.some(1)`,
            // `Maybe.definitely(x)`): pure, exactly like RecordNew — unless
            // a payload embeds a `'heap` place read (the impure path emits
            // the ledger acquire).
            ExprKind::Con {
                enum_symbol,
                tag,
                variant_symbol,
                args,
            } => {
                let arg_exprs: Vec<&Expr> = args.iter().collect();
                if self.embeds_object_place_read(&arg_exprs, ctx) {
                    return None;
                }
                let mut payloads = Vec::with_capacity(args.len());
                for arg in args {
                    payloads.push(self.try_pure(arg, ctx)?);
                }
                Some(self.variant_new_for_expr(
                    VariantSite {
                        node: expr.id,
                        instantiation: expr.instantiation.clone(),
                    },
                    *enum_symbol,
                    *tag,
                    *variant_symbol,
                    &payloads,
                    ctx,
                ))
            }
            // A record literal over pure fields: a tuple in the row's
            // canonical (label-sorted) field order (unless a `'heap` place
            // read embeds — the impure path emits the ledger acquire).
            ExprKind::RecordLiteral { fields, spread } => {
                if spread.is_some() {
                    return None;
                }
                let field_exprs: Vec<&Expr> = fields.iter().map(|f| &f.value).collect();
                if self.embeds_object_place_read(&field_exprs, ctx) {
                    return None;
                }
                let order = self.record_field_order(expr, fields, ctx)?;
                let mut values = Vec::with_capacity(fields.len());
                for field in fields {
                    values.push(self.try_pure(&field.value, ctx)?);
                }
                let items: Vec<ExprId> = order.iter().map(|&i| values[i]).collect();
                Some(self.p.tuple(&items))
            }
            ExprKind::Temp(temp) => ctx.temps.get(temp).copied(),
            ExprKind::Variable(name) => {
                let symbol = name.symbol().ok()?;
                if let Some(&binding) = ctx.env.get(&symbol) {
                    return Some(match binding {
                        Binding::Value(value) => value,
                        Binding::Cell(cell) => {
                            let TyKind::Cell(inner) = *self.p.ty_kind(self.p.expr_ty(cell)) else {
                                return None;
                            };
                            self.p.primop(Op::CellGet, &[cell], inner)
                        }
                    });
                }
                // A mutable top-level binding: read its registered cell
                // (a free variable of main; closure conversion carries it).
                if let Some(&cell) = self.top_level_cells.get(&symbol) {
                    let TyKind::Cell(inner) = *self.p.ty_kind(self.p.expr_ty(cell)) else {
                        return None;
                    };
                    return Some(self.p.primop(Op::CellGet, &[cell], inner));
                }
                // A function-typed global used as a value: demand its
                // specialization (instantiation recorded at this node).
                if self.sources.contains_key(&symbol) {
                    let theta = self.instantiation_at(expr.instantiation.as_ref(), ctx);
                    let label = self.demand(symbol, theta.clone())?;
                    let cap_entries = self.cap_entries_of(symbol, &theta);
                    if cap_entries.is_empty() {
                        return Some(self.p.func_ref(label));
                    }
                    return self.eta_expand_effectful_value(symbol, label, &cap_entries, ctx);
                }
                // A constant global (`public let STDOUT_FD: Int = 0`):
                // inline its literal value (whole-program constant
                // propagation; non-literal globals await M8 statics).
                if let Some(&(unit, rhs)) = self.globals.get(&symbol) {
                    let global_ctx = Ctx {
                        unit,
                        owner: None,
                        theta: Theta::default(),
                        env: FxHashMap::default(),
                        local_evidence: FxHashMap::default(),
                        temps: FxHashMap::default(),
                        ret_k: ctx.ret_k,
                        tail_k: ctx.ret_k,
                        raw_ret_k: ctx.raw_ret_k,
                        resume_k: None,
                        top_level: false,
                        caps: FxHashMap::default(),
                        cap_templates: FxHashMap::default(),
                        params: vec![],
                        loops: vec![],
                        drop_stack: vec![],
                        drop_flags: FxHashMap::default(),
                        initializing_self: None,
                        cellable: FxHashSet::default(),
                    };
                    return self.try_pure(rhs, &global_ctx);
                }
                None
            }
            // A function literal is a value: its λ_G Func reference
            // (captures are its free variables).
            ExprKind::Func(func) => self.lower_func_value(expr, func, ctx),
            // The unit literal `()`.
            ExprKind::Tuple(items) if items.is_empty() => Some(self.p.void()),
            ExprKind::InlineIR(instruction) => self.splice(instruction, ctx),
            // A tuple literal over pure items (unless a `'heap` place read
            // embeds — the impure path emits the ledger acquire).
            ExprKind::Tuple(items) => {
                let item_exprs: Vec<&Expr> = items.iter().collect();
                if self.embeds_object_place_read(&item_exprs, ctx) {
                    return None;
                }
                let mut values = Vec::with_capacity(items.len());
                for item in items {
                    values.push(self.try_pure(item, ctx)?);
                }
                Some(self.p.tuple(&values))
            }
            _ => None,
        }
    }

    pub(super) fn existential_pack_at(
        &self,
        pack: Option<&crate::types::output::ExistentialPack>,
        ctx: &Ctx,
    ) -> Option<crate::types::output::ExistentialPack> {
        let pack = pack?;
        let existential =
            pack.existential
                .substitute(&ctx.theta, &Default::default(), &Default::default());
        let payload = pack
            .payload
            .substitute(&ctx.theta, &Default::default(), &Default::default());
        Some(crate::types::output::ExistentialPack {
            existential: self.normalize_check_ty(existential, ctx.unit),
            payload: self.normalize_check_ty(payload, ctx.unit),
        })
    }

    pub(super) fn any_protocol(&self, ty: &CheckTy) -> Option<Symbol> {
        match ty {
            CheckTy::Any { protocol, .. } => Some(protocol.protocol),
            _ => None,
        }
    }

    /// The drop witness packed into every existential: `λ(payload, k)`
    /// dropping the payload's owned parts (deinit dispatch included). A
    /// uniform last slot in the witness table, so layout stays index-stable.
    pub(super) fn existential_drop_thunk(&mut self, ctx: &Ctx, payload_ty: &CheckTy) -> Label {
        let payload_lambda_ty = self.map_ty(payload_ty);
        let void_ty = self.p.ty_void();
        let bot = self.p.ty_bot();
        let k_ty = self.p.ty_fn(void_ty, bot);
        let dom = self.p.ty_tuple(&[payload_lambda_ty, k_ty]);
        let thunk = self.p.func("drop_payload", dom, bot);
        // The thunk escapes into the witness table: it must become a chunk.
        self.escaping.insert(thunk);
        let vthunk = self.p.var(thunk);
        let payload = self.p.extract(vthunk, 0);
        let k = self.p.extract(vthunk, 1);
        let unit_value = self.p.void();
        let finish = self.p.app(k, unit_value);
        let body = match payload_ty {
            // A type-parameter payload's drop is unknowable here (generic
            // repack); the thunk is a no-op — deferred, see plan notes.
            CheckTy::Param(_) => finish,
            _ => self.lower_drop_value_then(ctx, payload, payload_ty, finish),
        };
        self.p.set_body(thunk, body);
        thunk
    }

    pub(super) fn existential_pack_value(
        &mut self,
        node: crate::node_id::NodeID,
        payload: ExprId,
        pack: &crate::types::output::ExistentialPack,
        ctx: &Ctx,
    ) -> Option<ExprId> {
        let CheckTy::Any { protocol, assoc } = &pack.existential else {
            self.diagnostics
                .push("lowering: existential pack target is not an existential".into());
            return None;
        };
        if let CheckTy::Any {
            protocol: payload_protocol,
            ..
        } = &pack.payload
        {
            if payload_protocol == protocol {
                return Some(payload);
            }
            self.diagnostics.push(
                "lowering: existential upcast/repack reached lowering after type checking".into(),
            );
            return None;
        }
        if let CheckTy::Param(param) = &pack.payload {
            return self.existential_pack_from_local_evidence(
                protocol.protocol,
                assoc,
                *param,
                payload,
                ctx,
            );
        }

        let requirements = self.units[ctx.unit]
            .types
            .catalog
            .requirements_for_conformance(protocol);
        let mut values = Vec::with_capacity(requirements.len() + 1);
        values.push(payload);
        for (owner, label, requirement) in requirements {
            let witness = self.existential_witness_wrapper(
                protocol.protocol,
                assoc,
                owner.protocol,
                &label,
                &requirement,
                &pack.payload,
                ctx,
                node,
            )?;
            values.push(witness);
        }
        let drop_thunk = self.existential_drop_thunk(ctx, &pack.payload);
        values.push(self.p.func_ref(drop_thunk));
        let ty = self.p.ty(TyKind::Existential(protocol.protocol));
        Some(
            self.p
                .primop(Op::ExistentialPack(protocol.protocol), &values, ty),
        )
    }

    pub(super) fn existential_pack_from_local_evidence(
        &mut self,
        protocol: Symbol,
        assoc: &[(Symbol, CheckTy)],
        param: Symbol,
        payload: ExprId,
        ctx: &Ctx,
    ) -> Option<ExprId> {
        let evidence = self.local_evidence_for(ctx, param, protocol)?;
        let target_requirements = self.units[ctx.unit]
            .types
            .catalog
            .requirements_for_conformance(&ProtocolRef::bare(protocol));
        let source_requirements = self.units[ctx.unit]
            .types
            .catalog
            .requirements_for_conformance(&ProtocolRef::bare(evidence.protocol));
        let mut values = Vec::with_capacity(target_requirements.len() + 1);
        values.push(payload);
        for (owner, label, requirement) in target_requirements {
            let source_index = source_requirements
                .iter()
                .position(|(_, _, source)| source.symbol == requirement.symbol)?;
            let _signature = self.erased_requirement_signature(
                protocol,
                assoc,
                owner.protocol,
                &requirement,
                ctx.unit,
            )?;
            values.push(self.p.extract(evidence.table, source_index as u32));
            let _ = label;
        }
        let payload_ty = CheckTy::Param(param);
        let drop_thunk = self.existential_drop_thunk(ctx, &payload_ty);
        values.push(self.p.func_ref(drop_thunk));
        let ty = self.p.ty(TyKind::Existential(protocol));
        Some(self.p.primop(Op::ExistentialPack(protocol), &values, ty))
    }

    pub(super) fn local_evidence_for(
        &self,
        ctx: &Ctx,
        param: Symbol,
        protocol: Symbol,
    ) -> Option<EvidenceBinding> {
        if let Some(binding) = ctx.local_evidence.get(&(param, protocol)).copied() {
            return Some(binding);
        }
        if let Some((_, binding)) =
            ctx.local_evidence
                .iter()
                .find(|((candidate_param, candidate_protocol), _)| {
                    *candidate_param == param
                        && self.units[ctx.unit].types.catalog.bounds_satisfy(
                            &[ProtocolRef::bare(*candidate_protocol)],
                            &ProtocolRef::bare(protocol),
                        )
                })
        {
            return Some(*binding);
        }
        let candidates: Vec<EvidenceBinding> = ctx
            .local_evidence
            .iter()
            .filter(|((_, candidate_protocol), _)| {
                self.units[ctx.unit].types.catalog.bounds_satisfy(
                    &[ProtocolRef::bare(*candidate_protocol)],
                    &ProtocolRef::bare(protocol),
                )
            })
            .map(|(_, binding)| *binding)
            .collect();
        match candidates.as_slice() {
            [single] => Some(*single),
            _ => None,
        }
    }

    pub(super) fn evidence_table_for_ty(
        &mut self,
        protocol: &ProtocolRef,
        payload_ty: &CheckTy,
        ctx: &Ctx,
        node: crate::node_id::NodeID,
    ) -> Option<ExprId> {
        if let CheckTy::Param(param) = payload_ty
            && let Some(evidence) = self.local_evidence_for(ctx, *param, protocol.protocol)
        {
            return Some(evidence.table);
        }
        let assoc = self.assoc_bindings_for_concrete(protocol, payload_ty, ctx.unit);
        let requirements = self.units[ctx.unit]
            .types
            .catalog
            .requirements_for_conformance(protocol);
        let mut witnesses = Vec::with_capacity(requirements.len());
        for (owner, label, requirement) in requirements {
            let witness = self.existential_witness_wrapper(
                protocol.protocol,
                &assoc,
                owner.protocol,
                &label,
                &requirement,
                payload_ty,
                ctx,
                node,
            )?;
            witnesses.push(witness);
        }
        Some(self.p.tuple(&witnesses))
    }

    pub(super) fn evidence_table_ty(
        &mut self,
        protocol: Symbol,
        assoc: &[(Symbol, CheckTy)],
        unit: usize,
    ) -> TyId {
        let requirements = self.units[unit]
            .types
            .catalog
            .requirements_for_conformance(&ProtocolRef::bare(protocol));
        let witness_tys: Vec<TyId> = requirements
            .into_iter()
            .filter_map(|(owner, _, requirement)| {
                let signature = self.erased_requirement_signature(
                    protocol,
                    assoc,
                    owner.protocol,
                    &requirement,
                    unit,
                )?;
                Some(self.map_ty(&signature))
            })
            .collect();
        self.p.ty_tuple(&witness_tys)
    }

    pub(super) fn assoc_bindings_for_concrete(
        &self,
        protocol: &ProtocolRef,
        payload_ty: &CheckTy,
        unit: usize,
    ) -> Vec<(Symbol, CheckTy)> {
        let required = self.units[unit]
            .types
            .catalog
            .associated_types_in_ref(protocol);
        let CheckTy::Nominal(head, args) = payload_ty else {
            return required
                .into_iter()
                .map(|(_, _, symbol)| (symbol, CheckTy::Param(symbol)))
                .collect();
        };
        let Some(conformance) = self.units[unit]
            .types
            .catalog
            .matching_conformances(*head, args, protocol)
            .into_iter()
            .next()
        else {
            return required
                .into_iter()
                .map(|(_, _, symbol)| (symbol, CheckTy::Param(symbol)))
                .collect();
        };
        let row_theta = conformance.substitution;
        required
            .into_iter()
            .map(|(_, _, symbol)| {
                let ty = conformance
                    .conformance
                    .assoc
                    .get(&symbol)
                    .map(|ty| ty.substitute(&row_theta, &Default::default(), &Default::default()))
                    .unwrap_or(CheckTy::Param(symbol));
                (symbol, ty)
            })
            .collect()
    }

    #[allow(clippy::too_many_arguments)]
    pub(super) fn existential_witness_wrapper(
        &mut self,
        root_protocol: Symbol,
        assoc: &[(Symbol, CheckTy)],
        owner: Symbol,
        label: &str,
        requirement: &crate::types::catalog::Requirement,
        payload_ty: &CheckTy,
        ctx: &Ctx,
        node: crate::node_id::NodeID,
    ) -> Option<ExprId> {
        let signature =
            self.erased_requirement_signature(root_protocol, assoc, owner, requirement, ctx.unit)?;
        let CheckTy::Func(params, ret, _) = signature else {
            self.diagnostics
                .push("lowering: existential requirement is not a function".into());
            return None;
        };
        let mut dom_items: Vec<TyId> = params.iter().map(|param| self.map_ty(param)).collect();
        let ret_ty = self.map_ty(&ret);
        let bot = self.p.ty_bot();
        let ret_k_ty = self.p.ty_fn(ret_ty, bot);
        dom_items.push(ret_k_ty);
        let dom = self.p.ty_tuple(&dom_items);
        let wrapper = self.p.func(
            &format!("existential_{}_{}", root_protocol, label),
            dom,
            bot,
        );
        self.escaping.insert(wrapper);

        let self_var = self.p.var(wrapper);
        let erased_self = self.p.extract(self_var, 0);
        let payload_lambda_ty = self.map_ty(payload_ty);
        let payload = self
            .p
            .primop(Op::ExistentialPayload, &[erased_self], payload_lambda_ty);
        let mut args = Vec::with_capacity(params.len() + 1);
        args.push(payload);
        for index in 1..params.len() {
            args.push(self.p.extract(self_var, index as u32));
        }
        let ret_k = self.p.extract(self_var, params.len() as u32);
        args.push(ret_k);
        let arg_tuple = self.p.tuple(&args);
        let Some((target, _, _)) = self.resolve_witness(
            ProtocolRef::bare(owner),
            requirement.symbol,
            label.to_string(),
            payload_ty,
            &Theta::default(),
        ) else {
            self.diagnostics.push(format!(
                "lowering: cannot build existential witness for {label} at {:?}",
                node
            ));
            return None;
        };
        let target_ref = self.p.func_ref(target);
        let body = self.p.app(target_ref, arg_tuple);
        self.p.set_body(wrapper, body);
        Some(self.p.func_ref(wrapper))
    }

    pub(super) fn erased_requirement_signature(
        &mut self,
        root_protocol: Symbol,
        assoc: &[(Symbol, CheckTy)],
        owner: Symbol,
        requirement: &crate::types::catalog::Requirement,
        unit: usize,
    ) -> Option<CheckTy> {
        let mut tys = Theta::default();
        tys.insert(
            owner,
            CheckTy::Any {
                protocol: ProtocolRef::bare(root_protocol),
                assoc: assoc.to_vec(),
            },
        );
        for (assoc_symbol, ty) in assoc {
            tys.insert(*assoc_symbol, ty.clone());
        }
        let sig = self
            .units
            .iter()
            .find_map(|u| u.types.schemes.get(&requirement.symbol))
            .map(|scheme| scheme.ty.clone())?;
        let signature = sig.substitute(&tys, &Default::default(), &Default::default());
        Some(self.normalize_check_ty(signature, unit))
    }

    pub(super) fn existential_requirement_index(
        &self,
        protocol: Symbol,
        label: &str,
        requirement_symbol: Symbol,
        unit: usize,
    ) -> Option<usize> {
        self.units[unit]
            .types
            .catalog
            .requirements_for_conformance(&ProtocolRef::bare(protocol))
            .iter()
            .position(|(_, candidate_label, requirement)| {
                candidate_label == label && requirement.symbol == requirement_symbol
            })
    }

    /// Branch on a condition expression: br(cond, then_thunk, else_thunk)
    /// (the paper's br_⊥, §2.2).
    pub(super) fn branch(
        &mut self,
        cond: &Expr,
        then_body: ExprId,
        else_body: ExprId,
        ctx: &Ctx,
    ) -> ExprId {
        // The condition itself may need CPS (e.g. `n <= 1` is a call).
        match self.try_pure(cond, ctx) {
            Some(cv) => self.branch_value(cv, then_body, else_body),
            None => {
                let bot = self.p.ty_bot();
                let bool_ty = self.p.ty_bool();
                let ck = self.p.func("cond", bool_ty, bot);
                let cv = self.p.var(ck);
                let body = self.branch_value(cv, then_body, else_body);
                self.p.set_body(ck, body);
                let ck_ref = self.p.func_ref(ck);
                self.lower_expr(cond, ctx, ck_ref)
            }
        }
    }

    /// br over an already-lowered condition value.
    pub(super) fn branch_value(
        &mut self,
        cond: ExprId,
        then_body: ExprId,
        else_body: ExprId,
    ) -> ExprId {
        let void_ty = self.p.ty_void();
        let bot = self.p.ty_bot();
        let then_fn = self.p.func("then", void_ty, bot);
        self.p.set_body(then_fn, then_body);
        let else_fn = self.p.func("else", void_ty, bot);
        self.p.set_body(else_fn, else_body);
        let then_ref = self.p.func_ref(then_fn);
        let else_ref = self.p.func_ref(else_fn);
        let thunk_ty = self.p.ty_fn(void_ty, bot);
        self.p.br(cond, then_ref, else_ref, thunk_ty)
    }
}
