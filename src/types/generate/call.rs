use super::*;

impl<'s, 'a> BodyChecker<'s, 'a> {
    // ----- Calls ---------------------------------------------------------

    /// The shared tail of every call: callee type against arguments, the
    /// callee's latent effects unified into the ambient row (Koka's
    /// application rule).
    pub(super) fn finish_call(
        &mut self,
        node: NodeID,
        callee_ty: Ty,
        args: &[CallArg],
        trailing_block: &Option<Block>,
        ctx: &Ctx,
    ) -> Ty {
        self.finish_call_with_result_origin(node, node, callee_ty, args, trailing_block, ctx)
    }

    fn finish_call_with_result_origin(
        &mut self,
        node: NodeID,
        result_origin: NodeID,
        callee_ty: Ty,
        args: &[CallArg],
        trailing_block: &Option<Block>,
        ctx: &Ctx,
    ) -> Ty {
        let arg_count = args.len() + usize::from(trailing_block.is_some());

        match self.store.shallow(&callee_ty) {
            Ty::Func(params, ret, eff) => {
                if params.len() != arg_count {
                    self.diagnostics.errors.push((
                        TypeError::ArityMismatch {
                            expected: params.len(),
                            found: arg_count,
                        },
                        node,
                    ));
                    return Ty::Error;
                }
                for (arg, param) in args.iter().zip(&params) {
                    self.check_expr(&arg.value, param, CtReason::Apply, ctx);
                }
                if let Some(block) = trailing_block {
                    let block_ty = self.infer_closure_block(block, ctx);
                    self.emit_eq(
                        params[args.len()].clone(),
                        block_ty,
                        block.id,
                        CtReason::Apply,
                    );
                }
                self.emit_eff_eq(eff, ctx.eff.clone(), node);
                *ret
            }
            Ty::Var(_) => {
                let mut arg_tys: Vec<Ty> = args
                    .iter()
                    .map(|arg| self.infer_expr(&arg.value, ctx))
                    .collect();
                if let Some(block) = trailing_block {
                    arg_tys.push(self.infer_closure_block(block, ctx));
                }
                let ret = Ty::Var(self.store.fresh_ty(self.level, result_origin));
                let expected = Ty::Func(arg_tys, Box::new(ret.clone()), ctx.eff.clone());
                self.emit_eq(callee_ty, expected, node, CtReason::Apply);
                ret
            }
            Ty::Error => Ty::Error,
            other => {
                let found = self.store.render(&other);
                self.diagnostics
                    .errors
                    .push((TypeError::NotAFunction { found }, node));
                Ty::Error
            }
        }
    }

    /// `recv.label(args)`: a HasMember predicate plus the ordinary call
    /// tail. The member variable carries the call's arity, so an in-flight
    /// method of the same group resolves once its signature variable does.
    pub(super) fn infer_member_call(
        &mut self,
        expr: &Expr,
        callee: &Expr,
        receiver: &Expr,
        label: &Label,
        args: &[CallArg],
        trailing_block: &Option<Block>,
        ctx: &Ctx,
    ) -> Ty {
        let receiver_ty = self.infer_expr(receiver, ctx);
        let member = Ty::Var(self.store.fresh_ty(self.level, callee.id));
        self.artifacts.node_types.insert(callee.id, member.clone());
        let result = self.finish_call_with_result_origin(
            expr.id,
            callee.id,
            member.clone(),
            args,
            trailing_block,
            ctx,
        );
        self.wanteds.push(Constraint::HasMember {
            receiver: receiver_ty,
            label: label.clone(),
            member,
            origin: CtOrigin::new(callee.id, CtReason::Apply),
        });
        result
    }

    /// `Person(args)`: pick an initializer by arity, equate its
    /// self-prepended signature against a fresh instantiation of the struct.
    pub(super) fn infer_construction(
        &mut self,
        expr: &Expr,
        callee: &Expr,
        name: &Name,
        type_args: &[TypeAnnotation],
        args: &[CallArg],
        trailing_block: &Option<Block>,
        ctx: &Ctx,
    ) -> Ty {
        let Ok(symbol) = name.symbol() else {
            return Ty::Error;
        };
        let Some(info) = self.catalog.structs.get(&symbol).cloned() else {
            if self.catalog.enums.contains_key(&symbol) {
                self.unsupported(expr.id, "constructing an enum directly (use a case)");
            } else {
                self.unsupported(expr.id, "constructing this type");
            }
            return Ty::Error;
        };

        let theta: Vec<Ty> = info
            .params
            .iter()
            .map(|_| Ty::Var(self.store.fresh_ty(self.level, expr.id)))
            .collect();
        if !info.params.is_empty() {
            self.record_instantiation(expr.id, &info.params, &theta);
        }
        // `ArrayIterator<Element>(array: self)`: explicit type arguments pin
        // the instantiation positionally.
        for (annotation, target) in type_args.iter().zip(&theta) {
            let ty = self.lower_annotation(annotation);
            self.emit_eq(target.clone(), ty, annotation.id, CtReason::Annotation);
        }
        // Closure-field effect rows instantiate per construction (one
        // fresh open row per implicit effect param) and ride the head as
        // `Ty::Eff` arguments — THIS instance's rows, recovered at member
        // reads, contaminating nothing else.
        let eff_tails: FxHashMap<Symbol, EffTail> = info
            .eff_params
            .iter()
            .map(|&param| (param, EffTail::Var(self.store.fresh_eff(self.level, expr.id))))
            .collect();
        let mut head_args = theta.clone();
        head_args.extend(info.eff_params.iter().map(|param| {
            Ty::Eff(EffectRow {
                effects: vec![],
                tail: Some(eff_tails[param].clone()),
            })
        }));
        let self_ty = Ty::Nominal(symbol, head_args);
        self.emit_nominal_well_formedness(symbol, &theta, expr.id);

        let arg_count = args.len() + usize::from(trailing_block.is_some());
        let init = info
            .inits
            .iter()
            .copied()
            .find(|init| self.callable_arity(*init) == Some(arg_count + 1))
            .or_else(|| info.inits.first().copied());
        let Some(init) = init else {
            self.unsupported(expr.id, "constructing a type with no initializer");
            return Ty::Error;
        };
        self.artifacts
            .member_resolutions
            .insert(callee.id, MemberResolution::Direct(init));

        let substitution = param_subst(&info.params, &theta);
        let signature = self.lookup_symbol_ty(init, expr.id).substitute(
            &substitution,
            &Default::default(),
            &Default::default(),
        );

        match self.store.shallow(&signature) {
            Ty::Func(params, _ret, eff) => {
                // The memberwise init's param types are copies of the
                // field annotations with their OWN row variables; pin
                // them to this construction's instance rows so the stored
                // closure's row is the row reads recover.
                if !info.eff_params.is_empty() && params.len() == info.fields.len() + 1 {
                    for (param, (_, field_ty)) in params[1..].iter().zip(info.fields.values()) {
                        let field_ty =
                            field_ty.substitute(&substitution, &eff_tails, &Default::default());
                        self.emit_eq(param.clone(), field_ty, expr.id, CtReason::Apply);
                    }
                }
                if params.len() != arg_count + 1 {
                    self.diagnostics.errors.push((
                        TypeError::ArityMismatch {
                            expected: params.len().saturating_sub(1),
                            found: arg_count,
                        },
                        expr.id,
                    ));
                    return Ty::Error;
                }
                self.emit_immediate_argument_eq(
                    &params[0],
                    self_ty.clone(),
                    expr.id,
                    CtReason::Apply,
                );
                for (arg, param) in args.iter().zip(&params[1..]) {
                    self.check_expr(&arg.value, param, CtReason::Apply, ctx);
                }
                if let Some(block) = trailing_block {
                    let block_ty = self.infer_closure_block(block, ctx);
                    self.emit_eq(
                        params[args.len() + 1].clone(),
                        block_ty,
                        block.id,
                        CtReason::Apply,
                    );
                }
                self.emit_eff_eq(eff, ctx.eff.clone(), expr.id);
                self.artifacts.node_types.insert(
                    callee.id,
                    Ty::Func(
                        params[1..].to_vec(),
                        Box::new(self_ty.clone()),
                        EffectRow::pure(),
                    ),
                );
                self_ty
            }
            Ty::Var(_) => {
                // In-flight initializer: the struct is being constructed
                // within its own binding group.
                if !info.params.is_empty() {
                    self.unsupported(
                        expr.id,
                        "constructing a generic type within its own binding group",
                    );
                    return Ty::Error;
                }
                let mut arg_tys: Vec<Ty> = vec![self_ty.clone()];
                arg_tys.extend(args.iter().map(|arg| self.infer_expr(&arg.value, ctx)));
                if let Some(block) = trailing_block {
                    arg_tys.push(self.infer_closure_block(block, ctx));
                }
                // Record the constructor node's function type, as the `Ty::Func` arm
                // does, so every expression has a type.
                self.artifacts.node_types.insert(
                    callee.id,
                    Ty::Func(
                        arg_tys[1..].to_vec(),
                        Box::new(self_ty.clone()),
                        EffectRow::pure(),
                    ),
                );
                let expected = Ty::Func(arg_tys, Box::new(self_ty.clone()), ctx.eff.clone());
                self.emit_eq(signature, expected, expr.id, CtReason::Apply);
                self_ty
            }
            Ty::Error => Ty::Error,
            other => {
                let found = self.store.render(&other);
                self.diagnostics
                    .errors
                    .push((TypeError::NotAFunction { found }, expr.id));
                Ty::Error
            }
        }
    }

    // ----- Member resolution ----------------------------------------------
    // Value-receiver member access is a HasMember predicate solved in
    // solve/. Only TYPE members (Constructor receivers) resolve here.

    /// Resolve `Type.label`: enum variants (constructors, or bare values for
    /// payload-less cases), protocol requirements (the protocol-static form
    /// operators desugar to: `Add.add(lhs, rhs)`), and static methods.
    pub(super) fn resolve_type_member(
        &mut self,
        symbol: Symbol,
        label: &Label,
        node: NodeID,
    ) -> Option<Ty> {
        let label_str = label.to_string();

        if let Some(info) = self.catalog.enums.get(&symbol).cloned() {
            let variant = info.variants.get(&label_str)?.clone();
            let theta: Vec<Ty> = info
                .params
                .iter()
                .map(|_| Ty::Var(self.store.fresh_ty(self.level, node)))
                .collect();
            self.artifacts
                .member_resolutions
                .insert(node, MemberResolution::Direct(variant.symbol));
            let substitution = param_subst(&info.params, &theta);
            let instantiation = self.instantiate_variant(&variant, substitution, node);
            self.record_variant_instantiation(node, &instantiation);
            self.emit_variant_predicates(&instantiation, node);
            self.emit_nominal_well_formedness_for_ty(&instantiation.result_type, node);
            if instantiation.argument_types.is_empty() {
                return Some(instantiation.result_type);
            }
            let eff = EffectRow::open(self.store.fresh_eff(self.level, node));
            return Some(Ty::Func(
                instantiation.argument_types,
                Box::new(instantiation.result_type),
                eff,
            ));
        }

        // Protocol-static dispatch: `P.requirement(self, args...)`. The full
        // self-prepended signature is returned; Self is a fresh variable
        // constrained to conform, pinned by the first argument.
        if self.catalog.protocols.contains_key(&symbol) {
            let (owner, requirement) = self.catalog.requirement_in(symbol, &label_str)?;
            let requirement = requirement.clone();
            // The requirement's type is its scheme: freshen method-level
            // generics (recorded for the lowerer's θ) and every effect
            // row per use, like any scheme instantiation.
            let scheme = self.schemes.get(&requirement.symbol)?.clone();
            let assoc_symbols: Vec<Symbol> = self
                .catalog
                .protocols
                .get(&owner)
                .map(|i| i.assoc.values().copied().collect())
                .unwrap_or_default();

            let self_var = Ty::Var(self.store.fresh_ty(self.level, node));
            let mut tys: FxHashMap<Symbol, Ty> = assoc_symbols
                .iter()
                .map(|a| (*a, Ty::Proj(Box::new(self_var.clone()), owner, *a)))
                .collect();
            tys.insert(owner, self_var.clone());
            for param in &scheme.params {
                let var = Ty::Var(self.store.fresh_ty(self.level, node));
                self.artifacts
                    .instantiations
                    .entry(node)
                    .or_default()
                    .push((param.symbol, var.clone()));
                tys.insert(param.symbol, var);
            }
            let mut effs = FxHashMap::default();
            for param in &scheme.eff_params {
                effs.insert(*param, EffTail::Var(self.store.fresh_eff(self.level, node)));
            }
            for predicate in &scheme.predicates {
                self.wanteds.push(
                    predicate
                        .substitute(&tys, &effs, &Default::default())
                        .into_constraint(CtOrigin::new(node, CtReason::Apply)),
                );
            }
            let signature = scheme.ty.substitute(&tys, &effs, &Default::default());

            self.wanteds.push(Constraint::Conforms {
                ty: self_var,
                protocol: owner,
                origin: CtOrigin::new(node, CtReason::Apply),
            });
            self.artifacts.member_resolutions.insert(
                node,
                MemberResolution::ViaConformance {
                    protocol: owner,
                    witness: requirement.symbol,
                },
            );
            return Some(signature);
        }

        if let Some(info) = self.catalog.structs.get(&symbol).cloned()
            && let Some(&method) = info.statics.get(&label_str)
        {
            let theta: Vec<Ty> = info
                .params
                .iter()
                .map(|_| Ty::Var(self.store.fresh_ty(self.level, node)))
                .collect();
            if !info.params.is_empty() {
                self.record_instantiation(node, &info.params, &theta);
            }
            let substitution = param_subst(&info.params, &theta);
            let signature = self.lookup_symbol_ty(method, node).substitute(
                &substitution,
                &Default::default(),
                &Default::default(),
            );
            self.artifacts
                .member_resolutions
                .insert(node, MemberResolution::Direct(method));
            return Some(signature);
        }
        None
    }
}
