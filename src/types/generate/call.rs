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
        ctx: &Ctx,
    ) -> Ty {
        self.finish_call_with_result_origin(node, node, callee_ty, args, ctx)
    }

    fn finish_call_with_result_origin(
        &mut self,
        node: NodeID,
        result_origin: NodeID,
        callee_ty: Ty,
        args: &[CallArg],
        ctx: &Ctx,
    ) -> Ty {
        let arg_count = args.len();

        // Calling a function value is a read: a borrowed callee (the
        // borrow-by-default type of a function-typed parameter) peels to
        // the function it borrows.
        let mut callee_shallow = self.store.shallow(&callee_ty);
        while let Ty::Borrow(_, inner) = callee_shallow {
            callee_shallow = self.store.shallow(&inner);
        }
        match callee_shallow {
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
                self.wanteds.push(Constraint::EffectSubset {
                    inferred: eff,
                    allowed: ctx.eff.clone(),
                    origin: CtOrigin::new(node, CtReason::Apply),
                });
                *ret
            }
            Ty::Var(_) => {
                let arg_tys: Vec<Ty> = args
                    .iter()
                    .map(|arg| self.infer_expr(&arg.value, ctx))
                    .collect();
                let ret = Ty::Var(self.store.fresh_ty(self.level, result_origin));
                let callee_effects = EffectRow::open(self.store.fresh_eff(self.level, node));
                let expected = Ty::Func(arg_tys, Box::new(ret.clone()), callee_effects.clone());
                self.emit_eq(callee_ty, expected, node, CtReason::Apply);
                self.wanteds.push(Constraint::EffectSubset {
                    inferred: callee_effects,
                    allowed: ctx.eff.clone(),
                    origin: CtOrigin::new(node, CtReason::Apply),
                });
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
        args: &[CallArg],
        ctx: &Ctx,
    ) -> Ty {
        let ExprKind::Member(Some(receiver), label, _) = &callee.kind else {
            return Ty::Error;
        };
        let receiver_ty = self.infer_expr(receiver, ctx);
        let member = Ty::Var(self.store.fresh_ty(self.level, callee.id));
        self.artifacts.node_types.insert(callee.id, member.clone());
        let result =
            self.finish_call_with_result_origin(expr.id, callee.id, member.clone(), args, ctx);
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
        type_args: &[GenericArg],
        args: &[CallArg],
        ctx: &Ctx,
    ) -> Ty {
        let ExprKind::Constructor(name) = &callee.kind else {
            return Ty::Error;
        };
        let Ok(symbol) = name.symbol() else {
            return Ty::Error;
        };
        if symbol == Symbol::InlineArray {
            self.unsupported(
                expr.id,
                "constructing an InlineArray directly; use an array literal with an [Element; Count] annotation",
            );
            return Ty::Error;
        }
        if self.catalog.protocols.contains_key(&symbol) {
            return self.infer_protocol_construction(expr, callee, symbol, type_args, args, ctx);
        }
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
            .enumerate()
            .map(|(index, param)| {
                let fresh = self.store.fresh_ty(self.level, expr.id);
                if let crate::types::ty::ParamKind::Static(value_ty) = &param.kind {
                    self.store.mark_static_hole(fresh);
                    // ADR 0035 §2: this construction forms an application;
                    // every integer static argument owes nonnegativity.
                    // An explicit argument owns the obligation (its
                    // lowering emits at the argument's node); the hole
                    // covers inferred and defaulted slots.
                    if index >= type_args.len()
                        && matches!(value_ty, Ty::Nominal(symbol, _) if *symbol == Symbol::Int)
                    {
                        self.wanteds.push(Constraint::StaticCmp {
                            op: crate::types::ty::StaticCmpOp::Le,
                            lhs: Ty::Static(StaticValue::Int(StaticInt::constant(0))),
                            rhs: Ty::Var(fresh),
                            origin: CtOrigin::new(expr.id, CtReason::Annotation),
                        });
                    }
                }
                Ty::Var(fresh)
            })
            .collect();
        if !info.params.is_empty() {
            self.record_instantiation(expr.id, &info.params, &theta);
        }
        // `ArrayIterator<Element>(array: self)`: explicit type arguments pin
        // the instantiation positionally.
        for ((type_arg, target), param) in type_args.iter().zip(&theta).zip(&info.params) {
            let ty = self.lower_generic_arg_for_param(param.symbol, type_arg);
            self.emit_eq(target.clone(), ty, type_arg.id(), CtReason::Annotation);
        }
        // Omitted trailing arguments take their declared defaults — hard,
        // like the annotation form: explicit arguments are the way to
        // choose another value (`Grid()` IS `Grid<4>()`).
        for index in type_args.len()..info.params.len() {
            let Some(default) = info.params[index].default.clone() else {
                break;
            };
            if matches!(default, Ty::Error) {
                continue;
            }
            let substitution: FxHashMap<Symbol, Ty> = param_subst(&info.params, &theta);
            let default =
                default.substitute(&substitution, &Default::default(), &Default::default());
            self.emit_eq(theta[index].clone(), default, expr.id, CtReason::Annotation);
        }
        // Closure-field effect rows instantiate per construction (one
        // fresh open row per implicit effect param) and ride the head as
        // `Ty::Eff` arguments — THIS instance's rows, recovered at member
        // reads, contaminating nothing else.
        let eff_tails: FxHashMap<Symbol, EffTail> = info
            .eff_params
            .iter()
            .map(|&param| {
                (
                    param,
                    EffTail::Var(self.store.fresh_eff(self.level, expr.id)),
                )
            })
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

        let arg_count = args.len();
        let init = info
            .inits
            .iter()
            .find(|(_, arity)| *arity == arg_count + 1)
            .or_else(|| info.inits.first())
            .map(|(init, _)| *init);
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
                // The construction's result is `self_ty` regardless of the
                // init's own return type (init bodies return unit), so
                // leave the signature's return free instead of pinning it
                // to `self_ty`; otherwise `Box3()` inside `Box3`'s own
                // binding group (e.g. a static method) poisons the init's
                // signature and the body type comes out mismatched.
                let ret = Ty::Var(self.store.fresh_ty(self.level, expr.id));
                let expected = Ty::Func(arg_tys, Box::new(ret), ctx.eff.clone());
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

    /// `P(args)`: construction through a protocol's init requirement.
    /// `Self` is a fresh variable constrained to conform, pinned by the
    /// expected type rather than by any argument (the ExpressibleBy-literal
    /// pattern); the conformance's witness initializer runs at lowering.
    #[allow(clippy::too_many_arguments)]
    fn infer_protocol_construction(
        &mut self,
        expr: &Expr,
        callee: &Expr,
        symbol: Symbol,
        type_args: &[GenericArg],
        args: &[CallArg],
        ctx: &Ctx,
    ) -> Ty {
        let Some(owner_ref) = self.fresh_protocol_ref(symbol, expr.id) else {
            return Ty::Error;
        };
        let Some((owner, requirement)) = self.catalog.requirement_in_ref(&owner_ref, "init") else {
            self.unsupported(
                expr.id,
                "constructing a protocol without an init requirement",
            );
            return Ty::Error;
        };
        let requirement = requirement.clone();
        let Some(scheme) = self.schemes.get(&requirement.symbol).cloned() else {
            return Ty::Error;
        };
        // Explicit type arguments pin the protocol's own parameters
        // positionally.
        let protocol_params = self
            .catalog
            .protocols
            .get(&symbol)
            .map(|info| info.params.clone())
            .unwrap_or_default();
        for ((type_arg, target), param) in
            type_args.iter().zip(&owner_ref.args).zip(&protocol_params)
        {
            let ty = self.lower_generic_arg_for_param(param.symbol, type_arg);
            self.emit_eq(target.clone(), ty, type_arg.id(), CtReason::Annotation);
        }

        let self_var = Ty::Var(self.store.fresh_ty(self.level, expr.id));
        let app = ProtocolApplication::new(self_var.clone(), owner.clone());
        let mut tys = app.substitution(self.catalog);
        self.freshen_scheme_type_params(expr.id, &scheme, &mut tys);
        let effs = self.freshen_scheme_effect_params(expr.id, &scheme);
        for predicate in &scheme.predicates {
            self.wanteds.push(
                predicate
                    .substitute(&tys, &effs, &Default::default())
                    .into_constraint(CtOrigin::new(expr.id, CtReason::Apply)),
            );
        }
        let signature = scheme.ty.substitute(&tys, &effs, &Default::default());
        self.wanteds.push(Constraint::Conforms {
            ty: self_var.clone(),
            protocol: owner.clone(),
            origin: CtOrigin::new(expr.id, CtReason::Apply),
        });
        self.artifacts.member_resolutions.insert(
            callee.id,
            MemberResolution::ViaRequirement {
                protocol: owner,
                requirement: requirement.symbol,
                self_ty: self_var,
            },
        );

        let Ty::Func(params, ret, eff) = self.store.shallow(&signature) else {
            return Ty::Error;
        };
        let arg_count = args.len();
        if params.len() != arg_count {
            self.diagnostics.errors.push((
                TypeError::ArityMismatch {
                    expected: params.len(),
                    found: arg_count,
                },
                expr.id,
            ));
            return Ty::Error;
        }
        for (arg, param) in args.iter().zip(&params) {
            self.check_expr(&arg.value, param, CtReason::Apply, ctx);
        }
        self.emit_eff_eq(eff, ctx.eff.clone(), expr.id);
        self.artifacts
            .node_types
            .insert(callee.id, Ty::Func(params, ret.clone(), EffectRow::pure()));
        *ret
    }

    // ----- Member resolution ----------------------------------------------
    // Value-receiver member access is a HasMember predicate solved in
    // solve/. Only TYPE members (Constructor receivers) resolve here.

    fn fresh_protocol_ref(&mut self, protocol: Symbol, node: NodeID) -> Option<ProtocolRef> {
        let params = self.catalog.protocols.get(&protocol)?.params.clone();
        Some(ProtocolRef {
            protocol,
            args: params
                .iter()
                .map(|_| Ty::Var(self.store.fresh_ty(self.level, node)))
                .collect(),
        })
    }

    fn freshen_scheme_type_params(
        &mut self,
        node: NodeID,
        scheme: &Scheme,
        tys: &mut FxHashMap<Symbol, Ty>,
    ) {
        for param in &scheme.params {
            let var = Ty::Var(self.store.fresh_ty(self.level, node));
            self.artifacts
                .instantiations
                .entry(node)
                .or_default()
                .push((param.symbol, var.clone()));
            tys.insert(param.symbol, var);
        }
    }

    fn freshen_scheme_effect_params(
        &mut self,
        node: NodeID,
        scheme: &Scheme,
    ) -> FxHashMap<Symbol, EffTail> {
        scheme
            .eff_params
            .iter()
            .map(|param| (*param, EffTail::Var(self.store.fresh_eff(self.level, node))))
            .collect()
    }

    /// Resolve `Type.label`: enum variants (constructors, or bare values for
    /// payload-less cases), protocol requirements (the protocol-static form
    /// operators desugar to: `Add.add(lhs, rhs)`), and static methods.
    pub(super) fn resolve_type_member(
        &mut self,
        symbol: Symbol,
        label: &Label,
        node: NodeID,
        reason: CtReason,
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
            let protocol_ref = self.fresh_protocol_ref(symbol, node)?;
            let (owner, requirement) =
                self.catalog.requirement_in_ref(&protocol_ref, &label_str)?;
            let requirement = requirement.clone();
            // The requirement's type is its scheme: bind Self, protocol
            // inputs, and associated projections for the owning protocol
            // application, then freshen method-level generics/effects like
            // any ordinary scheme instantiation.
            let scheme = self.schemes.get(&requirement.symbol)?.clone();
            let self_var = Ty::Var(self.store.fresh_ty(self.level, node));
            let app = ProtocolApplication::new(self_var.clone(), owner.clone());
            let mut tys = app.substitution(self.catalog);
            self.freshen_scheme_type_params(node, &scheme, &mut tys);
            let effs = self.freshen_scheme_effect_params(node, &scheme);
            for predicate in &scheme.predicates {
                self.wanteds.push(
                    predicate
                        .substitute(&tys, &effs, &Default::default())
                        .into_constraint(CtOrigin::new(node, reason)),
                );
            }
            let signature = scheme.ty.substitute(&tys, &effs, &Default::default());

            self.wanteds.push(Constraint::Conforms {
                ty: self_var.clone(),
                protocol: owner.clone(),
                origin: CtOrigin::new(node, reason),
            });
            if reason == CtReason::EqualityComparison
                && let [rhs] = owner.args.as_slice()
            {
                self.wanteds.push(Constraint::PreferEq(
                    self_var.clone(),
                    rhs.clone(),
                    CtOrigin::new(node, reason),
                ));
            }
            self.artifacts.member_resolutions.insert(
                node,
                MemberResolution::ViaRequirement {
                    protocol: owner,
                    requirement: requirement.symbol,
                    self_ty: self_var,
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
