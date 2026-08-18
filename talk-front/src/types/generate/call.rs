use super::*;

impl<'s, 'a> BodyChecker<'s, 'a> {
    // ----- Calls ---------------------------------------------------------

    /// The shared tail of every call: callee type against arguments, the
    /// callee's latent effects unified into the ambient row (Koka's
    /// application rule).
    pub(super) fn finish_call(
        &mut self,
        node: NodeID,
        target: String,
        callee_ty: Ty,
        args: &[CallArg],
        ctx: &Ctx,
    ) -> Ty {
        self.finish_call_with_result_origin(node, node, target, callee_ty, args, false, ctx)
    }

    pub(super) fn finish_call_with_result_origin(
        &mut self,
        node: NodeID,
        result_origin: NodeID,
        target: String,
        callee_ty: Ty,
        args: &[CallArg],
        adapt_unresolved_variant_params: bool,
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
                    self.diagnostics
                        .argument_arity(node, target, params.len(), arg_count);
                    return Ty::Error;
                }
                for (arg, param) in args.iter().zip(&params) {
                    if adapt_unresolved_variant_params
                        && matches!(self.store.shallow(param), Ty::Var(_))
                    {
                        let found = self.infer_expr(&arg.value, ctx);
                        if matches!(self.store.shallow(&found), Ty::Var(_) | Ty::Borrow(..)) {
                            self.wanteds.push(Constraint::Adapt {
                                expected: param.clone(),
                                found,
                                node_is_value: true,
                                origin: CtOrigin::new(arg.value.id, CtReason::Apply),
                            });
                        } else {
                            self.emit_eq(param.clone(), found, arg.value.id, CtReason::Apply);
                        }
                    } else {
                        self.check_expr(&arg.value, param, CtReason::Apply, ctx);
                    }
                    self.note_copy_marker(arg, param);
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
                for (index, (arg, arg_ty)) in args.iter().zip(&arg_tys).enumerate() {
                    self.note_indexed_marker(arg, &callee_ty, index, args.len(), arg_ty);
                }
                let ret = Ty::Var(self.store.fresh_ty(self.level, result_origin));
                let callee_effects = EffectRow::open(self.store.fresh_eff(self.level, node));
                let expected = Ty::Func(arg_tys, Box::new(ret.clone()), callee_effects.clone());
                self.emit_eq(callee_ty, expected, result_origin, CtReason::Apply);
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
        // The written labels let the solver select among label-overloaded
        // methods once the receiver's head is known (ADR 0041).
        self.artifacts.member_call_slots.insert(
            callee.id,
            args.iter()
                .map(crate::types::callables::WrittenSlot::of)
                .collect(),
        );
        let result = self.finish_call_with_result_origin(
            expr.id,
            callee.id,
            format!("Method '{label}'"),
            member.clone(),
            args,
            false,
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
        type_args: &[GenericArg],
        args: &[CallArg],
        ctx: &Ctx,
    ) -> Ty {
        let ExprKind::Constructor(name, head_segments) = &callee.kind else {
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
            if head_segments.iter().any(|segment| !segment.is_empty()) {
                self.unsupported(expr.id, "explicit type arguments on a protocol constructor");
            }
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
            .map(|param| {
                let fresh = self.store.fresh_ty(self.level, expr.id);
                if matches!(param.kind, crate::types::ty::ParamKind::Static(_)) {
                    self.store.mark_static_hole(fresh);
                }
                Ty::Var(fresh)
            })
            .collect();
        if !info.params.is_empty() {
            self.record_instantiation(expr.id, &info.params, &theta);
        }
        // Explicit type arguments pin the instantiation: per-segment head
        // args (`Outer<Int>.Inner<Bool>(…)`) plus call-site args
        // (`ArrayIterator<Element>(array: self)`), which fill the final
        // segment's remaining own slots.
        let covered = self.pin_head_args(
            symbol,
            head_segments,
            type_args,
            &info.params,
            &theta,
            expr.id,
        );
        // ADR 0035 §2: this construction forms an application; every
        // integer static argument owes nonnegativity. An explicit
        // argument owns the obligation (its lowering emits at the
        // argument's node); the hole covers inferred and defaulted slots.
        for (index, param) in info.params.iter().enumerate() {
            if covered[index] {
                continue;
            }
            if let crate::types::ty::ParamKind::Static(value_ty) = &param.kind
                && matches!(value_ty, Ty::Nominal(symbol, _) if *symbol == Symbol::Int)
            {
                self.wanteds.push(Constraint::StaticCmp {
                    op: crate::types::ty::StaticCmpOp::Le,
                    lhs: Ty::Static(StaticValue::Int(StaticInt::constant(0))),
                    rhs: theta[index].clone(),
                    origin: CtOrigin::new(expr.id, CtReason::Annotation),
                });
            }
        }
        // Omitted trailing arguments take their declared defaults — hard,
        // like the annotation form: explicit arguments are the way to
        // choose another value (`Grid()` IS `Grid<4>()`). The trailing
        // region starts after the final segment's explicit args.
        let final_offset = self
            .catalog
            .nominal_owners
            .get(&symbol)
            .map(|owner| nominal_params(self.catalog, *owner).len())
            .unwrap_or(0);
        let final_explicit = head_segments.last().map(Vec::len).unwrap_or(0) + type_args.len();
        for index in (final_offset + final_explicit)..info.params.len() {
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
        // ADR 0041: initializer selection uses the declared label sequence;
        // with no exact match, a same-arity candidate recovers and the
        // label pass reports its mismatch.
        let written: Vec<crate::types::callables::WrittenSlot> = args
            .iter()
            .map(crate::types::callables::WrittenSlot::of)
            .collect();
        // Inaccessible initializers never participate in selection
        // (ADR 0042): a type whose every initializer is hidden is not
        // constructible from this file.
        let inits: Vec<(Symbol, usize)> = info
            .inits
            .iter()
            .copied()
            .filter(|(init, _)| {
                self.catalog
                    .member_accessible(*init, self.module_id, expr.id.0)
            })
            .collect();
        if inits.is_empty() && !info.inits.is_empty() {
            let rendered = self.store.render(&self_ty);
            self.diagnostics.errors.push((
                TypeError::InaccessibleMember {
                    receiver: rendered,
                    label: "init".into(),
                },
                expr.id,
            ));
            return Ty::Error;
        }
        let init = inits
            .iter()
            .find(|(init, arity)| {
                *arity == arg_count + 1
                    && self
                        .catalog
                        .callable_contracts
                        .get(init)
                        .is_some_and(|contract| {
                            crate::types::callables::labels_admit(&contract.name.labels, &written)
                        })
            })
            .or_else(|| inits.iter().find(|(_, arity)| *arity == arg_count + 1))
            .or_else(|| inits.first())
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
                    self.diagnostics.argument_arity(
                        expr.id,
                        format!("Type '{symbol}'"),
                        params.len().saturating_sub(1),
                        arg_count,
                    );
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
                    self.note_copy_marker(arg, param);
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
                for (index, (arg, arg_ty)) in args.iter().zip(&arg_tys[1..]).enumerate() {
                    self.note_indexed_marker(arg, &signature, index, args.len(), arg_ty);
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
        if type_args.len() > protocol_params.len() {
            self.diagnostics.generic_argument_arity(
                expr.id,
                format!("Protocol '{symbol}'"),
                protocol_params.len(),
                type_args.len(),
            );
        }
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
            self.diagnostics.argument_arity(
                expr.id,
                format!("Protocol '{symbol}'"),
                params.len(),
                arg_count,
            );
            return Ty::Error;
        }
        for (arg, param) in args.iter().zip(&params) {
            self.check_expr(&arg.value, param, CtReason::Apply, ctx);
            self.note_copy_marker(arg, param);
        }
        self.emit_eff_eq(eff, ctx.eff.clone(), expr.id);
        self.artifacts
            .node_types
            .insert(callee.id, Ty::Func(params, ret.clone(), EffectRow::pure()));
        *ret
    }

    /// `T(args)` for a rigid type parameter: construction through an
    /// `init` requirement of one of `T`'s declared bounds — the
    /// requirement is ordinary conformance evidence whose committed
    /// witness is the conforming type's initializer (the Swift
    /// protocol-init / Eiffel creation-constraint shape). The resolution
    /// publishes as a requirement operation; the backend forces the
    /// witness per specialization (ADR 0036's two-point rule).
    #[allow(clippy::too_many_arguments)]
    pub(super) fn infer_param_construction(
        &mut self,
        expr: &Expr,
        callee: &Expr,
        symbol: Symbol,
        type_args: &[GenericArg],
        args: &[CallArg],
        ctx: &Ctx,
    ) -> Ty {
        if !type_args.is_empty() {
            self.diagnostics.generic_argument_arity(
                expr.id,
                format!("Type parameter '{symbol}'"),
                0,
                type_args.len(),
            );
            return Ty::Error;
        }
        let bounds = self
            .catalog
            .param_bounds
            .get(&symbol)
            .cloned()
            .unwrap_or_default();
        let resolved = bounds.iter().find_map(|bound| {
            self.catalog
                .requirement_in_ref(bound, "init")
                .map(|(owner, requirement)| (owner, requirement.clone()))
        });
        let Some((owner, requirement)) = resolved else {
            self.unsupported(
                expr.id,
                "constructing a type parameter whose bounds declare no init requirement",
            );
            return Ty::Error;
        };
        let Some(scheme) = self.schemes.get(&requirement.symbol).cloned() else {
            return Ty::Error;
        };
        // `Self` is the rigid parameter itself; the bound's conformance
        // is a given, so no wanted constraint is owed.
        let self_ty = Ty::Param(symbol);
        let app = ProtocolApplication::new(self_ty.clone(), owner.clone());
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
        self.artifacts.member_resolutions.insert(
            callee.id,
            MemberResolution::ViaRequirement {
                protocol: owner,
                requirement: requirement.symbol,
                self_ty,
            },
        );

        let Ty::Func(params, ret, eff) = self.store.shallow(&signature) else {
            return Ty::Error;
        };
        if params.len() != args.len() {
            self.diagnostics.argument_arity(
                expr.id,
                format!("Type parameter '{symbol}'"),
                params.len(),
                args.len(),
            );
            return Ty::Error;
        }
        for (arg, param) in args.iter().zip(&params) {
            self.check_expr(&arg.value, param, CtReason::Apply, ctx);
            self.note_copy_marker(arg, param);
        }
        self.emit_eff_eq(eff, ctx.eff.clone(), expr.id);
        self.artifacts
            .node_types
            .insert(callee.id, Ty::Func(params, ret.clone(), EffectRow::pure()));
        *ret
    }

    /// A `mut` argument writes its evolved value back, so it must name a
    /// writable place — the argument-position mirror of
    /// `infer_assignment_target`. A true rvalue's evolution would be
    /// silently discarded, which is a source error, not a backend gap.
    /// Select one static method from an overload set by written labels
    /// (ADR 0041), mirroring the solver's instance-method selection.
    fn select_static_overload(
        &mut self,
        set: &[Symbol],
        label: &str,
        node: NodeID,
    ) -> Option<Symbol> {
        use crate::types::callables::labels_admit;

        match set {
            [] => None,
            [one] => Some(*one),
            _ => {
                let slots = self.artifacts.member_call_slots.get(&node);
                if let Some(slots) = slots {
                    let admitted: Vec<Symbol> =
                        set.iter()
                            .copied()
                            .filter(|symbol| {
                                self.catalog.callable_contracts.get(symbol).is_some_and(
                                    |contract| labels_admit(&contract.name.labels, slots),
                                )
                            })
                            .collect();
                    if let [one] = admitted.as_slice() {
                        return Some(*one);
                    }
                    if admitted.is_empty() {
                        let same_arity: Vec<Symbol> = set
                            .iter()
                            .copied()
                            .filter(|symbol| {
                                self.catalog.callable_contracts.get(symbol).is_some_and(
                                    |contract| contract.name.labels.len() == slots.len(),
                                )
                            })
                            .collect();
                        if let [one] = same_arity.as_slice() {
                            return Some(*one);
                        }
                    }
                }
                let candidates = set
                    .iter()
                    .filter_map(|symbol| {
                        Some(
                            crate::types::callables::CallableName {
                                base: label.to_string(),
                                labels: self
                                    .catalog
                                    .callable_contracts
                                    .get(symbol)?
                                    .name
                                    .labels
                                    .clone(),
                            }
                            .to_string(),
                        )
                    })
                    .collect();
                self.diagnostics.errors.push((
                    TypeError::AmbiguousMember {
                        receiver: String::new(),
                        label: label.to_string(),
                        candidates,
                    },
                    node,
                ));
                set.first().copied()
            }
        }
    }

    pub(super) fn check_mut_arg_is_place(&mut self, arg: &CallArg) {
        use crate::parsing::node_kinds::call_arg::ArgMode;
        if !matches!(arg.mode, Some(ArgMode::Mut)) {
            return;
        }
        if !matches!(
            &arg.value.kind,
            ExprKind::Variable(_) | ExprKind::Member(Some(_), ..)
        ) {
            self.diagnostics
                .errors
                .push((TypeError::MutArgumentNotAPlace, arg.value.id));
        }
    }

    /// A call-site ownership marker is checked source semantics: `copy`
    /// demands Copy or Clone evidence, `mut` an exclusive-borrow
    /// parameter, `borrow` a borrowing parameter. The judgments defer to
    /// finalization, when the argument's slot type has resolved.
    fn note_copy_marker(&mut self, arg: &CallArg, param: &Ty) {
        use crate::parsing::node_kinds::call_arg::ArgMode;
        self.check_mut_arg_is_place(arg);
        if matches!(
            arg.mode,
            Some(ArgMode::Copy | ArgMode::Mut | ArgMode::Borrow)
        ) {
            self.artifacts.marked_args.push((
                arg.value.id,
                MarkedSlot::Param(param.clone()),
                arg.mode.expect("mode matched above"),
            ));
        }
    }

    /// [`Self::note_copy_marker`] through a still-unresolved callee: the
    /// parameter slot is found post-solve by indexing the callee's
    /// function type.
    pub(super) fn note_indexed_marker(
        &mut self,
        arg: &CallArg,
        callee: &Ty,
        index: usize,
        arg_count: usize,
        arg_ty: &Ty,
    ) {
        use crate::parsing::node_kinds::call_arg::ArgMode;
        self.check_mut_arg_is_place(arg);
        if matches!(
            arg.mode,
            Some(ArgMode::Copy | ArgMode::Mut | ArgMode::Borrow)
        ) {
            self.artifacts.marked_args.push((
                arg.value.id,
                MarkedSlot::CalleeIndexed {
                    callee: callee.clone(),
                    index,
                    arg_count,
                    arg_ty: arg_ty.clone(),
                },
                arg.mode.expect("mode matched above"),
            ));
        }
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
    /// `head_segments` are explicit args on the type reference itself
    /// (`Opt<Int>.some`, `Res<Int>.A<Bool>.pair`), one list per dotted
    /// path segment: each pins its segment's own param slots.
    pub(super) fn resolve_type_member(
        &mut self,
        symbol: Symbol,
        head_segments: &[Vec<GenericArg>],
        label: &Label,
        node: NodeID,
        reason: CtReason,
    ) -> Option<Ty> {
        let label_str = label.to_string();

        if let Some(info) = self.catalog.enums.get(&symbol).cloned()
            && let Some(variant) = info.variants.get(&label_str).cloned()
        {
            let theta: Vec<Ty> = info
                .params
                .iter()
                .map(|_| Ty::Var(self.store.fresh_ty(self.level, node)))
                .collect();
            self.pin_head_args(symbol, head_segments, &[], &info.params, &theta, node);
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
            if head_segments.iter().any(|segment| !segment.is_empty()) {
                self.unsupported(node, "explicit type arguments on a protocol receiver");
            }
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

        let static_info = self
            .catalog
            .structs
            .get(&symbol)
            .map(|info| (info.params.clone(), info.statics.clone()))
            .or_else(|| {
                self.catalog
                    .enums
                    .get(&symbol)
                    .map(|info| (info.params.clone(), info.statics.clone()))
            });
        if let Some((params, statics)) = static_info
            && let Some(set) = statics.get(&label_str)
        {
            // Inaccessible overloads never participate in selection
            // (ADR 0042).
            let accessible: Vec<Symbol> = set
                .iter()
                .copied()
                .filter(|method| {
                    self.catalog
                        .member_accessible(*method, self.module_id, node.0)
                })
                .collect();
            if accessible.is_empty() && !set.is_empty() {
                let rendered = self.store.render(&Ty::Nominal(symbol, vec![]));
                self.diagnostics.errors.push((
                    TypeError::InaccessibleMember {
                        receiver: rendered,
                        label: label_str,
                    },
                    node,
                ));
                return None;
            }
            if let Some(method) = self.select_static_overload(&accessible, &label_str, node) {
                let theta: Vec<Ty> = params
                    .iter()
                    .map(|_| Ty::Var(self.store.fresh_ty(self.level, node)))
                    .collect();
                self.pin_head_args(symbol, head_segments, &[], &params, &theta, node);
                if !params.is_empty() {
                    self.record_instantiation(node, &params, &theta);
                }
                let substitution = param_subst(&params, &theta);
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
        }
        None
    }

    /// Unify a type reference's explicit head args with the head's
    /// freshly-minted instantiation. `segments` holds one arg list per
    /// dotted path segment (`Res<Int>.A<Bool>`), aligned to the tail of
    /// the nesting chain; `trailing` are call-site type args, which fill
    /// the final segment's remaining own slots. Each segment's args pin
    /// positionally from that segment's own offset — its owner's
    /// flattened param count. Returns which flattened param indexes the
    /// explicit args covered (their lowering owns those slots'
    /// formation obligations).
    pub(super) fn pin_head_args(
        &mut self,
        symbol: Symbol,
        segments: &[Vec<GenericArg>],
        trailing: &[GenericArg],
        params: &[SchemeParam],
        theta: &[Ty],
        node: NodeID,
    ) -> Vec<bool> {
        let mut covered = vec![false; params.len()];
        if segments.iter().all(Vec::is_empty) && trailing.is_empty() {
            return covered;
        }
        // The nesting chain, outermost first; path segments name its tail.
        let mut chain = vec![symbol];
        let mut current = symbol;
        while let Some(&owner) = self.catalog.nominal_owners.get(&current) {
            chain.push(owner);
            current = owner;
        }
        chain.reverse();
        let count = segments.len().max(1);
        if count > chain.len() {
            // A path longer than the nesting chain never resolved to
            // this symbol; resolution already diagnosed it.
            return covered;
        }
        let tail = &chain[chain.len() - count..];
        let empty = vec![];
        for (index, seg_symbol) in tail.iter().enumerate() {
            let offset = self
                .catalog
                .nominal_owners
                .get(seg_symbol)
                .map(|owner| nominal_params(self.catalog, *owner).len())
                .unwrap_or(0);
            let own = nominal_params(self.catalog, *seg_symbol)
                .len()
                .saturating_sub(offset);
            let base = segments.get(index).unwrap_or(&empty);
            let seg_args: Vec<&GenericArg> = if index + 1 == tail.len() {
                base.iter().chain(trailing).collect()
            } else {
                base.iter().collect()
            };
            if seg_args.is_empty() {
                continue;
            }
            if seg_args.len() > own {
                self.diagnostics.generic_argument_arity(
                    node,
                    format!("Type '{seg_symbol}'"),
                    own,
                    seg_args.len(),
                );
                continue;
            }
            for (position, arg) in seg_args.iter().enumerate() {
                let target_index = offset + position;
                let (Some(target), Some(param)) =
                    (theta.get(target_index), params.get(target_index))
                else {
                    break;
                };
                let target = target.clone();
                let ty = self.lower_generic_arg_for_param(param.symbol, arg);
                self.emit_eq(target, ty, arg.id(), CtReason::Annotation);
                covered[target_index] = true;
            }
        }
        covered
    }
}
