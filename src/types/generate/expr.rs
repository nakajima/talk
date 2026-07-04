use super::*;

impl<'s, 'a> BodyChecker<'s, 'a> {
    // ----- Expressions -------------------------------------------------

    pub(super) fn infer_expr(&mut self, expr: &Expr, ctx: &Ctx) -> Ty {
        let ty = self.infer_expr_kind(expr, ctx);
        self.artifacts.node_types.insert(expr.id, ty.clone());
        ty
    }

    /// Checking mode: push the expected type inward where syntax allows
    /// (Pierce & Turner; DK 2021's mode recipe), otherwise infer and emit an
    /// equality oriented expected-then-found for blame.
    pub(super) fn check_expr(&mut self, expr: &Expr, expected: &Ty, reason: CtReason, ctx: &Ctx) {
        if let Ty::Borrow(expected_kind, inner) = self.store.shallow(expected) {
            match &expr.kind {
                ExprKind::Member(None, ..) => {
                    self.check_expr(expr, &inner, reason, ctx);
                    return;
                }
                ExprKind::Call { callee, .. }
                    if matches!(callee.kind, ExprKind::Member(None, ..)) =>
                {
                    self.check_expr(expr, &inner, reason, ctx);
                    return;
                }
                _ => {}
            }
            let found = self.infer_expr(expr, ctx);
            self.emit_immediate_borrow_check(
                expr.id,
                expected_kind,
                (*inner).clone(),
                expected.clone(),
                found,
                reason,
            );
            return;
        }

        match &expr.kind {
            // Leading-dot variant construction (`.sleep(ms)`, `.none`)
            // resolves through the expected enum — checking mode is what
            // makes the head known (bidirectional payoff).
            ExprKind::Member(None, label, _) => {
                if self.check_leading_dot(expr, label, None, expected, ctx, None) {
                    return;
                }
                let ty = self.infer_expr(expr, ctx);
                self.check_inferred_against_expected(expr.id, expected, ty, reason);
            }
            ExprKind::Call { callee, args, .. }
                if matches!(callee.kind, ExprKind::Member(None, _, _)) =>
            {
                if let ExprKind::Member(None, label, _) = &callee.kind
                    && self.check_leading_dot(
                        expr,
                        label,
                        Some(args),
                        expected,
                        ctx,
                        Some(callee.id),
                    )
                {
                    return;
                }
                let ty = self.infer_expr(expr, ctx);
                self.check_inferred_against_expected(expr.id, expected, ty, reason);
            }
            ExprKind::LiteralArray(items) => {
                if let Ty::Nominal(symbol, args) = self.store.shallow(expected)
                    && symbol == Symbol::Array
                    && let [element] = args.as_slice()
                {
                    for item in items {
                        self.check_expr(item, element, CtReason::ArrayElement, ctx);
                    }
                    self.artifacts.node_types.insert(expr.id, expected.clone());
                    return;
                }
                let ty = self.infer_expr(expr, ctx);
                self.check_inferred_against_expected(expr.id, expected, ty, reason);
            }
            ExprKind::Tuple(items) => {
                if items.len() == 1 {
                    self.check_expr(&items[0], expected, reason, ctx);
                    self.artifacts.node_types.insert(expr.id, expected.clone());
                    return;
                }
                if let Ty::Tuple(expected_items) = self.store.shallow(expected)
                    && expected_items.len() == items.len()
                {
                    for (item, expected_item) in items.iter().zip(&expected_items) {
                        self.check_expr(item, expected_item, reason, ctx);
                    }
                    self.artifacts.node_types.insert(expr.id, expected.clone());
                    return;
                }
                let ty = self.infer_expr(expr, ctx);
                self.check_inferred_against_expected(expr.id, expected, ty, reason);
            }
            ExprKind::RecordLiteral { fields, spread } => {
                if spread.is_none()
                    && let Ty::Record(row) = self.store.shallow(expected)
                    && row.tail.is_none()
                {
                    let mut found_fields = vec![];
                    for field in fields {
                        let label = Label::Named(field.label.name_str());
                        let field_ty = row
                            .fields
                            .iter()
                            .find(|(expected_label, _)| *expected_label == label)
                            .map(|(_, field_ty)| field_ty.clone());
                        match field_ty {
                            Some(field_ty) => {
                                self.check_expr(&field.value, &field_ty, reason, ctx);
                                found_fields.push((label, field_ty));
                            }
                            None => {
                                let inferred = self.infer_expr(&field.value, ctx);
                                found_fields.push((label, inferred));
                            }
                        }
                    }
                    self.emit_eq(
                        expected.clone(),
                        Ty::Record(Row::closed(found_fields)),
                        expr.id,
                        reason,
                    );
                    self.artifacts.node_types.insert(expr.id, expected.clone());
                    return;
                }
                let ty = self.infer_expr(expr, ctx);
                self.check_inferred_against_expected(expr.id, expected, ty, reason);
            }
            ExprKind::Block(block) => {
                self.check_block_value(block, expected, ctx);
                self.artifacts.node_types.insert(expr.id, expected.clone());
            }
            ExprKind::If(..) => {
                unreachable!("if expressions are desugared to match before type checking")
            }
            ExprKind::Match(scrutinee, arms) => {
                self.check_match_expr(scrutinee, arms, expected, ctx);
                self.artifacts.node_types.insert(expr.id, expected.clone());
            }
            ExprKind::Func(func) => {
                if let Ty::Func(params, ret, eff) = self.store.shallow(expected)
                    && params.len() == func.params.len()
                {
                    let ty = self.infer_func_against(func, &params, &ret, &eff, ctx);
                    self.artifacts.node_types.insert(expr.id, ty);
                    return;
                }
                let ty = self.infer_expr(expr, ctx);
                self.check_inferred_against_expected(expr.id, expected, ty, reason);
            }
            _ => {
                let ty = self.infer_expr(expr, ctx);
                self.check_inferred_against_expected(expr.id, expected, ty, reason);
            }
        }
    }

    pub(super) fn emit_immediate_argument_eq(
        &mut self,
        expected: &Ty,
        found: Ty,
        node: crate::node_id::NodeID,
        reason: CtReason,
    ) {
        if let Ty::Borrow(expected_kind, inner) = self.store.shallow(expected) {
            self.emit_immediate_borrow_check(
                node,
                expected_kind,
                (*inner).clone(),
                expected.clone(),
                found,
                reason,
            );
            return;
        }
        self.emit_eq(expected.clone(), found, node, reason);
    }

    fn emit_immediate_borrow_check(
        &mut self,
        node: crate::node_id::NodeID,
        expected_kind: Perm,
        expected_inner: Ty,
        expected: Ty,
        found: Ty,
        reason: CtReason,
    ) {
        match self.store.shallow(&found) {
            Ty::Borrow(found_kind, found_inner) if found_kind == expected_kind => {
                self.emit_eq(expected_inner, (*found_inner).clone(), node, reason);
            }
            Ty::Borrow(Perm::Exclusive, found_inner) if expected_kind == Perm::Shared => {
                self.emit_eq(expected_inner, (*found_inner).clone(), node, reason);
            }
            Ty::Borrow(..) => self.emit_eq(expected, found, node, reason),
            Ty::Var(_) if reason == CtReason::Apply => {
                self.wanteds.push(Constraint::ApplyBorrow {
                    expected_perm: expected_kind,
                    expected_inner,
                    found,
                    origin: CtOrigin::new(node, reason),
                });
            }
            _ => self.emit_eq(expected_inner, found, node, reason),
        }
    }

    pub(super) fn emit_borrow_downgrade_or_eq(
        &mut self,
        expected: Ty,
        found: Ty,
        node: crate::node_id::NodeID,
        reason: CtReason,
    ) {
        match (self.store.shallow(&expected), self.store.shallow(&found)) {
            (
                Ty::Borrow(Perm::Shared, expected_inner),
                Ty::Borrow(Perm::Exclusive, found_inner),
            ) => self.emit_eq(
                (*expected_inner).clone(),
                (*found_inner).clone(),
                node,
                reason,
            ),
            _ => self.emit_eq(expected, found, node, reason),
        }
    }

    pub(super) fn check_inferred_against_expected(
        &mut self,
        node: NodeID,
        expected: &Ty,
        found: Ty,
        reason: CtReason,
    ) {
        if found.is_never() {
            return;
        }
        if self.try_implicit_existential_pack(node, expected, &found, reason) {
            return;
        }
        // Reaching here, `expected` is not a borrow (immediate auto-borrow is handled by the
        // `Ty::Borrow` branch of `check_expr`). Checking a value against a non-borrow type is
        // not an application of that value, so drop `Apply`: a function value must satisfy a
        // function-typed slot invariantly rather than coercing its contravariant parameters.
        // Exception: an owned copy-out-of-borrow slot — or a borrowed such argument (the
        // expected side may still be a projection, e.g. a requirement's associated RHS) —
        // keeps `Apply` so the solver's tier-2 coercion (borrowed argument satisfied by a
        // free copy or an O(1) clone) can fire even when either side resolves late.
        let copies = |symbol: Symbol| self.catalog.copies_out_of_borrow(symbol);
        let keeps_apply = reason == CtReason::Apply
            && (matches!(self.store.shallow(expected), Ty::Nominal(symbol, _) if copies(symbol))
                || matches!(
                    self.store.shallow(&found),
                    Ty::Borrow(_, ref inner)
                        if matches!(self.store.shallow(inner), Ty::Nominal(symbol, _) if copies(symbol))
                ));
        let reason = if keeps_apply { reason } else { reason.nested() };
        self.emit_eq(expected.clone(), found, node, reason);
    }

    pub(super) fn try_implicit_existential_pack(
        &mut self,
        node: NodeID,
        expected: &Ty,
        found: &Ty,
        reason: CtReason,
    ) -> bool {
        let Ty::Any { protocol, assoc } = self.store.shallow(expected) else {
            return false;
        };

        if let Ty::Any {
            protocol: found_protocol,
            assoc: found_assoc,
        } = self.store.shallow(found)
        {
            if protocol == found_protocol
                && assoc.len() == found_assoc.len()
                && assoc
                    .iter()
                    .zip(&found_assoc)
                    .all(|((left, _), (right, _))| left == right)
            {
                self.emit_eq(expected.clone(), found.clone(), node, reason);
                self.artifacts.node_types.insert(node, expected.clone());
            } else {
                self.diagnostics.errors.push((
                    TypeError::UnsupportedExistentialUpcast {
                        expected: self.store.render(expected),
                        found: self.store.render(found),
                    },
                    node,
                ));
            }
            return true;
        }

        self.wanteds.push(Constraint::Conforms {
            ty: found.clone(),
            protocol,
            origin: CtOrigin::new(node, reason),
        });
        for (assoc_symbol, assoc_ty) in &assoc {
            self.wanteds.push(Constraint::Eq(
                Ty::Proj(Box::new(found.clone()), protocol, *assoc_symbol),
                assoc_ty.clone(),
                CtOrigin::new(node, reason),
            ));
        }
        self.artifacts.existential_packs.insert(
            node,
            ExistentialPack {
                existential: expected.clone(),
                payload: found.clone(),
            },
        );
        self.artifacts.node_types.insert(node, expected.clone());
        true
    }

    pub(super) fn infer_match_expr(
        &mut self,
        node: NodeID,
        scrutinee: &Expr,
        arms: &[MatchArm],
        ctx: &Ctx,
    ) -> Ty {
        if arms.is_empty() {
            self.infer_expr(scrutinee, ctx);
            return Ty::Nominal(Symbol::Never, vec![]);
        }
        let result = Ty::Var(self.store.fresh_ty(self.level, node));
        self.check_match_arms_against(scrutinee, arms, &result, true, ctx);
        result
    }

    pub(super) fn check_match_expr(
        &mut self,
        scrutinee: &Expr,
        arms: &[MatchArm],
        expected: &Ty,
        ctx: &Ctx,
    ) {
        self.check_match_arms_against(scrutinee, arms, expected, false, ctx);
    }

    pub(super) fn check_match_arms_against(
        &mut self,
        scrutinee: &Expr,
        arms: &[MatchArm],
        expected: &Ty,
        inferring_result: bool,
        ctx: &Ctx,
    ) {
        // OutsideIn(X) checks each GADT arm under an implication: constructor
        // equalities are givens, arm-local unification variables are
        // touchable, and outer variables stay untouchable.
        let scrutinee_ty = self.infer_expr(scrutinee, ctx);
        // Patterns match through a borrow. When the scrutinee's type is
        // still unresolved (an iterator's element type, say), a deferred
        // PatternView constraint strips it once its head is known — pinning
        // the patterns to the owned enum here would clash with a borrow
        // arriving later from a conformance solution.
        let pattern_scrutinee_ty = match self.store.shallow(&scrutinee_ty) {
            Ty::Borrow(_, inner) => *inner,
            Ty::Var(id) => {
                let view = Ty::Var(self.store.fresh_ty(self.level, scrutinee.id));
                self.wanteds.push(Constraint::PatternView {
                    scrutinee: Ty::Var(id),
                    view: view.clone(),
                    origin: CtOrigin::new(scrutinee.id, CtReason::Pattern),
                });
                view
            }
            other => other,
        };
        for arm in arms {
            let old_level = self.level;
            let arm_level = self.level.next();
            let start = self.wanteds.len();
            self.level = arm_level;
            let refinement = self.check_pattern(&arm.pattern, &pattern_scrutinee_ty);
            let reason = if inferring_result && !refinement.is_empty() {
                CtReason::GadtBranch
            } else {
                CtReason::Body
            };
            self.check_block_value_with_reason(&arm.body, expected, reason, ctx);
            self.level = old_level;
            let wanteds = self.wanteds.split_off(start);
            if refinement.is_empty() {
                self.wanteds.extend(wanteds);
            } else {
                self.wanteds.push(Constraint::Implic(Box::new(Implication {
                    level: arm_level,
                    givens: refinement.givens,
                    wanteds,
                    local_params: refinement.local_params,
                    touchable_level: Some(arm_level),
                })));
            }
        }
    }

    /// Try to resolve `.variant`/`.variant(args)` against an expected enum
    /// type. Returns false when the expected head is not (yet) a known enum.
    pub(super) fn check_leading_dot(
        &mut self,
        expr: &Expr,
        label: &Label,
        args: Option<&[CallArg]>,
        expected: &Ty,
        ctx: &Ctx,
        // When the leading dot is the callee of a call (`.write(fd, buf)`), the id
        // of that callee node, so it gets the variant's constructor type (the call
        // checker resolves it structurally and never types it otherwise).
        callee_id: Option<NodeID>,
    ) -> bool {
        let Ty::Nominal(symbol, enum_args) = self.store.shallow(expected) else {
            return false;
        };
        let Some(info) = self.catalog.enums.get(&symbol).cloned() else {
            return false;
        };
        let Some(variant) = info.variants.get(&label.to_string()).cloned() else {
            self.diagnostics.errors.push((
                TypeError::UnknownMember {
                    receiver: self.store.render(expected),
                    label: label.to_string(),
                },
                expr.id,
            ));
            self.artifacts.node_types.insert(expr.id, Ty::Error);
            return true;
        };
        self.artifacts
            .member_resolutions
            .insert(expr.id, MemberResolution::Direct(variant.symbol));
        let substitution = param_subst(&info.params, &enum_args);
        let instantiation = self.instantiate_variant(&variant, substitution, expr.id);
        if let Some(callee_id) = callee_id {
            self.artifacts.node_types.insert(
                callee_id,
                Ty::Func(
                    instantiation.argument_types.clone(),
                    Box::new(instantiation.result_type.clone()),
                    EffectRow::pure(),
                ),
            );
        }
        self.record_variant_instantiation(expr.id, &instantiation);
        self.emit_variant_predicates(&instantiation, expr.id);
        self.emit_eq(
            expected.clone(),
            instantiation.result_type.clone(),
            expr.id,
            CtReason::Apply,
        );
        let args = args.unwrap_or(&[]);
        if args.len() != instantiation.argument_types.len() {
            self.diagnostics.errors.push((
                TypeError::ArityMismatch {
                    expected: instantiation.argument_types.len(),
                    found: args.len(),
                },
                expr.id,
            ));
        } else {
            for (arg, payload) in args.iter().zip(&instantiation.argument_types) {
                self.check_expr(&arg.value, payload, CtReason::Apply, ctx);
            }
        }
        self.artifacts.node_types.insert(expr.id, expected.clone());
        true
    }

    pub(super) fn infer_expr_kind(&mut self, expr: &Expr, ctx: &Ctx) -> Ty {
        match &expr.kind {
            ExprKind::LiteralInt(_) => Ty::Nominal(Symbol::Int, vec![]),
            ExprKind::LiteralFloat(_) => Ty::Nominal(Symbol::Float, vec![]),
            ExprKind::LiteralTrue | ExprKind::LiteralFalse => Ty::Nominal(Symbol::Bool, vec![]),
            ExprKind::LiteralString(_) => Ty::Nominal(Symbol::String, vec![]),

            ExprKind::LiteralArray(items) => {
                let element = Ty::Var(self.store.fresh_ty(self.level, expr.id));
                for item in items {
                    self.check_expr(item, &element, CtReason::ArrayElement, ctx);
                }
                Ty::Nominal(Symbol::Array, vec![element])
            }

            ExprKind::Tuple(items) => match items.as_slice() {
                // `()` is the unit value, `(e)` is grouping.
                [] => Ty::unit(),
                [single] => self.infer_expr(single, ctx),
                _ => Ty::Tuple(
                    items
                        .iter()
                        .map(|item| self.infer_expr(item, ctx))
                        .collect(),
                ),
            },

            ExprKind::RecordLiteral { fields, spread } => {
                if let Some(spread) = spread {
                    self.infer_expr(spread, ctx);
                    self.unsupported(expr.id, "record spread");
                    return Ty::Error;
                }
                let fields = fields
                    .iter()
                    .map(|field| {
                        let ty = self.infer_expr(&field.value, ctx);
                        (Label::Named(field.label.name_str()), ty)
                    })
                    .collect();
                Ty::Record(Row::closed(fields))
            }

            ExprKind::Variable(name) => self.lookup(name, expr.id),

            ExprKind::Block(block) => self.infer_block_value(block, ctx),

            ExprKind::If(..) => {
                unreachable!("if expressions are desugared to match before type checking")
            }

            ExprKind::Match(scrutinee, arms) => {
                self.infer_match_expr(expr.id, scrutinee, arms, ctx)
            }

            ExprKind::Call {
                callee,
                type_args,
                args,
                trailing_block,
            } => {
                if let ExprKind::Constructor(name) = &callee.kind {
                    return self.infer_construction(
                        expr,
                        callee,
                        name,
                        type_args,
                        args,
                        trailing_block,
                        ctx,
                    );
                }
                if let ExprKind::Member(Some(receiver), label, _) = &callee.kind
                    && !matches!(receiver.kind, ExprKind::Constructor(_))
                {
                    if !type_args.is_empty() {
                        self.unsupported(expr.id, "type arguments on method calls");
                    }
                    return self.infer_member_call(
                        expr,
                        callee,
                        receiver,
                        label,
                        args,
                        trailing_block,
                        ctx,
                    );
                }
                let callee_ty = self.infer_expr(callee, ctx);
                if !type_args.is_empty() {
                    self.apply_type_args(callee.id, type_args);
                }
                self.finish_call(expr.id, callee_ty, args, trailing_block, ctx)
            }

            ExprKind::Func(func) => self.infer_func(func, ctx),

            ExprKind::As(inner, annotation) => {
                let ty = self.lower_annotation(annotation);
                self.check_expr(inner, &ty, CtReason::Annotation, ctx);
                ty
            }

            ExprKind::Member(Some(receiver), label, _) => {
                if let ExprKind::Constructor(name) = &receiver.kind {
                    let Ok(symbol) = name.symbol() else {
                        return Ty::Error;
                    };
                    // The receiver is a bare type name, resolved structurally rather
                    // than as a value — but it's still an expression node, so record a
                    // type for it (it has no value type, like a type name used as a
                    // value, so `Ty::Error`). Keeps `node_types` total over expressions.
                    self.artifacts.node_types.insert(receiver.id, Ty::Error);
                    return match self.resolve_type_member(symbol, label, expr.id) {
                        Some(ty) => ty,
                        None => {
                            self.diagnostics.errors.push((
                                TypeError::UnknownMember {
                                    receiver: name.name_str(),
                                    label: label.to_string(),
                                },
                                expr.id,
                            ));
                            Ty::Error
                        }
                    };
                }
                // A HasMember predicate (Gaster & Jones 1996); the solver
                // discharges it as soon as the receiver's head is known.
                let receiver_ty = self.infer_expr(receiver, ctx);
                let member = Ty::Var(self.store.fresh_ty(self.level, expr.id));
                self.wanteds.push(Constraint::HasMember {
                    receiver: receiver_ty,
                    label: label.clone(),
                    member: member.clone(),
                    origin: CtOrigin::new(expr.id, CtReason::Apply),
                });
                member
            }
            ExprKind::Member(None, _, _) => {
                self.unsupported(expr.id, "leading-dot member access");
                Ty::Error
            }

            ExprKind::Constructor(_) => {
                self.unsupported(expr.id, "type names as values");
                Ty::Error
            }
            ExprKind::CallEffect {
                effect_name,
                type_args,
                args,
                ..
            } => {
                // Performing an operation: arguments check against the
                // declared signature, the effect joins the ambient row
                // (Plotkin & Pretnar 2009 operations; row growth per Koka).
                // Discharge happens at the handler's extent — a `@handle`
                // widening the ambient row for the rest of its block — not
                // at the perform site; closed effect annotations are
                // checked after the group solve.
                let Ok(symbol) = effect_name.symbol() else {
                    return Ty::Error;
                };
                let Some(sig) = self.catalog.effects.get(&symbol).cloned() else {
                    self.unsupported(expr.id, "calling an undeclared effect");
                    return Ty::Error;
                };
                // A generic effect instantiates fresh at each perform
                // (Damas-Milner instantiation, exactly like schemes);
                // explicit type arguments equate positionally. The
                // handler sees the rigid parameters instead — it must be
                // generic over them.
                let mut tys: FxHashMap<Symbol, Ty> = FxHashMap::default();
                for param in &sig.generics {
                    let var = Ty::Var(self.store.fresh_ty(self.level, expr.id));
                    tys.insert(*param, var);
                }
                if !tys.is_empty() {
                    self.artifacts
                        .instantiations
                        .entry(expr.id)
                        .or_default()
                        .extend(sig.generics.iter().map(|g| (*g, tys[g].clone())));
                }
                if type_args.len() > sig.generics.len() {
                    self.unsupported(expr.id, "more type arguments than the effect declares");
                }
                for (annotation, param) in type_args.iter().zip(&sig.generics) {
                    let annotated = self.lower_annotation(annotation);
                    self.emit_eq(tys[param].clone(), annotated, expr.id, CtReason::Annotation);
                }
                for predicate in &sig.predicates {
                    self.wanteds.push(
                        predicate
                            .substitute(&tys, &Default::default(), &Default::default())
                            .into_constraint(CtOrigin::new(expr.id, CtReason::Apply)),
                    );
                }
                let instantiate =
                    |ty: &Ty| ty.substitute(&tys, &Default::default(), &Default::default());
                if args.len() == sig.params.len() {
                    for (arg, param) in args.iter().zip(&sig.params) {
                        self.check_expr(&arg.value, &instantiate(param), CtReason::Apply, ctx);
                    }
                } else {
                    self.diagnostics.errors.push((
                        TypeError::ArityMismatch {
                            expected: sig.params.len(),
                            found: args.len(),
                        },
                        expr.id,
                    ));
                }
                let tail = self.store.fresh_eff(self.level, expr.id);
                let entry = EffectEntry {
                    effect: symbol,
                    args: sig.generics.iter().map(|g| tys[g].clone()).collect(),
                };
                let performed = EffectRow {
                    effects: vec![entry],
                    tail: Some(EffTail::Var(tail)),
                };
                self.emit_eff_eq(performed, ctx.eff.clone(), expr.id);
                instantiate(&sig.ret)
            }
            ExprKind::InlineIR(instruction) => {
                // The instruction itself is trusted: it takes whatever type its
                // context demands (a fresh variable solved by the surrounding
                // annotation or return type). Its operands, however, are ordinary
                // value expressions and must be typed.
                for operand in &instruction.binds {
                    self.infer_expr(operand, ctx);
                }
                Ty::Var(self.store.fresh_ty(self.level, expr.id))
            }
            ExprKind::Unary(..) | ExprKind::Binary(..) => {
                // Operators are desugared to method calls during name
                // resolution; reaching one here is a transform bug.
                self.unsupported(expr.id, "raw operator expression");
                Ty::Error
            }
            ExprKind::Incomplete(crate::node_kinds::incomplete_expr::IncompleteExpr::Member(
                Some(receiver),
            )) => {
                self.infer_expr(receiver, ctx);
                Ty::Error
            }
            ExprKind::Incomplete(_) => Ty::Error,
        }
    }
}
