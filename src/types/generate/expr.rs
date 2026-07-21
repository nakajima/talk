use super::*;
use crate::token_kind::TokenKind;

impl<'s, 'a> BodyChecker<'s, 'a> {
    // ----- Expressions -------------------------------------------------

    pub(super) fn infer_expr(&mut self, expr: &Expr, ctx: &Ctx) -> Ty {
        self.infer_expr_with_static_member_reason(expr, ctx, CtReason::Apply)
    }

    fn infer_expr_with_static_member_reason(
        &mut self,
        expr: &Expr,
        ctx: &Ctx,
        reason: CtReason,
    ) -> Ty {
        let ty = self.infer_expr_kind(expr, ctx, reason);
        if self.module_id != ModuleId::Core
            && (matches!(expr.kind, ExprKind::InlineIR(_)) || Self::mentions_raw_ptr(&ty))
        {
            self.require_unsafe(expr.id, ctx);
        }
        self.artifacts.node_types.insert(expr.id, ty.clone());
        ty
    }

    /// Add the intrinsic compile-time capability to this expression's
    /// ambient row. It has no catalog operation and cannot be performed.
    fn require_unsafe(&mut self, node: NodeID, ctx: &Ctx) {
        let tail = self.store.fresh_eff(self.level, node);
        self.emit_eff_eq(
            EffectRow {
                effects: vec![EffectEntry::label(Symbol::Unsafe)],
                tail: Some(EffTail::Var(tail)),
            },
            ctx.eff.clone(),
            node,
        );
    }

    fn mentions_raw_ptr(ty: &Ty) -> bool {
        ty.try_visit(&mut |item| match item {
            Ty::Nominal(symbol, _) if *symbol == Symbol::RawPtr => ControlFlow::Break(()),
            _ => ControlFlow::Continue(()),
        })
        .is_break()
    }

    /// Checking mode: push the expected type inward where syntax allows
    /// (Pierce & Turner; DK 2021's mode recipe), otherwise infer and emit an
    /// equality oriented expected-then-found for blame.
    pub(super) fn check_expr(&mut self, expr: &Expr, expected: &Ty, reason: CtReason, ctx: &Ctx) {
        if let Ty::Borrow(expected_kind, inner) = self.store.shallow(expected) {
            // The auto-borrow peel is position-dependent. It stays for:
            //   - `Apply`: the argument is borrowed for the call's extent;
            //   - `Return`/`Body`: return-position borrows, where flow's
            //     `check_return_provenance` validates the source (tier 1);
            //   - `Assignment`: writing an owned value through a `&mut`
            //     slot is ADR 0018's inout write-back, not aliasing;
            //   - place expressions under any reason: a borrow introduction
            //     (`let x: &T = local`; flow installs the loan).
            // Everything else — an annotation, branch, pattern, or element
            // slot fed a non-place rvalue — demands a genuine borrow:
            // peeling would alias an owned temp that dies at statement end
            // (temp drop + alias-owner drop; ownership-soundness plan S4).
            let peels = matches!(
                reason,
                CtReason::Apply | CtReason::Return | CtReason::Body | CtReason::Assignment
            ) || Self::is_borrowable_place(expr);
            if !peels {
                let found = self.infer_expr(expr, ctx);
                self.check_inferred_against_expected(expr.id, expected, found, reason);
                return;
            }
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

        if self.module_id != ModuleId::Core && Self::mentions_raw_ptr(expected) {
            self.require_unsafe(expr.id, ctx);
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
                if let Ty::Nominal(symbol, args) = self.store.shallow(expected) {
                    if symbol == Symbol::Array
                        && let [element] = args.as_slice()
                    {
                        for item in items {
                            self.check_expr(item, element, CtReason::ArrayElement, ctx);
                        }
                        self.artifacts.node_types.insert(expr.id, expected.clone());
                        return;
                    }
                    if symbol == Symbol::InlineArray
                        && let [element, count] = args.as_slice()
                    {
                        for item in items {
                            self.check_expr(item, element, CtReason::ArrayElement, ctx);
                        }
                        let literal_count = Ty::Static(StaticValue::Int(StaticInt::constant(
                            i64::try_from(items.len()).unwrap_or(i64::MAX),
                        )));
                        self.emit_eq(
                            count.clone(),
                            literal_count,
                            expr.id,
                            CtReason::InlineArrayLength,
                        );
                        self.artifacts.node_types.insert(expr.id, expected.clone());
                        return;
                    }
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
            ExprKind::Unsafe(block) => {
                let inner = self.enter_effect_mask(ctx, Symbol::Unsafe, expr.id);
                self.check_block_value(block, expected, &inner);
                self.artifacts.node_types.insert(expr.id, expected.clone());
            }
            ExprKind::If(..) => {
                unreachable!("if expressions are desugared to match before type checking")
            }
            ExprKind::Match(scrutinee, arms) => {
                self.check_match_expr(scrutinee, arms, expected, reason, ctx);
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

    /// A place expression names borrowable storage: a variable, or a field
    /// path rooted at one. Everything else evaluates to an owned rvalue
    /// temp, which a borrow-typed slot outside an application must reject.
    fn is_borrowable_place(expr: &Expr) -> bool {
        match &expr.kind {
            ExprKind::Variable(_) => true,
            ExprKind::Member(Some(receiver), ..) => Self::is_borrowable_place(receiver),
            _ => false,
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
        // Peeling the expected borrow consumes the application boundary:
        // the inner equation is no longer an application of the value, so
        // `Apply` demotes — a nested function type unifies invariantly
        // instead of coercing its contravariant parameters.
        let inner_reason = reason.nested();
        match self.store.shallow(&found) {
            Ty::Borrow(found_kind, found_inner) if found_kind == expected_kind => {
                self.emit_eq(expected_inner, (*found_inner).clone(), node, inner_reason);
            }
            Ty::Borrow(Perm::Exclusive, found_inner) if expected_kind == Perm::Shared => {
                self.emit_eq(expected_inner, (*found_inner).clone(), node, inner_reason);
            }
            Ty::Borrow(..) => self.emit_eq(expected, found, node, reason),
            // An unresolved found (a call result whose member is still
            // being solved) defers under EVERY reason: eagerly equating
            // the peeled inner would rigidly bind the result var owned,
            // then conflict with the member scheme's borrow-typed return
            // once it resolves (ADR 0021's first-class borrow results).
            Ty::Var(_) => {
                self.wanteds.push(Constraint::ApplyBorrow {
                    expected_perm: expected_kind,
                    expected_inner,
                    found,
                    origin: CtOrigin::new(node, reason),
                });
            }
            _ => self.emit_eq(expected_inner, found, node, inner_reason),
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
        // An owned rigid-`Param` slot fed a still-unsolved argument (a call
        // result whose member is being solved) defers: eagerly equating
        // would bind the result var owned, then conflict with the member
        // scheme's borrow-typed return once it resolves. A rigid param
        // never drives the var's inference, so the deferral loses nothing
        // (ADR 0021's per-instantiation clone coercion).
        let defer_coercion = reason == CtReason::Apply
            && matches!(
                (self.store.shallow(expected), self.store.shallow(&found)),
                (Ty::Param(_), Ty::Var(_) | Ty::Borrow(..)) | (Ty::Var(_), Ty::Borrow(..))
            );
        if defer_coercion {
            self.wanteds.push(Constraint::CoerceOwned {
                expected: expected.clone(),
                found,
                origin: CtOrigin::new(node, reason),
            });
            return;
        }
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
            protocol: protocol.clone(),
            origin: CtOrigin::new(node, reason),
        });
        for (assoc_symbol, assoc_ty) in &assoc {
            self.wanteds.push(Constraint::Eq(
                Ty::Proj(Box::new(found.clone()), protocol.clone(), *assoc_symbol),
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
        self.check_match_arms_against(scrutinee, arms, &result, None, ctx);
        result
    }

    fn enum_hint_from_match_arms(&mut self, arms: &[MatchArm], node: NodeID) -> Option<Ty> {
        let mut names = vec![];
        for arm in arms {
            collect_top_level_variant_names(&arm.pattern, &mut names);
        }
        if names.is_empty() {
            return None;
        }
        names.sort();
        names.dedup();

        let mut candidates = self
            .catalog
            .enums
            .iter()
            .filter(|(_, info)| names.iter().all(|name| info.variants.contains_key(name)));
        let (symbol, info) = candidates.next()?;
        if candidates.next().is_some() {
            return None;
        }
        let symbol = *symbol;
        let param_count = info.params.len();
        let args = (0..param_count)
            .map(|_| Ty::Var(self.store.fresh_ty(self.level, node)))
            .collect();
        Some(Ty::Nominal(symbol, args))
    }

    pub(super) fn check_match_expr(
        &mut self,
        scrutinee: &Expr,
        arms: &[MatchArm],
        expected: &Ty,
        reason: CtReason,
        ctx: &Ctx,
    ) {
        self.check_match_arms_against(scrutinee, arms, expected, Some(reason), ctx);
    }

    pub(super) fn check_match_arms_against(
        &mut self,
        scrutinee: &Expr,
        arms: &[MatchArm],
        expected: &Ty,
        checking_reason: Option<CtReason>,
        ctx: &Ctx,
    ) {
        // OutsideIn(X) checks each GADT arm under an implication: constructor
        // equalities are givens, arm-local unification variables are
        // touchable, and outer variables stay untouchable.
        let scrutinee_ty = self.infer_expr(scrutinee, ctx);
        self.check_match_arms_against_known_scrutinee(
            scrutinee,
            scrutinee_ty,
            arms,
            expected,
            checking_reason,
            ctx,
        );
    }

    fn check_match_arms_against_known_scrutinee(
        &mut self,
        scrutinee: &Expr,
        scrutinee_ty: Ty,
        arms: &[MatchArm],
        expected: &Ty,
        checking_reason: Option<CtReason>,
        ctx: &Ctx,
    ) {
        // Every arm shares one view of the root occurrence. Recursive
        // aggregate projections create their own views in `check_pattern`.
        let pattern_scrutinee_ty = match self.store.shallow(&scrutinee_ty) {
            Ty::Borrow(_, inner) => *inner,
            Ty::Var(id) => {
                // Several enums may share one case name (`Result.ok` and
                // `Scan.ok`). Use every top-level variant named by the match
                // before checking the first arm; their intersection often
                // identifies the enum even while the scrutinee call is still
                // an unsolved variable.
                let view = self
                    .enum_hint_from_match_arms(arms, scrutinee.id)
                    .unwrap_or_else(|| Ty::Var(self.store.fresh_ty(self.level, scrutinee.id)));
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
            let refinement = self.check_pattern_viewed(&arm.pattern, &pattern_scrutinee_ty);
            let reason = match (checking_reason, refinement.is_empty()) {
                (Some(CtReason::Recursion), _) => CtReason::Branch,
                (Some(reason), _) => reason,
                (None, false) => CtReason::GadtBranch,
                (None, true) => CtReason::Branch,
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

    fn propagation_binders(
        &mut self,
        source: &Expr,
        prefix: &str,
        count: usize,
    ) -> Vec<(Pattern, Name)> {
        (0..count)
            .map(|index| {
                let id = self.artifacts.synthetic_id(source.id.0);
                let symbol = Symbol::PatternBindLocal(self.symbols.next_pattern_bind());
                let text = format!("__{prefix}_{index}_{}", source.id.1);
                self.artifacts.display_names.insert(symbol, text.clone());
                let name = Name::Resolved(symbol, text);
                (
                    Pattern {
                        id,
                        kind: PatternKind::Bind(name.clone()),
                        span: source.span,
                    },
                    name,
                )
            })
            .collect()
    }

    fn propagation_value(&mut self, source: &Expr, binders: &[(Pattern, Name)]) -> Expr {
        let mut values = binders
            .iter()
            .map(|(_, name)| Expr {
                id: self.artifacts.synthetic_id(source.id.0),
                kind: ExprKind::Variable(name.clone()),
                span: source.span,
            })
            .collect::<Vec<_>>();
        let kind = match values.len() {
            0 => ExprKind::Tuple(vec![]),
            1 => values
                .pop()
                .map_or(ExprKind::Tuple(vec![]), |value| value.kind),
            _ => ExprKind::Tuple(values),
        };
        Expr {
            id: self.artifacts.synthetic_id(source.id.0),
            kind,
            span: source.span,
        }
    }

    fn propagation_constructor(
        &mut self,
        source: &Expr,
        enum_symbol: Symbol,
        enum_name: &str,
        variant_name: &str,
        variant: &Variant,
        binders: &[(Pattern, Name)],
    ) -> Expr {
        let receiver = Expr {
            id: self.artifacts.synthetic_id(source.id.0),
            kind: ExprKind::Constructor(Name::Resolved(enum_symbol, enum_name.into())),
            span: source.span,
        };
        let member = Expr {
            id: self.artifacts.synthetic_id(source.id.0),
            kind: ExprKind::Member(
                Some(Box::new(receiver)),
                Label::Named(variant_name.into()),
                source.span,
            ),
            span: source.span,
        };
        if binders.is_empty() {
            return member;
        }
        let args = binders
            .iter()
            .enumerate()
            .map(|(index, (_, name))| CallArg {
                id: self.artifacts.synthetic_id(source.id.0),
                span: source.span,
                label: variant
                    .payload_labels
                    .get(index)
                    .and_then(Option::as_ref)
                    .map_or(Label::Positional(index), |label| {
                        Label::Named(label.clone())
                    }),
                label_span: source.span,
                value: Expr {
                    id: self.artifacts.synthetic_id(source.id.0),
                    kind: ExprKind::Variable(name.clone()),
                    span: source.span,
                },
                mode: None,
                mode_span: None,
            })
            .collect();
        Expr {
            id: self.artifacts.synthetic_id(source.id.0),
            kind: ExprKind::Call {
                callee: Box::new(member),
                type_args: vec![],
                args,
                trailing_block: None,
                desugared_operator: Some(TokenKind::QuestionMark),
            },
            span: source.span,
        }
    }

    fn propagation_arm(
        &mut self,
        source: &Expr,
        enum_symbol: Symbol,
        enum_name: &str,
        variant_name: &str,
        variant: &Variant,
        returns: bool,
    ) -> MatchArm {
        let binders =
            self.propagation_binders(source, variant_name, variant.argument_types().len());
        let pattern = Pattern {
            id: self.artifacts.synthetic_id(source.id.0),
            kind: PatternKind::Variant {
                enum_name: Some(Name::Resolved(enum_symbol, enum_name.into())),
                variant_name: variant_name.into(),
                variant_name_span: source.span,
                fields: binders.iter().map(|(pattern, _)| pattern.clone()).collect(),
                field_labels: variant
                    .payload_labels
                    .iter()
                    .map(|label| label.as_ref().map(|label| Name::Raw(label.clone())))
                    .collect(),
            },
            span: source.span,
        };
        let value = if returns {
            self.propagation_constructor(
                source,
                enum_symbol,
                enum_name,
                variant_name,
                variant,
                &binders,
            )
        } else {
            self.propagation_value(source, &binders)
        };
        let body_node = if returns {
            Node::Stmt(Stmt {
                id: self.artifacts.synthetic_id(source.id.0),
                kind: StmtKind::Return(Some(value)),
                span: source.span,
            })
        } else {
            Node::Expr(value)
        };
        MatchArm {
            id: self.artifacts.synthetic_id(source.id.0),
            pattern,
            body: Block {
                id: self.artifacts.synthetic_id(source.id.0),
                args: vec![],
                body: vec![body_node],
                span: source.span,
            },
            span: source.span,
        }
    }

    fn infer_propagation(&mut self, expr: &Expr, source: &Expr, ctx: &Ctx) -> Ty {
        let source_ty = self.infer_expr(source, ctx);
        if !ctx.has_return_boundary {
            self.diagnostics.errors.push((
                TypeError::InvalidEarlyPropagation {
                    reason: "there is no enclosing function return boundary".into(),
                },
                expr.id,
            ));
            return Ty::Error;
        }

        let nominal_symbol = |ty: Ty| match ty {
            Ty::Nominal(symbol, _) if self.catalog.enums.contains_key(&symbol) => Some(symbol),
            Ty::Borrow(_, inner) => match *inner {
                Ty::Nominal(symbol, _) if self.catalog.enums.contains_key(&symbol) => Some(symbol),
                _ => None,
            },
            _ => None,
        };
        let source_symbol = nominal_symbol(self.store.shallow(&source_ty));
        let return_symbol = nominal_symbol(self.store.shallow(&ctx.ret));
        let enum_symbol = match (source_symbol, return_symbol) {
            (Some(source), Some(ret)) if source != ret => {
                self.diagnostics.errors.push((
                    TypeError::InvalidEarlyPropagation {
                        reason: format!(
                            "the operand and enclosing return type use different enums ({} and {})",
                            self.store.render(&source_ty),
                            self.store.render(&ctx.ret)
                        ),
                    },
                    expr.id,
                ));
                return Ty::Error;
            }
            (Some(symbol), _) | (_, Some(symbol)) => symbol,
            _ => {
                self.diagnostics.errors.push((
                    TypeError::InvalidEarlyPropagation {
                        reason: "the operand or enclosing return type must identify an enum".into(),
                    },
                    expr.id,
                ));
                return Ty::Error;
            }
        };
        let Some(info) = self.catalog.enums.get(&enum_symbol).cloned() else {
            unreachable!("the selected propagation symbol was checked as an enum")
        };
        if info.variants.len() != 2 {
            self.diagnostics.errors.push((
                TypeError::InvalidEarlyPropagation {
                    reason: format!(
                        "{} has {} variants; propagation requires exactly two",
                        self.store.render(&Ty::Nominal(enum_symbol, vec![])),
                        info.variants.len()
                    ),
                },
                expr.id,
            ));
            return Ty::Error;
        }
        let enum_name = self
            .artifacts
            .display_names
            .get(&enum_symbol)
            .cloned()
            .unwrap_or_else(|| enum_symbol.to_string());
        let (first_name, first) = info.variants.get_index(0).expect("two variants");
        let (second_name, second) = info.variants.get_index(1).expect("two variants");
        let arms = vec![
            self.propagation_arm(source, enum_symbol, &enum_name, first_name, first, false),
            self.propagation_arm(source, enum_symbol, &enum_name, second_name, second, true),
        ];
        let lowered_id = self.artifacts.synthetic_id(source.id.0);
        let result = Ty::Var(self.store.fresh_ty(self.level, expr.id));
        self.check_match_arms_against_known_scrutinee(source, source_ty, &arms, &result, None, ctx);
        let lowered = Expr {
            id: lowered_id,
            kind: ExprKind::Match(Box::new(source.clone()), arms),
            span: expr.span,
        };
        self.artifacts.node_types.insert(lowered_id, result.clone());
        self.artifacts
            .propagation_plans
            .insert(expr.id, PropagationPlan { lowered });
        result
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
        self.validate_variant_payload_labels(
            &label.to_string(),
            &variant,
            &args.iter().map(|arg| arg.label.clone()).collect::<Vec<_>>(),
            expr.id,
        );
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

    pub(super) fn validate_variant_payload_labels(
        &mut self,
        variant_name: &str,
        variant: &Variant,
        labels: &[Label],
        node: NodeID,
    ) {
        if !variant.payload_labels_match(labels) {
            self.diagnostics.errors.push((
                TypeError::InvalidVariantPayloadLabels {
                    variant: variant_name.into(),
                },
                node,
            ));
        }
    }

    pub(super) fn infer_expr_kind(
        &mut self,
        expr: &Expr,
        ctx: &Ctx,
        static_member_reason: CtReason,
    ) -> Ty {
        match &expr.kind {
            ExprKind::LiteralInt(source) => {
                self.check_integer_literal(expr.id, source);
                Ty::Nominal(Symbol::Int, vec![])
            }
            ExprKind::LiteralFloat(_) => Ty::Nominal(Symbol::Float, vec![]),
            ExprKind::LiteralTrue | ExprKind::LiteralFalse => Ty::Nominal(Symbol::Bool, vec![]),
            ExprKind::LiteralString(_) => Ty::Nominal(Symbol::String, vec![]),
            ExprKind::LiteralCharacter(_) => Ty::Nominal(Symbol::Character, vec![]),

            ExprKind::LiteralArray(items) => {
                let element = Ty::Var(self.store.fresh_ty(self.level, expr.id));
                for item in items {
                    self.check_expr(item, &element, CtReason::ArrayElement, ctx);
                }
                Ty::Nominal(Symbol::Array, vec![element])
            }

            ExprKind::Propagate(source) => self.infer_propagation(expr, source, ctx),
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
            ExprKind::Unsafe(block) => {
                let inner = self.enter_effect_mask(ctx, Symbol::Unsafe, expr.id);
                self.infer_block_value(block, &inner)
            }

            ExprKind::If(..) => {
                unreachable!("if expressions are desugared to match before type checking")
            }

            ExprKind::Match(scrutinee, arms) => {
                self.infer_match_expr(expr.id, scrutinee, arms, ctx)
            }

            // Trailing blocks desugared to ordinary anonymous-function
            // arguments before name resolution; the surface field is
            // always empty here.
            ExprKind::Call {
                callee,
                type_args,
                args,
                desugared_operator,
                ..
            } => {
                if let ExprKind::Constructor(_) = &callee.kind {
                    return self.infer_construction(expr, callee, type_args, args, ctx);
                }
                if let ExprKind::Member(Some(receiver), label, _) = &callee.kind
                    && let ExprKind::Constructor(name) = &receiver.kind
                    && let Ok(symbol) = name.symbol()
                    && let Some(variant) = self
                        .catalog
                        .enums
                        .get(&symbol)
                        .and_then(|info| info.variants.get(&label.to_string()))
                        .cloned()
                {
                    self.validate_variant_payload_labels(
                        &label.to_string(),
                        &variant,
                        &args.iter().map(|arg| arg.label.clone()).collect::<Vec<_>>(),
                        expr.id,
                    );
                }
                if let ExprKind::Member(Some(receiver), _, _) = &callee.kind
                    && !matches!(receiver.kind, ExprKind::Constructor(_))
                {
                    if !type_args.is_empty() {
                        self.unsupported(expr.id, "type arguments on method calls");
                    }
                    return self.infer_member_call(expr, callee, args, ctx);
                }
                // A leading-dot construction whose enum is not yet known:
                // infer the payload, hand the resolution to the solver. The
                // callee node gets a variable unified with the constructor's
                // function type on discharge.
                if let ExprKind::Member(None, label, _) = &callee.kind
                    && type_args.is_empty()
                {
                    let payload: Vec<(Label, Ty)> = args
                        .iter()
                        .map(|arg| (arg.label.clone(), self.infer_expr(&arg.value, ctx)))
                        .collect();
                    let result = Ty::Var(self.store.fresh_ty(self.level, expr.id));
                    let ctor = Ty::Var(self.store.fresh_ty(self.level, callee.id));
                    self.artifacts.node_types.insert(callee.id, ctor.clone());
                    self.wanteds.push(Constraint::HasVariant {
                        enum_ty: result.clone(),
                        label: label.clone(),
                        payload,
                        ctor: Some(ctor),
                        origin: CtOrigin::new(expr.id, CtReason::Apply),
                    });
                    return result;
                }
                let callee_reason = match desugared_operator {
                    Some(TokenKind::EqualsEquals | TokenKind::BangEquals) => {
                        CtReason::EqualityComparison
                    }
                    _ => CtReason::Apply,
                };
                let callee_ty =
                    self.infer_expr_with_static_member_reason(callee, ctx, callee_reason);
                if !type_args.is_empty() {
                    self.apply_type_args(callee.id, type_args);
                }
                self.finish_call(expr.id, callee_ty, args, ctx)
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
                    return match self.resolve_type_member(
                        symbol,
                        label,
                        expr.id,
                        static_member_reason,
                    ) {
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
            // A leading dot in inference position: the enum arrives through
            // unification, not the checking mode, so resolution defers to
            // the solver (the same discipline as `HasMember`).
            ExprKind::Member(None, label, _) => {
                let result = Ty::Var(self.store.fresh_ty(self.level, expr.id));
                self.wanteds.push(Constraint::HasVariant {
                    enum_ty: result.clone(),
                    label: label.clone(),
                    payload: vec![],
                    ctor: None,
                    origin: CtOrigin::new(expr.id, CtReason::Apply),
                });
                result
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
                if symbol == Symbol::Unsafe {
                    self.unsupported(
                        expr.id,
                        "the intrinsic `'unsafe` effect cannot be performed; use `@unsafe { ... }`",
                    );
                    return Ty::Error;
                }
                let Some(sig) = self.catalog.effects.get(&symbol).cloned() else {
                    self.unsupported(expr.id, "calling an undeclared effect");
                    return Ty::Error;
                };
                // A generic effect instantiates fresh at each perform
                // (Damas-Milner instantiation, exactly like schemes);
                // explicit type arguments equate positionally by the
                // parameter's kind. The handler sees the rigid
                // parameters instead — it must be generic over them.
                let mut tys: FxHashMap<Symbol, Ty> = FxHashMap::default();
                for (index, param) in sig.generics.iter().enumerate() {
                    let fresh = self.store.fresh_ty(self.level, expr.id);
                    if let crate::types::ty::ParamKind::Static(value_ty) = &param.kind {
                        self.store.mark_static_hole(fresh);
                        // ADR 0035 §2: performing forms an application;
                        // every integer static argument owes
                        // nonnegativity. An explicit argument owns the
                        // obligation; the hole covers inferred and
                        // defaulted slots.
                        if index >= type_args.len()
                            && matches!(value_ty, Ty::Nominal(symbol, _) if *symbol == Symbol::Int)
                        {
                            self.wanteds.push(Constraint::StaticCmp {
                                op: crate::types::ty::StaticCmpOp::Le,
                                lhs: Ty::Static(StaticValue::Int(StaticInt::constant(0))),
                                rhs: Ty::Var(fresh),
                                origin: CtOrigin::new(expr.id, CtReason::Apply),
                            });
                        }
                    }
                    tys.insert(param.symbol, Ty::Var(fresh));
                }
                if !tys.is_empty() {
                    self.artifacts
                        .instantiations
                        .entry(expr.id)
                        .or_default()
                        .extend(
                            sig.generics
                                .iter()
                                .map(|param| (param.symbol, tys[&param.symbol].clone())),
                        );
                }
                if type_args.len() > sig.generics.len() {
                    self.unsupported(expr.id, "more type arguments than the effect declares");
                }
                for (type_arg, param) in type_args.iter().zip(&sig.generics) {
                    let annotated = self.lower_generic_arg_for_param(param.symbol, type_arg);
                    self.emit_eq(
                        tys[&param.symbol].clone(),
                        annotated,
                        expr.id,
                        CtReason::Annotation,
                    );
                }
                // Omitted trailing arguments fall back to their declared
                // defaults (PreferEq — inference or an explicit argument
                // wins), exactly like scheme instantiation.
                for index in type_args.len()..sig.generics.len() {
                    let Some(default) = sig.generics[index].default.clone() else {
                        continue;
                    };
                    if matches!(default, Ty::Error) {
                        continue;
                    }
                    let default =
                        default.substitute(&tys, &Default::default(), &Default::default());
                    self.wanteds.push(Constraint::PreferEq(
                        tys[&sig.generics[index].symbol].clone(),
                        default,
                        CtOrigin::new(expr.id, CtReason::Annotation),
                    ));
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
                    args: sig
                        .generics
                        .iter()
                        .map(|param| tys[&param.symbol].clone())
                        .collect(),
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
                // Operators are desugared to protocol calls before name
                // resolution; reaching one here is a transform bug.
                self.unsupported(expr.id, "raw operator expression");
                Ty::Error
            }
            ExprKind::Subscript(..) => {
                self.unsupported(expr.id, "raw subscript expression");
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

fn collect_top_level_variant_names(pattern: &Pattern, names: &mut Vec<String>) {
    match &pattern.kind {
        PatternKind::Variant { variant_name, .. } => names.push(variant_name.clone()),
        PatternKind::Or(alternatives) => {
            for alternative in alternatives {
                collect_top_level_variant_names(alternative, names);
            }
        }
        _ => {}
    }
}
