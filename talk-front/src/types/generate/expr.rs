use super::*;
use crate::token_kind::TokenKind;

enum BinaryEnumArm<'a> {
    Value,
    Return,
    Failure(&'a Expr),
}

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
    /// Checking a value against a first-class scheme (rank-N field
    /// subsumption): the value must satisfy the scheme's body for every
    /// choice of its parameters. The parameters are already rigid —
    /// skolems by construction — so wrapping the check in an
    /// implication with them as local parameters rejects (via the
    /// escape check) a value that commits one to a concrete type, and
    /// the scheme's predicates act as givens: a reference whose own
    /// bounds the declared bounds imply discharges, a weaker one
    /// escapes. The field's scheme is baked as the value's node type so
    /// lowering compiles it against the projections' agreed assignment.
    fn check_against_forall(&mut self, expr: &Expr, scheme: &Scheme, reason: CtReason, ctx: &Ctx) {
        let wanted_start = self.wanteds.len();
        self.check_expr(expr, &scheme.ty, reason, ctx);
        let wanteds = self.wanteds.split_off(wanted_start);
        self.wanteds.push(Constraint::Implic(Box::new(Implication {
            node: expr.id,
            level: self.level,
            givens: scheme.predicates.clone(),
            wanteds,
            local_params: scheme.params.iter().map(|param| param.symbol).collect(),
            touchable_level: None,
        })));
        let ty = Ty::Forall(Box::new(scheme.clone()));
        self.artifacts.node_types.insert(expr.id, ty.clone());
        if let ExprKind::Func(func) = &expr.kind
            && func.id != expr.id
        {
            self.artifacts.node_types.insert(func.id, ty);
        }
    }

    pub(super) fn check_expr(&mut self, expr: &Expr, expected: &Ty, reason: CtReason, ctx: &Ctx) {
        // A first-class scheme in expected position (a declared rank-N
        // field): the value must satisfy the type for EVERY choice of
        // the quantified parameters, so it checks against the body
        // under the scheme's own rigids and predicates — an
        // implication whose skolems the value may not pin.
        if let Ty::Forall(scheme) = self.store.shallow(expected) {
            return self.check_against_forall(expr, &scheme, reason, ctx);
        }
        if let Ty::Borrow(_, inner) = self.store.shallow(expected) {
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
            // A borrow source may already hold or produce a first-class
            // borrow, so it reconciles against the borrow-typed slot
            // directly (loan installation, permission matching, and the
            // deferred borrow-result judgment). Everything else is a
            // construction: it can only build an owned value, so checking
            // mode continues against the peeled inner type — coercion
            // sites propagate through literals, match arms, and block
            // tails (Rust RFC 401's coercion-propagating expressions) —
            // and the built value is borrowed at the boundary.
            if Self::is_borrow_source(expr) {
                let found = self.infer_expr(expr, ctx);
                self.emit_immediate_argument_eq(expected, found, expr.id, reason);
                return;
            }
            self.check_expr(expr, &inner, reason, ctx);
            return;
        }

        if self.module_id != ModuleId::Core && Self::mentions_raw_ptr(expected) {
            self.require_unsafe(expr.id, ctx);
        }

        match &expr.kind {
            // The expected type is the implicit receiver for a leading-dot
            // expression. A known nominal resolves immediately; an unknown
            // head defers through the shared enum-case/static-function path.
            ExprKind::Member(None, label, _) => {
                if let Ty::Nominal(symbol, _) = self.store.shallow(expected) {
                    match self.resolve_type_member(symbol, &[], label, expr.id, reason) {
                        Some(found) => {
                            self.emit_eq(expected.clone(), found, expr.id, reason);
                            self.artifacts.node_types.insert(expr.id, expected.clone());
                        }
                        None => {
                            self.wanteds.push(Constraint::HasTypeMember {
                                receiver: expected.clone(),
                                label: label.clone(),
                                payload: vec![],
                                ctor: None,
                                allowed_effects: None,
                                member_node: expr.id,
                                origin: CtOrigin::new(expr.id, reason),
                            });
                            self.artifacts.node_types.insert(expr.id, expected.clone());
                        }
                    }
                } else {
                    let found = self.infer_expr(expr, ctx);
                    self.check_inferred_against_expected(expr.id, expected, found, reason);
                }
            }
            ExprKind::Call {
                callee,
                type_args,
                args,
                ..
            } if matches!(callee.kind, ExprKind::Member(None, ..)) => {
                if let Ty::Nominal(symbol, _) = self.store.shallow(expected) {
                    let ExprKind::Member(None, label, _) = &callee.kind else {
                        unreachable!("guarded above")
                    };
                    self.artifacts.member_call_slots.insert(
                        callee.id,
                        args.iter()
                            .map(crate::types::callables::WrittenSlot::of)
                            .collect(),
                    );
                    let variant = self
                        .catalog
                        .enums
                        .get(&symbol)
                        .and_then(|info| info.variants.get(&label.to_string()))
                        .cloned();
                    if let Some(variant) = &variant {
                        self.validate_variant_payload_labels(
                            &label.to_string(),
                            variant,
                            &args.iter().map(|arg| arg.label.clone()).collect::<Vec<_>>(),
                            expr.id,
                        );
                    }
                    match self.resolve_type_member(symbol, &[], label, callee.id, reason) {
                        Some(member) => {
                            self.artifacts.node_types.insert(callee.id, member.clone());
                            let result = self.finish_call_with_result_origin(
                                expr.id,
                                expr.id,
                                format!("Type member '{label}'"),
                                member,
                                args,
                                variant.is_some(),
                                ctx,
                            );
                            self.emit_eq(expected.clone(), result, expr.id, reason);
                            if !type_args.is_empty() {
                                self.apply_type_args(
                                    callee.id,
                                    format!("Type member '{label}'"),
                                    type_args,
                                );
                            }
                            self.artifacts.node_types.insert(expr.id, expected.clone());
                        }
                        None => {
                            let payload: Vec<(Label, Ty)> = args
                                .iter()
                                .map(|arg| (arg.label.clone(), self.infer_expr(&arg.value, ctx)))
                                .collect();
                            let ctor = Ty::Var(self.store.fresh_ty(self.level, callee.id));
                            self.artifacts.node_types.insert(callee.id, ctor.clone());
                            for (index, (arg, (_, arg_ty))) in args.iter().zip(&payload).enumerate()
                            {
                                self.note_indexed_marker(arg, &ctor, index, args.len(), arg_ty);
                            }
                            self.wanteds.push(Constraint::HasTypeMember {
                                receiver: expected.clone(),
                                label: label.clone(),
                                payload,
                                ctor: Some(ctor),
                                allowed_effects: Some(ctx.eff.clone()),
                                member_node: callee.id,
                                origin: CtOrigin::new(expr.id, reason),
                            });
                            self.artifacts.node_types.insert(expr.id, expected.clone());
                        }
                    }
                } else {
                    let found = self.infer_expr(expr, ctx);
                    self.check_inferred_against_expected(expr.id, expected, found, reason);
                }
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
            ExprKind::LiteralString(_)
                if matches!(
                    self.store.shallow(expected),
                    Ty::Nominal(symbol, args)
                        if symbol == Symbol::Static
                            && matches!(args.as_slice(), [Ty::Nominal(inner, args)]
                                if *inner == Symbol::String && args.is_empty())
                ) =>
            {
                self.artifacts.node_types.insert(expr.id, expected.clone());
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
                    let result_reason = if matches!(reason, CtReason::Apply | CtReason::NestedApply)
                    {
                        CtReason::CallbackResult
                    } else {
                        CtReason::Body
                    };
                    let ty = self.infer_func_against(func, &params, &ret, &eff, result_reason, ctx);
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

    /// An expression whose value may already be a first-class borrow: a
    /// place read (variable, member path, subscript), any call or
    /// operator application, an effect perform, a cast, inline IR, a
    /// bare name reference, or a recovery node whose type is opaque.
    /// These reconcile against a borrow-typed slot through the
    /// immediate-borrow machinery. Every other expression is a
    /// construction that can only produce an owned value, so checking
    /// mode pushes the slot's inner type into it — an overlooked kind
    /// here degrades to donation (an extra retain), never to rejection.
    fn is_borrow_source(expr: &Expr) -> bool {
        match &expr.kind {
            ExprKind::Variable(..)
            | ExprKind::Member(Some(_), ..)
            | ExprKind::Subscript(..)
            | ExprKind::Binary(..)
            | ExprKind::Unary(..)
            | ExprKind::Propagate(..)
            | ExprKind::ForceUnwrap(..)
            | ExprKind::CallEffect { .. }
            | ExprKind::InlineIR(..)
            | ExprKind::As(..)
            | ExprKind::MacroCall { .. }
            | ExprKind::Incomplete(..)
            | ExprKind::Constructor(..) => true,
            // Leading-dot calls construct variants; every other call's
            // result is opaque until its member or scheme resolves.
            ExprKind::Call { callee, .. } => !matches!(callee.kind, ExprKind::Member(None, ..)),
            _ => false,
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
        use crate::types::adapt::{Adapted, Site, adapt};
        match adapt(self.store, self.catalog, expected, &found, Site::Argument) {
            // Peeling an ownership wrapper consumes the application
            // boundary: the inner equation is no longer an application of
            // the value, so `Apply` demotes — a nested function type
            // unifies invariantly instead of coercing its contravariant
            // parameters.
            Adapted::Eq {
                expected,
                found,
                peeled,
            } => {
                let reason = if peeled { reason.nested() } else { reason };
                self.emit_eq(expected, found, node, reason);
            }
            Adapted::Mismatch { expected, found } => {
                self.emit_eq(expected, found, node, reason)
            }
            // A convertible crossing defers like a donation (the argument
            // node here is exactly the node the conversion wraps); the
            // solver's dispatcher re-judges and the final solve commits
            // the inserted `.into()`.
            Adapted::Convert { .. } => {
                self.wanteds.push(Constraint::Adapt {
                    expected: expected.clone(),
                    found,
                    node_is_value: true,
                    origin: CtOrigin::new(node, reason),
                });
            }
            // Donation evidence and its diagnostics belong to the solver's
            // `Adapt` dispatcher; generation only flags the crossing. An
            // unresolved found with a borrow in sight waits with it
            // (ADR 0021's first-class borrow results).
            Adapted::Donate { .. }
            | Adapted::NoEvidence { .. }
            | Adapted::Unresolved {
                visible_borrow: true,
            }
            | Adapted::PeelableProjection { .. } => {
                self.wanteds.push(Constraint::Adapt {
                    expected: expected.clone(),
                    found,
                    node_is_value: true,
                    origin: CtOrigin::new(node, reason),
                });
            }
            Adapted::Unresolved {
                visible_borrow: false,
            } => self.emit_eq(expected.clone(), found, node, reason),
            Adapted::Silent => {}
        }
    }

    pub(super) fn emit_borrow_downgrade_or_eq(
        &mut self,
        expected: Ty,
        found: Ty,
        node: crate::node_id::NodeID,
        reason: CtReason,
    ) {
        use crate::types::adapt::{Adapted, Site, adapt};
        match adapt(self.store, self.catalog, &expected, &found, Site::Result) {
            Adapted::Eq {
                expected, found, ..
            } => self.emit_eq(expected, found, node, reason),
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
        // A borrow-shaped value (or a projection that may still resolve to
        // one — a member result reduces only after its head is solved)
        // checking against an owned slot is the value-boundary coercion:
        // under implicit sharing the borrow satisfies the slot by donating
        // a retain, and the solver's constraint waits out late heads
        // before judging. Bare vars keep the eager equality — checking-
        // mode unification is what drives inference — except the original
        // rigid-`Param`-slot deferral (ADR 0021), where eager equating
        // would bind the result var owned and then conflict with a
        // borrow-typed member return.
        let defer_coercion = match (self.store.shallow(expected), self.store.shallow(&found)) {
            // Borrow-expected slots peeled in `check_expr`; an unsolved
            // slot must keep the eager equality that drives inference,
            // except the legacy Apply deferrals above.
            (Ty::Borrow(..), _) => false,
            (Ty::Var(_), Ty::Borrow(..)) => {
                matches!(reason, CtReason::Apply | CtReason::ArrayElement)
            }
            (Ty::Param(_), Ty::Var(_)) => reason == CtReason::Apply,
            (Ty::Var(_), _) => false,
            // A concrete owned slot fed a still-unsolved value: the value
            // may yet resolve borrowed (a binding whose initializer is a
            // member projection), so the judgment waits. Quiescence
            // defaults leftovers to the plain equality.
            (_, Ty::Borrow(..) | Ty::Proj(..) | Ty::Var(_)) => true,
            _ => false,
        };
        if defer_coercion {
            self.wanteds.push(Constraint::Adapt {
                expected: expected.clone(),
                found,
                node_is_value: true,
                origin: CtOrigin::new(node, reason),
            });
            return;
        }
        // A convertible crossing — distinct resolved monotypes with
        // exactly one declared `Into` row — defers to the solver's Adapt
        // dispatcher; the final solve commits the inserted `.into()`.
        // Everything reaching this funnel is a checking-mode value
        // position, so the coercion-eligible sites are exactly the
        // callers': no reason filter is needed.
        if crate::types::adapt::conversion(self.store, self.catalog, expected, &found).is_some() {
            self.wanteds.push(Constraint::Adapt {
                expected: expected.clone(),
                found,
                node_is_value: true,
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
            // Arm roots check against the match's already-viewed
            // scrutinee; publish their occurrence type too (ADR 0038).
            self.artifacts
                .pattern_tys
                .insert(arm.pattern.id, pattern_scrutinee_ty.clone());
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
                    node: arm.pattern.id,
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
                let id = self.artifacts.synthetic_id(source.id);
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
                id: self.artifacts.synthetic_id(source.id),
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
            id: self.artifacts.synthetic_id(source.id),
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
            id: self.artifacts.synthetic_id(source.id),
            kind: ExprKind::Constructor(Name::Resolved(enum_symbol, enum_name.into()), vec![]),
            span: source.span,
        };
        let member = Expr {
            id: self.artifacts.synthetic_id(source.id),
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
                origin: crate::node_kinds::call_arg::CallArgOrigin::Synthesized,
                id: self.artifacts.synthetic_id(source.id),
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
                    id: self.artifacts.synthetic_id(source.id),
                    kind: ExprKind::Variable(name.clone()),
                    span: source.span,
                },
                mode: None,
                mode_span: None,
            })
            .collect();
        Expr {
            id: self.artifacts.synthetic_id(source.id),
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
        action: BinaryEnumArm<'_>,
    ) -> MatchArm {
        let binders =
            self.propagation_binders(source, variant_name, variant.argument_types().len());
        let pattern = Pattern {
            id: self.artifacts.synthetic_id(source.id),
            kind: PatternKind::Variant {
                enum_name: Some(Name::Resolved(enum_symbol, enum_name.into())),
                enum_generics: vec![],
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
        let body_node = match action {
            BinaryEnumArm::Value => Node::Expr(self.propagation_value(source, &binders)),
            BinaryEnumArm::Return => {
                let value = self.propagation_constructor(
                    source,
                    enum_symbol,
                    enum_name,
                    variant_name,
                    variant,
                    &binders,
                );
                Node::Stmt(Stmt {
                    id: self.artifacts.synthetic_id(source.id),
                    kind: StmtKind::Return(Some(value)),
                    span: source.span,
                })
            }
            BinaryEnumArm::Failure(failure) => Node::Expr(failure.clone()),
        };
        MatchArm {
            id: self.artifacts.synthetic_id(source.id),
            pattern,
            body: Block {
                id: self.artifacts.synthetic_id(source.id),
                args: vec![],
                body: vec![body_node],
                span: source.span,
            },
            span: source.span,
        }
    }

    fn invalid_binary_enum_postfix(
        &mut self,
        node: NodeID,
        force_unwrap: bool,
        reason: impl Into<String>,
    ) {
        let reason = reason.into();
        let error = if force_unwrap {
            TypeError::InvalidForceUnwrap { reason }
        } else {
            TypeError::InvalidEarlyPropagation { reason }
        };
        self.diagnostics.errors.push((error, node));
    }

    fn infer_propagation(&mut self, expr: &Expr, source: &Expr, ctx: &Ctx) -> Ty {
        let source_ty = self.infer_expr(source, ctx);
        let result = Ty::Var(self.store.fresh_ty(self.level, expr.id));
        self.check_binary_enum_postfix(expr, source, None, ctx, source_ty, result)
    }

    fn infer_force_unwrap(&mut self, expr: &Expr, source: &Expr, failure: &Expr, ctx: &Ctx) -> Ty {
        let source_ty = self.infer_expr(source, ctx);
        let result = Ty::Var(self.store.fresh_ty(self.level, expr.id));
        let mut head = self.store.shallow(&source_ty);
        while let Ty::Borrow(_, inner) = head {
            head = self.store.shallow(&inner);
        }
        if matches!(head, Ty::Var(_) | Ty::Proj(..)) {
            // The hidden `unreachable` already contributes `'panic` even
            // though the enum match must wait for the operand's head. This
            // keeps the surrounding effect row open through the first solve.
            self.infer_expr(failure, ctx);
            self.pending_force_unwraps.push(PendingForceUnwrap {
                expr: expr.clone(),
                source: source.clone(),
                failure: failure.clone(),
                source_ty,
                result: result.clone(),
                ctx: ctx.clone(),
                level: self.level,
            });
            return result;
        }
        self.check_binary_enum_postfix(expr, source, Some(failure), ctx, source_ty, result)
    }

    pub(super) fn check_binary_enum_postfix(
        &mut self,
        expr: &Expr,
        source: &Expr,
        failure: Option<&Expr>,
        ctx: &Ctx,
        source_ty: Ty,
        result: Ty,
    ) -> Ty {
        if failure.is_none() && !ctx.has_return_boundary {
            self.invalid_binary_enum_postfix(
                expr.id,
                false,
                "there is no enclosing function return boundary",
            );
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
        let return_ty = self.store.shallow(&ctx.ret);
        let return_is_open = matches!(return_ty, Ty::Var(_) | Ty::Error);
        let return_symbol = failure
            .is_none()
            .then(|| nominal_symbol(return_ty))
            .flatten();
        let recovery_ret = if failure.is_none()
            && let Some(source_symbol) = source_symbol
            && return_symbol.is_none()
            && !return_is_open
        {
            let source = self.store.render(&source_ty);
            let ret = self.store.render(&ctx.ret);
            let required = self.store.render(&Ty::Nominal(source_symbol, vec![]));
            self.invalid_binary_enum_postfix(
                expr.id,
                false,
                format!(
                    "the operand has type {source}, but the enclosing function or block returns {ret}; '?' requires that boundary to return {required}"
                ),
            );
            Some(source_ty.clone())
        } else {
            None
        };
        let enum_symbol = match (source_symbol, return_symbol) {
            (Some(source), Some(ret)) if source != ret => {
                let source = self.store.render(&source_ty);
                let ret = self.store.render(&ctx.ret);
                self.invalid_binary_enum_postfix(
                    expr.id,
                    false,
                    format!(
                        "the operand and enclosing return type use different enums ({source} and {ret})"
                    ),
                );
                return Ty::Error;
            }
            (Some(symbol), _) | (_, Some(symbol)) => symbol,
            _ => {
                let reason = if failure.is_some() {
                    "the operand must identify an enum"
                } else {
                    "the operand or enclosing return type must identify an enum"
                };
                self.invalid_binary_enum_postfix(expr.id, failure.is_some(), reason);
                return Ty::Error;
            }
        };
        let Some(info) = self.catalog.enums.get(&enum_symbol).cloned() else {
            unreachable!("the selected postfix operand was checked as an enum")
        };
        if info.variants.len() != 2 {
            let operation = if failure.is_some() {
                "force unwrap"
            } else {
                "propagation"
            };
            let enum_name = self.store.render(&Ty::Nominal(enum_symbol, vec![]));
            self.invalid_binary_enum_postfix(
                expr.id,
                failure.is_some(),
                format!(
                    "{enum_name} has {} variants; {operation} requires exactly two",
                    info.variants.len()
                ),
            );
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
        let second_action = failure.map_or(BinaryEnumArm::Return, BinaryEnumArm::Failure);
        let arms = vec![
            self.propagation_arm(
                source,
                enum_symbol,
                &enum_name,
                first_name,
                first,
                BinaryEnumArm::Value,
            ),
            self.propagation_arm(
                source,
                enum_symbol,
                &enum_name,
                second_name,
                second,
                second_action,
            ),
        ];
        let lowered_id = self.artifacts.synthetic_id(source.id);
        let recovery_ctx = recovery_ret.map(|ret| ctx.with_ret_eff(ret, ctx.eff.clone()));
        let match_ctx = recovery_ctx.as_ref().unwrap_or(ctx);
        self.check_match_arms_against_known_scrutinee(
            source, source_ty, &arms, &result, None, match_ctx,
        );
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
            ExprKind::Unreachable => {
                unreachable!("unreachable expressions are desugared to the panic effect")
            }
            ExprKind::MacroCall { .. } | ExprKind::SyntaxQuote { .. } => Ty::Error,
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
            ExprKind::ForceUnwrap(source, failure) => {
                self.infer_force_unwrap(expr, source, failure, ctx)
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
                        // A func literal field gets its own scheme
                        // (rank-N field types): solved and generalized
                        // locally — declared generics and where
                        // clauses included — so sibling fields'
                        // predicates never fuse into this record's
                        // type. A bare reference to a polymorphic
                        // binding keeps the binding's scheme as the
                        // field's own — the desugared form of a
                        // func-literal field: no instantiation at the
                        // reference, each projection instantiates.
                        let ty = match &field.value.kind {
                            ExprKind::Func(func) => {
                                self.generalize_field_func(func, &field.value, ctx)
                            }
                            ExprKind::Variable(Name::Resolved(symbol, _))
                                if self.schemes.get(symbol).is_some_and(|scheme| {
                                    !scheme.is_monomorphic() || !scheme.predicates.is_empty()
                                }) =>
                            {
                                // The reference materializes the stored
                                // closure: its instantiation is
                                // recorded for lowering, and its
                                // obligations float straight to the
                                // final solve (the field's own scheme
                                // discharges the real uses; the
                                // materialization's are improvement's
                                // business). The field's type — and
                                // the reference node's baked type,
                                // lowering's marker for a rank-N
                                // materialization — is the binding's
                                // own scheme, so each projection
                                // instantiates per use (the desugared
                                // form of a func-literal field).
                                let materialization_start = self.wanteds.len();
                                self.infer_expr(&field.value, ctx);
                                self.deferred
                                    .extend(self.wanteds.split_off(materialization_start));
                                let ty = Ty::Forall(Box::new(self.schemes[symbol].clone()));
                                self.artifacts.node_types.insert(field.value.id, ty.clone());
                                ty
                            }
                            _ => self.infer_expr(&field.value, ctx),
                        };
                        (Label::Named(field.label.name_str()), ty)
                    })
                    .collect();
                Ty::Record(Row::closed(fields))
            }

            ExprKind::Variable(name) => {
                let ty = self.lookup(name, expr.id);
                if matches!(name.symbol(), Ok(Symbol::Variant(_))) {
                    self.diagnostics.errors.push((
                        TypeError::BareVariantReference {
                            variant: name.name_str(),
                        },
                        expr.id,
                    ));
                }
                ty
            }

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
                // Member callees record their written labels so static and
                // instance overload sets can select (ADR 0041).
                if let ExprKind::Member(..) = &callee.kind {
                    self.artifacts.member_call_slots.insert(
                        callee.id,
                        args.iter()
                            .map(crate::types::callables::WrittenSlot::of)
                            .collect(),
                    );
                }
                if let ExprKind::Constructor(..) = &callee.kind {
                    return self.infer_construction(expr, callee, type_args, args, ctx);
                }
                // `T(args)` for a rigid type parameter: construction
                // through a bound's init requirement (never an ordinary
                // call — a type parameter names no value).
                if let ExprKind::Variable(name) = &callee.kind
                    && let Ok(symbol) = name.symbol()
                    && matches!(symbol, Symbol::TypeParameter(_))
                {
                    return self
                        .infer_param_construction(expr, callee, symbol, type_args, args, ctx);
                }
                if let ExprKind::Member(Some(receiver), label, _) = &callee.kind
                    && let ExprKind::Constructor(name, _) = &receiver.kind
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
                if let ExprKind::Member(Some(receiver), label, _) = &callee.kind
                    && !matches!(receiver.kind, ExprKind::Constructor(..))
                {
                    if !type_args.is_empty() {
                        self.diagnostics.generic_argument_arity(
                            expr.id,
                            format!("Method '{label}'"),
                            0,
                            type_args.len(),
                        );
                    }
                    return self.infer_member_call(expr, callee, args, ctx);
                }
                // A leading-dot call gets its implicit type receiver from
                // the call result. Ordinary call inference owns arguments,
                // effects, and ownership markers; type-member lookup later
                // chooses an enum constructor or static function.
                if let ExprKind::Member(None, label, _) = &callee.kind {
                    let payload: Vec<(Label, Ty)> = args
                        .iter()
                        .map(|arg| (arg.label.clone(), self.infer_expr(&arg.value, ctx)))
                        .collect();
                    let result = Ty::Var(self.store.fresh_ty(self.level, expr.id));
                    let ctor = Ty::Var(self.store.fresh_ty(self.level, callee.id));
                    self.artifacts.node_types.insert(callee.id, ctor.clone());
                    for (index, (arg, (_, arg_ty))) in args.iter().zip(&payload).enumerate() {
                        self.note_indexed_marker(arg, &ctor, index, args.len(), arg_ty);
                    }
                    self.wanteds.push(Constraint::HasTypeMember {
                        receiver: result.clone(),
                        label: label.clone(),
                        payload,
                        ctor: Some(ctor),
                        allowed_effects: Some(ctx.eff.clone()),
                        member_node: callee.id,
                        origin: CtOrigin::new(expr.id, CtReason::Apply),
                    });
                    if !type_args.is_empty() {
                        self.apply_type_args(
                            callee.id,
                            format!("Type member '{label}'"),
                            type_args,
                        );
                    }
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
                let target = match &callee.kind {
                    ExprKind::Variable(name) => format!("Function '{}'", name.name_str()),
                    ExprKind::Constructor(name, _) => format!("Type '{}'", name.name_str()),
                    ExprKind::Member(_, label, _) => format!("Variant '{label}'"),
                    _ => "Function value".to_string(),
                };
                if !type_args.is_empty() {
                    self.apply_type_args(callee.id, target.clone(), type_args);
                }
                self.finish_call(expr.id, target, callee_ty, args, ctx)
            }

            ExprKind::Func(func) => self.infer_func(func, ctx),

            ExprKind::As(inner, annotation) => {
                let ty = self.lower_annotation(annotation);
                self.check_expr(inner, &ty, CtReason::Annotation, ctx);
                ty
            }

            ExprKind::Member(Some(receiver), label, _) => {
                if let ExprKind::Constructor(name, head_args) = &receiver.kind {
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
                        head_args,
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
            // A bare leading dot is both the contextual type receiver and
            // the selected member value. Payload-less enum cases satisfy
            // that equality; static properties can join this path later.
            ExprKind::Member(None, label, _) => {
                let result = Ty::Var(self.store.fresh_ty(self.level, expr.id));
                self.wanteds.push(Constraint::HasTypeMember {
                    receiver: result.clone(),
                    label: label.clone(),
                    payload: vec![],
                    ctor: None,
                    allowed_effects: None,
                    member_node: expr.id,
                    origin: CtOrigin::new(expr.id, CtReason::Apply),
                });
                result
            }

            ExprKind::Constructor(..) => {
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
                // Discharge happens at the handler's extent — a `#handle`
                // widening the ambient row for the rest of its block — not
                // at the perform site; closed effect annotations are
                // checked after the group solve.
                let Ok(symbol) = effect_name.symbol() else {
                    return Ty::Error;
                };
                if symbol == Symbol::Unsafe {
                    self.unsupported(
                        expr.id,
                        "the intrinsic `'unsafe` effect cannot be performed; use `#unsafe { ... }`",
                    );
                    return Ty::Error;
                }
                let Some(sig) = self.catalog.effects.get(&symbol).cloned() else {
                    self.unsupported(expr.id, "calling an undeclared effect");
                    return Ty::Error;
                };
                // Publish this perform's checked contract (ADR 0038):
                // declared parameter types and the type-generic
                // witness-block layout, consumed by lowering off the
                // typed tree.
                self.artifacts.effect_contracts.insert(
                    expr.id,
                    crate::types::output::EffectContract {
                        params: sig.params.clone(),
                        type_generics: sig
                            .generics
                            .iter()
                            .filter(|param| matches!(param.kind, crate::types::ty::ParamKind::Type))
                            .map(|param| param.symbol)
                            .collect(),
                    },
                );
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
                    self.diagnostics.generic_argument_arity(
                        expr.id,
                        format!("Effect '{symbol}'"),
                        sig.generics.len(),
                        type_args.len(),
                    );
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
                        self.check_mut_arg_is_place(arg);
                        self.check_expr(&arg.value, &instantiate(param), CtReason::Apply, ctx);
                    }
                } else {
                    self.diagnostics.argument_arity(
                        expr.id,
                        format!("Effect '{symbol}'"),
                        sig.params.len(),
                        args.len(),
                    );
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
                // The instruction takes whatever type its context demands
                // (a fresh variable solved by the surrounding annotation or
                // return type). Its operands are ordinary value expressions
                // and must be typed; the operation itself is validated here
                // and published as a checked op (ADR 0038) — lowering never
                // interprets the parser instruction.
                for operand in &instruction.binds {
                    self.infer_expr(operand, ctx);
                }
                if let Some(checked) = self.check_inline_ir(expr.id, instruction) {
                    self.artifacts.checked_ir.insert(expr.id, checked);
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

    // ----- Inline IR (ADR 0038) -----------------------------------------

    /// Validate one inline-IR instruction and produce its checked,
    /// target-neutral operation: canonical operation identity, checked
    /// types, validated operands. Every judgment lowering used to make —
    /// scalar/operation combinations, comparison operators, operand and
    /// register forms, annotation shapes — is made once, here.
    fn check_inline_ir(
        &mut self,
        node: NodeID,
        instruction: &crate::node_kinds::inline_ir_instruction::InlineIRInstruction,
    ) -> Option<crate::types::output::CheckedIrKind> {
        use crate::node_kinds::inline_ir_instruction::InlineIRInstructionKind as K;
        use crate::types::output::{CheckedIrKind as C, IrCmp, IrScalarOp as Op};

        Some(match &instruction.kind {
            K::Add { ty, a, b, .. } => {
                let op = if self.ir_annotation_symbol(ty) == Some(Symbol::RawPtr) {
                    Op::PtrAdd
                } else {
                    self.ir_arith(node, ty, Op::IntAdd, Op::FloatAdd)?
                };
                C::Scalar {
                    op,
                    a: self.ir_operand(node, instruction, a)?,
                    b: Some(self.ir_operand(node, instruction, b)?),
                }
            }
            K::Sub { ty, a, b, .. } => C::Scalar {
                op: self.ir_arith(node, ty, Op::IntSub, Op::FloatSub)?,
                a: self.ir_operand(node, instruction, a)?,
                b: Some(self.ir_operand(node, instruction, b)?),
            },
            K::Mul { ty, a, b, .. } => C::Scalar {
                op: self.ir_arith(node, ty, Op::IntMul, Op::FloatMul)?,
                a: self.ir_operand(node, instruction, a)?,
                b: Some(self.ir_operand(node, instruction, b)?),
            },
            K::Div { ty, a, b, .. } => C::Scalar {
                op: self.ir_arith(node, ty, Op::IntDiv, Op::FloatDiv)?,
                a: self.ir_operand(node, instruction, a)?,
                b: Some(self.ir_operand(node, instruction, b)?),
            },
            K::And { ty, a, b, .. } => C::Scalar {
                op: self.ir_bit(node, ty, Op::IntAnd, Op::ByteAnd)?,
                a: self.ir_operand(node, instruction, a)?,
                b: Some(self.ir_operand(node, instruction, b)?),
            },
            K::Or { ty, a, b, .. } => C::Scalar {
                op: self.ir_bit(node, ty, Op::IntOr, Op::ByteOr)?,
                a: self.ir_operand(node, instruction, a)?,
                b: Some(self.ir_operand(node, instruction, b)?),
            },
            K::Xor { ty, a, b, .. } => C::Scalar {
                op: self.ir_bit(node, ty, Op::IntXor, Op::ByteXor)?,
                a: self.ir_operand(node, instruction, a)?,
                b: Some(self.ir_operand(node, instruction, b)?),
            },
            K::Shl { ty, a, b, .. } => C::Scalar {
                op: self.ir_bit(node, ty, Op::IntShl, Op::ByteShl)?,
                a: self.ir_operand(node, instruction, a)?,
                b: Some(self.ir_operand(node, instruction, b)?),
            },
            K::Shr { ty, a, b, .. } => C::Scalar {
                op: self.ir_bit(node, ty, Op::IntShr, Op::ByteShr)?,
                a: self.ir_operand(node, instruction, a)?,
                b: Some(self.ir_operand(node, instruction, b)?),
            },
            K::Not { ty, a, .. } => C::Scalar {
                op: self.ir_bit(node, ty, Op::IntNot, Op::ByteNot)?,
                a: self.ir_operand(node, instruction, a)?,
                b: None,
            },
            K::Cmp {
                ty, lhs, rhs, op, ..
            } => {
                let kind = match op {
                    TokenKind::EqualsEquals => IrCmp::Eq,
                    TokenKind::BangEquals => IrCmp::Ne,
                    TokenKind::Less => IrCmp::Lt,
                    TokenKind::LessEquals => IrCmp::Le,
                    TokenKind::Greater => IrCmp::Gt,
                    TokenKind::GreaterEquals => IrCmp::Ge,
                    _ => {
                        self.unsupported(node, "this comparison operator in inline IR");
                        return None;
                    }
                };
                let op = match self.ir_annotation_symbol(ty) {
                    Some(Symbol::Int) => Op::IntCmp(kind),
                    Some(Symbol::Float) => Op::FloatCmp(kind),
                    Some(Symbol::Byte) => Op::ByteCmp(kind),
                    Some(Symbol::Bool) if matches!(kind, IrCmp::Eq | IrCmp::Ne) => {
                        Op::BoolCmp(kind)
                    }
                    Some(Symbol::RawPtr) if matches!(kind, IrCmp::Eq | IrCmp::Ne) => {
                        Op::PtrCmp(kind)
                    }
                    _ => {
                        self.unsupported(
                            node,
                            &format!(
                                "inline IR comparisons on `{}`",
                                Self::ir_annotation_name(ty)
                            ),
                        );
                        return None;
                    }
                };
                C::Scalar {
                    op,
                    a: self.ir_operand(node, instruction, lhs)?,
                    b: Some(self.ir_operand(node, instruction, rhs)?),
                }
            }
            K::Trunc { val, .. } => C::Scalar {
                op: Op::FloatToIntTrunc,
                a: self.ir_operand(node, instruction, val)?,
                b: None,
            },
            K::IntToFloat { val, .. } => C::Scalar {
                op: Op::IntToFloat,
                a: self.ir_operand(node, instruction, val)?,
                b: None,
            },
            K::ByteToInt { val, .. } => C::Scalar {
                op: Op::ByteToInt,
                a: self.ir_operand(node, instruction, val)?,
                b: None,
            },
            K::IntToByte { val, .. } => C::Scalar {
                op: Op::IntToByte,
                a: self.ir_operand(node, instruction, val)?,
                b: None,
            },
            K::Alloc { ty, count, .. } => C::Alloc {
                elem: self.ir_annotation_ty(node, ty)?,
                count: self.ir_operand(node, instruction, count)?,
            },
            K::Free { ptr } => C::Free {
                ptr: self.ir_operand(node, instruction, ptr)?,
            },
            K::Retain { ty, value } => C::Retain {
                ty: self.ir_annotation_ty(node, ty)?,
                value: self.ir_operand(node, instruction, value)?,
            },
            K::IsUnique { ptr, .. } => C::IsUnique {
                ptr: self.ir_operand(node, instruction, ptr)?,
            },
            K::Load { ty, addr, .. } => C::Load {
                ty: self.ir_annotation_ty(node, ty)?,
                addr: self.ir_operand(node, instruction, addr)?,
            },
            K::Store { value, ty, addr } => C::Store {
                ty: self.ir_annotation_ty(node, ty)?,
                value: self.ir_operand(node, instruction, value)?,
                addr: self.ir_operand(node, instruction, addr)?,
            },
            K::Swap { ty, a, b } => C::Swap {
                ty: self.ir_annotation_ty(node, ty)?,
                a: self.ir_operand(node, instruction, a)?,
                b: self.ir_operand(node, instruction, b)?,
            },
            K::Take { ty, value, .. } => C::Take {
                ty: self.ir_annotation_ty(node, ty)?,
                value: self.ir_operand(node, instruction, value)?,
            },
            K::Copy {
                from, to, length, ..
            } => C::MemCopy {
                from: self.ir_operand(node, instruction, from)?,
                to: self.ir_operand(node, instruction, to)?,
                length: self.ir_operand(node, instruction, length)?,
            },
            K::InlineGet {
                ty, array, index, ..
            } => C::InlineGet {
                element: self.ir_annotation_ty(node, ty)?,
                array: self.ir_operand(node, instruction, array)?,
                index: self.ir_operand(node, instruction, index)?,
            },
            K::Gep {
                ty,
                addr,
                offset_index,
                ..
            } => C::Gep {
                elem: self.ir_annotation_ty(node, ty)?,
                addr: self.ir_operand(node, instruction, addr)?,
                offset: self.ir_operand(node, instruction, offset_index)?,
            },
            K::Io { op, a, b, c, .. } => {
                // The operation index selects a fixed host-table entry; it
                // is meaningless as a runtime value, so it must be spelled
                // as an integer literal in the IR text.
                let crate::node_kinds::inline_ir_instruction::Value::Int(op) = op else {
                    self.unsupported(node, "inline IR io with a non-literal operation index");
                    return None;
                };
                let Ok(op) = u8::try_from(*op) else {
                    self.unsupported(node, "inline IR io operation index out of range");
                    return None;
                };
                C::Io {
                    op,
                    a: self.ir_operand(node, instruction, a)?,
                    b: self.ir_operand(node, instruction, b)?,
                    c: self.ir_operand(node, instruction, c)?,
                }
            }
        })
    }

    fn ir_arith(
        &mut self,
        node: NodeID,
        annotation: &crate::node_kinds::type_annotation::TypeAnnotation,
        int: crate::types::output::IrScalarOp,
        float: crate::types::output::IrScalarOp,
    ) -> Option<crate::types::output::IrScalarOp> {
        match self.ir_annotation_symbol(annotation) {
            Some(Symbol::Int) => Some(int),
            Some(Symbol::Float) => Some(float),
            _ => {
                self.unsupported(
                    node,
                    &format!(
                        "inline IR arithmetic on `{}`",
                        Self::ir_annotation_name(annotation)
                    ),
                );
                None
            }
        }
    }

    fn ir_bit(
        &mut self,
        node: NodeID,
        annotation: &crate::node_kinds::type_annotation::TypeAnnotation,
        int: crate::types::output::IrScalarOp,
        byte: crate::types::output::IrScalarOp,
    ) -> Option<crate::types::output::IrScalarOp> {
        match self.ir_annotation_symbol(annotation) {
            Some(Symbol::Int) => Some(int),
            Some(Symbol::Byte) => Some(byte),
            _ => {
                self.unsupported(
                    node,
                    &format!(
                        "inline IR bitwise operations on `{}`",
                        Self::ir_annotation_name(annotation)
                    ),
                );
                None
            }
        }
    }

    /// The resolved head symbol of a bare nominal IR annotation.
    fn ir_annotation_symbol(
        &self,
        annotation: &crate::node_kinds::type_annotation::TypeAnnotation,
    ) -> Option<Symbol> {
        use crate::node_kinds::type_annotation::TypeAnnotationKind;
        match &annotation.kind {
            TypeAnnotationKind::Nominal {
                name: Name::Resolved(symbol, _),
                ..
            } => Some(*symbol),
            _ => None,
        }
    }

    /// The annotation's source spelling, for diagnostics.
    fn ir_annotation_name(
        annotation: &crate::node_kinds::type_annotation::TypeAnnotation,
    ) -> String {
        use crate::node_kinds::type_annotation::TypeAnnotationKind;
        match &annotation.kind {
            TypeAnnotationKind::Nominal { name, .. } => name.name_str(),
            _ => "this annotation".to_string(),
        }
    }

    /// A memory/value type annotation on an IR operation: a nominal head
    /// or a borrow of one (the shapes lowering supports), lowered to its
    /// checked type. Generic heads substitute per instance during
    /// backend specialization.
    fn ir_annotation_ty(
        &mut self,
        node: NodeID,
        annotation: &crate::node_kinds::type_annotation::TypeAnnotation,
    ) -> Option<Ty> {
        use crate::node_kinds::type_annotation::TypeAnnotationKind;
        match &annotation.kind {
            TypeAnnotationKind::Nominal { .. } => Some(self.lower_annotation(annotation)),
            TypeAnnotationKind::Borrow { inner, .. } => self.ir_annotation_ty(node, inner),
            _ => {
                self.unsupported(node, "this inline IR type annotation");
                None
            }
        }
    }

    /// A validated IR operand: `%N` (parameter), `$N` (bound
    /// sub-expression, index-checked), or an immediate.
    fn ir_operand(
        &mut self,
        node: NodeID,
        instruction: &crate::node_kinds::inline_ir_instruction::InlineIRInstruction,
        value: &crate::node_kinds::inline_ir_instruction::Value,
    ) -> Option<crate::types::output::IrOperand> {
        use crate::node_kinds::inline_ir_instruction::Value;
        use crate::types::output::IrOperand;
        match value {
            Value::Reg(index) => match u16::try_from(*index) {
                Ok(index) => Some(IrOperand::Reg(index)),
                Err(_) => {
                    self.unsupported(node, "an inline IR register out of range");
                    None
                }
            },
            Value::Bind(index) => {
                if *index < instruction.binds.len()
                    && let Ok(index) = u16::try_from(*index)
                {
                    Some(IrOperand::Bind(index))
                } else {
                    self.unsupported(node, "an inline IR bind out of range");
                    None
                }
            }
            Value::Int(value) => Some(IrOperand::Int(*value)),
            Value::Float(value) => Some(IrOperand::Float(*value)),
            Value::Bool(value) => Some(IrOperand::Bool(*value)),
            Value::Void => Some(IrOperand::Void),
            _ => {
                self.unsupported(node, "this inline IR operand");
                None
            }
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
