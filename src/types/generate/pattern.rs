use super::*;

impl PatternRefinement {
    pub(super) fn is_empty(&self) -> bool {
        self.givens.is_empty() && self.local_params.is_empty()
    }

    pub(super) fn extend(&mut self, other: PatternRefinement) {
        for given in other.givens {
            if !self.givens.contains(&given) {
                self.givens.push(given);
            }
        }
        for param in other.local_params {
            if !self.local_params.contains(&param) {
                self.local_params.push(param);
            }
        }
    }

    pub(super) fn equivalent_to(&self, other: &Self) -> bool {
        if self.givens.len() != other.givens.len()
            || self.local_params.len() != other.local_params.len()
        {
            return false;
        }
        self.givens.iter().zip(&other.givens).all(|(left, right)| {
            Self::predicate_equivalent(left, right, &self.local_params, &other.local_params)
        })
    }

    pub(super) fn types_equivalent_to(&self, other: &Self, left: &Ty, right: &Ty) -> bool {
        self.local_params.len() == other.local_params.len()
            && Self::ty_equivalent(left, right, &self.local_params, &other.local_params)
    }

    pub(super) fn substitute_constraint_from(
        &self,
        source: &Self,
        constraint: Constraint,
    ) -> Constraint {
        let tys: FxHashMap<Symbol, Ty> = source
            .local_params
            .iter()
            .copied()
            .zip(self.local_params.iter().copied().map(Ty::Param))
            .collect();
        let effs = FxHashMap::default();
        let rows = FxHashMap::default();
        match constraint {
            Constraint::Eq(a, b, origin) => Constraint::Eq(
                a.substitute(&tys, &effs, &rows),
                b.substitute(&tys, &effs, &rows),
                origin,
            ),
            Constraint::EffEq(a, b, origin) => Constraint::EffEq(a, b, origin),
            Constraint::Conforms {
                ty,
                protocol,
                origin,
            } => Constraint::Conforms {
                ty: ty.substitute(&tys, &effs, &rows),
                protocol,
                origin,
            },
            Constraint::HasMember {
                receiver,
                label,
                member,
                origin,
            } => Constraint::HasMember {
                receiver: receiver.substitute(&tys, &effs, &rows),
                label,
                member: member.substitute(&tys, &effs, &rows),
                origin,
            },
            Constraint::Implic(implication) => Constraint::Implic(implication),
        }
    }

    pub(super) fn predicate_equivalent(
        left: &Predicate,
        right: &Predicate,
        left_params: &[Symbol],
        right_params: &[Symbol],
    ) -> bool {
        match (left, right) {
            (Predicate::TypeEq(a, b), Predicate::TypeEq(c, d)) => {
                Self::ty_equivalent(a, c, left_params, right_params)
                    && Self::ty_equivalent(b, d, left_params, right_params)
            }
            (Predicate::EffectEq(a, b), Predicate::EffectEq(c, d)) => {
                Self::effect_equivalent(a, c, left_params, right_params)
                    && Self::effect_equivalent(b, d, left_params, right_params)
            }
            (Predicate::RowEq(a, b), Predicate::RowEq(c, d)) => {
                Self::row_equivalent(a, c, left_params, right_params)
                    && Self::row_equivalent(b, d, left_params, right_params)
            }
            (
                Predicate::Conforms { ty, protocol },
                Predicate::Conforms {
                    ty: other_ty,
                    protocol: other_protocol,
                },
            ) => {
                protocol == other_protocol
                    && Self::ty_equivalent(ty, other_ty, left_params, right_params)
            }
            (
                Predicate::HasMember {
                    receiver,
                    label,
                    member,
                },
                Predicate::HasMember {
                    receiver: other_receiver,
                    label: other_label,
                    member: other_member,
                },
            ) => {
                label == other_label
                    && Self::ty_equivalent(receiver, other_receiver, left_params, right_params)
                    && Self::ty_equivalent(member, other_member, left_params, right_params)
            }
            _ => false,
        }
    }

    pub(super) fn ty_equivalent(
        left: &Ty,
        right: &Ty,
        left_params: &[Symbol],
        right_params: &[Symbol],
    ) -> bool {
        left.try_zip(right, &mut |left, right| match (left, right) {
            (Ty::Param(left), Ty::Param(right)) => {
                Self::symbol_equivalent(*left, *right, left_params, right_params)
            }
            (Ty::Var(left), Ty::Var(right)) => left == right,
            (Ty::Nominal(left_symbol, _), Ty::Nominal(right_symbol, _)) => {
                left_symbol == right_symbol
            }
            (Ty::Func(_, _, left_eff), Ty::Func(_, _, right_eff)) => {
                Self::effect_equivalent(left_eff, right_eff, left_params, right_params)
            }
            (Ty::Record(left), Ty::Record(right)) => {
                Self::row_tail_equivalent(&left.tail, &right.tail, left_params, right_params)
            }
            (
                Ty::Any {
                    protocol: left_protocol,
                    ..
                },
                Ty::Any {
                    protocol: right_protocol,
                    ..
                },
            ) => left_protocol == right_protocol,
            (Ty::Proj(_, left_protocol, left_assoc), Ty::Proj(_, right_protocol, right_assoc)) => {
                left_protocol == right_protocol && left_assoc == right_assoc
            }
            (Ty::Tuple(_), Ty::Tuple(_)) | (Ty::Error, Ty::Error) => true,
            _ => true,
        })
    }

    pub(super) fn effect_equivalent(
        left: &EffectRow,
        right: &EffectRow,
        left_params: &[Symbol],
        right_params: &[Symbol],
    ) -> bool {
        left.effects == right.effects
            && match (&left.tail, &right.tail) {
                (None, None) => true,
                (Some(EffTail::Var(left)), Some(EffTail::Var(right))) => left == right,
                (Some(EffTail::Param(left)), Some(EffTail::Param(right))) => {
                    Self::symbol_equivalent(*left, *right, left_params, right_params)
                }
                _ => false,
            }
    }

    pub(super) fn row_equivalent(
        left: &Row,
        right: &Row,
        left_params: &[Symbol],
        right_params: &[Symbol],
    ) -> bool {
        Self::row_tail_equivalent(&left.tail, &right.tail, left_params, right_params)
            && left.try_zip(right, &mut |left, right| {
                Self::ty_equivalent(left, right, left_params, right_params)
            })
    }

    pub(super) fn row_tail_equivalent(
        left: &Option<RowTail>,
        right: &Option<RowTail>,
        left_params: &[Symbol],
        right_params: &[Symbol],
    ) -> bool {
        match (left, right) {
            (None, None) => true,
            (Some(RowTail::Var(left)), Some(RowTail::Var(right))) => left == right,
            (Some(RowTail::Param(left)), Some(RowTail::Param(right))) => {
                Self::symbol_equivalent(*left, *right, left_params, right_params)
            }
            _ => false,
        }
    }

    pub(super) fn symbol_equivalent(
        left: Symbol,
        right: Symbol,
        left_params: &[Symbol],
        right_params: &[Symbol],
    ) -> bool {
        for (left_param, right_param) in left_params.iter().zip(right_params) {
            if *left_param == left || *right_param == right {
                return *left_param == left && *right_param == right;
            }
        }
        left == right
    }
}

impl<'s, 'a> BodyChecker<'s, 'a> {
    // ----- Patterns -----------------------------------------------------

    pub(super) fn check_pattern(&mut self, pattern: &Pattern, expected: &Ty) -> PatternRefinement {
        match &pattern.kind {
            PatternKind::Wildcard => PatternRefinement::default(),
            PatternKind::Bind(name) => {
                if let Ok(symbol) = name.symbol() {
                    // Or-pattern alternatives share their binder symbols
                    // (the resolver unifies them), so a re-bind must agree
                    // with the earlier alternative's type.
                    match self.mono.get(&symbol).cloned() {
                        Some(existing) => {
                            self.emit_eq(existing, expected.clone(), pattern.id, CtReason::Pattern);
                        }
                        None => {
                            self.mono.insert(symbol, expected.clone());
                        }
                    }
                }
                PatternRefinement::default()
            }
            PatternKind::LiteralInt(_) => {
                self.emit_eq(
                    expected.clone(),
                    Ty::Nominal(Symbol::Int, vec![]),
                    pattern.id,
                    CtReason::Pattern,
                );
                PatternRefinement::default()
            }
            PatternKind::LiteralFloat(_) => {
                self.emit_eq(
                    expected.clone(),
                    Ty::Nominal(Symbol::Float, vec![]),
                    pattern.id,
                    CtReason::Pattern,
                );
                PatternRefinement::default()
            }
            PatternKind::LiteralTrue | PatternKind::LiteralFalse => {
                self.emit_eq(
                    expected.clone(),
                    Ty::Nominal(Symbol::Bool, vec![]),
                    pattern.id,
                    CtReason::Pattern,
                );
                PatternRefinement::default()
            }
            PatternKind::Tuple(patterns) => {
                let items: Vec<Ty> = patterns
                    .iter()
                    .map(|p| Ty::Var(self.store.fresh_ty(self.level, p.id)))
                    .collect();
                self.emit_eq(
                    expected.clone(),
                    Ty::Tuple(items.clone()),
                    pattern.id,
                    CtReason::Pattern,
                );
                let mut refinement = PatternRefinement::default();
                for (sub, ty) in patterns.iter().zip(&items) {
                    refinement.extend(self.check_pattern(sub, ty));
                }
                refinement
            }
            PatternKind::Or(patterns) => {
                let base_mono = self.mono.clone();
                let mut alternatives = vec![];
                for sub in patterns {
                    *self.mono = base_mono.clone();
                    let wanted_start = self.wanteds.len();
                    let refinement = self.check_pattern(sub, expected);
                    let wanteds = self.wanteds.split_off(wanted_start);
                    let bindings: FxHashMap<Symbol, Ty> = self
                        .mono
                        .iter()
                        .filter_map(|(symbol, ty)| {
                            (base_mono.get(symbol) != Some(ty)).then_some((*symbol, ty.clone()))
                        })
                        .collect();
                    alternatives.push((refinement, bindings, wanteds));
                }
                *self.mono = base_mono;

                let Some((first, first_bindings, first_wanteds)) = alternatives.first() else {
                    return PatternRefinement::default();
                };
                self.wanteds.extend(first_wanteds.iter().cloned());
                let mut compatible = true;
                for (refinement, bindings, wanteds) in alternatives.iter().skip(1) {
                    let equivalent = first.equivalent_to(refinement);
                    if !equivalent {
                        compatible = false;
                    }
                    for (symbol, first_ty) in first_bindings {
                        if let Some(ty) = bindings.get(symbol)
                            && !first.types_equivalent_to(refinement, first_ty, ty)
                        {
                            self.emit_eq(
                                first_ty.clone(),
                                ty.clone(),
                                pattern.id,
                                CtReason::Pattern,
                            );
                        }
                    }
                    if equivalent {
                        self.wanteds.extend(
                            wanteds
                                .iter()
                                .cloned()
                                .map(|wanted| first.substitute_constraint_from(refinement, wanted)),
                        );
                    } else {
                        self.wanteds.extend(wanteds.iter().cloned());
                    }
                }
                if !compatible {
                    self.diagnostics
                        .errors
                        .push((TypeError::IncompatibleOrPatternRefinements, pattern.id));
                }
                for (symbol, ty) in first_bindings {
                    self.mono.insert(*symbol, ty.clone());
                }
                first.clone()
            }
            PatternKind::Variant {
                enum_name,
                variant_name,
                variant_name_span: _,
                fields,
            } => self.check_variant_pattern(pattern, enum_name, variant_name, fields, expected),
            PatternKind::Record { fields } => {
                let mut row_fields: Vec<(Label, Ty)> = vec![];
                let mut open = false;
                let mut refinement = PatternRefinement::default();
                for field in fields {
                    match &field.kind {
                        RecordFieldPatternKind::Bind(name) => {
                            let ty = Ty::Var(self.store.fresh_ty(self.level, field.id));
                            row_fields.push((Label::Named(name.name_str()), ty.clone()));
                            if let Ok(symbol) = name.symbol() {
                                self.mono.insert(symbol, ty);
                            }
                        }
                        RecordFieldPatternKind::Equals { name, value, .. } => {
                            let ty = Ty::Var(self.store.fresh_ty(self.level, field.id));
                            row_fields.push((Label::Named(name.name_str()), ty.clone()));
                            if let Ok(symbol) = name.symbol() {
                                self.mono.insert(symbol, ty.clone());
                            }
                            refinement.extend(self.check_pattern(value, &ty));
                        }
                        RecordFieldPatternKind::Rest => open = true,
                    }
                }
                let tail = if open {
                    Some(crate::types::ty::RowTail::Var(
                        self.store.fresh_row(self.level, pattern.id),
                    ))
                } else {
                    None
                };
                let mut row = Row::closed(row_fields);
                row.tail = tail;
                self.emit_eq(
                    expected.clone(),
                    Ty::Record(row),
                    pattern.id,
                    CtReason::Pattern,
                );
                refinement
            }
            PatternKind::Struct { .. } => {
                self.unsupported(pattern.id, "struct destructuring patterns");
                PatternRefinement::default()
            }
        }
    }

    /// Variant patterns (`.definitely(x)` / `Maybe.definitely(x)`): the enum
    /// comes from the explicit name or the scrutinee's head, and the
    /// constructor result is decomposed into arm-local givens as in Peyton
    /// Jones, Vytiniotis, Weirich, and Washburn's GADT typing rule.
    pub(super) fn check_variant_pattern(
        &mut self,
        pattern: &Pattern,
        enum_name: &Option<Name>,
        variant_name: &str,
        fields: &[Pattern],
        expected: &Ty,
    ) -> PatternRefinement {
        let shallow = self.store.shallow(expected);
        let enum_symbol = match enum_name {
            Some(name) => name.symbol().ok(),
            None => match &shallow {
                Ty::Nominal(symbol, _) if self.catalog.enums.contains_key(symbol) => Some(*symbol),
                _ => None,
            },
        };
        let Some(enum_symbol) = enum_symbol else {
            self.unsupported(
                pattern.id,
                "variant patterns on a scrutinee whose enum is not yet known (annotate the scrutinee)",
            );
            return PatternRefinement::default();
        };
        let Some(info) = self.catalog.enums.get(&enum_symbol).cloned() else {
            self.unsupported(pattern.id, "variant patterns on non-enum types");
            return PatternRefinement::default();
        };
        let Some(variant) = info.variants.get(variant_name) else {
            self.diagnostics.errors.push((
                TypeError::UnknownMember {
                    receiver: self.store.render(expected),
                    label: variant_name.to_string(),
                },
                pattern.id,
            ));
            return PatternRefinement::default();
        };
        // Record the resolution for tooling (go-to-definition on the
        // pattern's variant name).
        self.artifacts
            .member_resolutions
            .insert(pattern.id, MemberResolution::Direct(variant.symbol));

        // Bind the scrutinee to this enum, reusing its arguments when the
        // head is already concrete.
        let theta: Vec<Ty> = match &shallow {
            Ty::Nominal(symbol, args) if *symbol == enum_symbol => args.clone(),
            _ => {
                let theta: Vec<Ty> = info
                    .params
                    .iter()
                    .map(|_| Ty::Var(self.store.fresh_ty(self.level, pattern.id)))
                    .collect();
                self.emit_eq(
                    expected.clone(),
                    Ty::Nominal(enum_symbol, theta.clone()),
                    pattern.id,
                    CtReason::Pattern,
                );
                theta
            }
        };

        let substitution = param_subst(&info.params, &theta);
        let (instantiation, local_params) =
            self.instantiate_variant_pattern(variant, substitution, pattern.id);
        if fields.len() != instantiation.argument_types.len() {
            self.diagnostics.errors.push((
                TypeError::ArityMismatch {
                    expected: instantiation.argument_types.len(),
                    found: fields.len(),
                },
                pattern.id,
            ));
            return PatternRefinement::default();
        }
        let mut refinement = PatternRefinement {
            givens: instantiation.givens.clone(),
            local_params,
        };
        let scrutinee_result = Ty::Nominal(enum_symbol, theta);
        self.collect_refinement_type_equalities(
            scrutinee_result,
            instantiation.result_type.clone(),
            &mut refinement.givens,
        );
        for (sub, payload) in fields.iter().zip(&instantiation.argument_types) {
            refinement.extend(self.check_pattern(sub, payload));
        }
        refinement
    }

    pub(super) fn collect_refinement_type_equalities(
        &mut self,
        left: Ty,
        right: Ty,
        givens: &mut Vec<Predicate>,
    ) {
        let left = self.store.shallow(&left);
        let right = self.store.shallow(&right);
        match (left, right) {
            (Ty::Nominal(left_symbol, left_args), Ty::Nominal(right_symbol, right_args))
                if left_symbol == right_symbol && left_args.len() == right_args.len() =>
            {
                for (left, right) in left_args.into_iter().zip(right_args) {
                    self.collect_refinement_type_equalities(left, right, givens);
                }
            }
            (Ty::Tuple(left_items), Ty::Tuple(right_items))
                if left_items.len() == right_items.len() =>
            {
                for (left, right) in left_items.into_iter().zip(right_items) {
                    self.collect_refinement_type_equalities(left, right, givens);
                }
            }
            (left, right) if left == right => {}
            (left, right) => givens.push(Predicate::TypeEq(left, right)),
        }
    }
}
