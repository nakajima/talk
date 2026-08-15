use super::*;

impl<'s> Solver<'s> {
    /// Solve an OutsideIn(X) implication: givens are visible only while
    /// checking the implication's wanteds, and only touchable variables may
    /// be unified. Constructor-local GADT skolems are then checked for the
    /// non-escape condition from Peyton Jones et al. 2006.
    pub(super) fn solve_implication(&mut self, implication: Implication) -> Vec<Constraint> {
        let Implication {
            node,
            level,
            givens,
            wanteds,
            local_params,
            touchable_level,
        } = implication;

        if givens.is_empty() && local_params.is_empty() && touchable_level.is_none() {
            return wanteds;
        }

        let original_given_len = self.givens.len();
        let original_level = self.level;
        let original_touchable_level = self.touchable_level;
        let original_local_param_len = self.local_params.len();
        self.givens.extend(givens.iter().cloned());
        self.local_params.extend(local_params.iter().copied());
        self.level = level;
        self.touchable_level = touchable_level;

        let residuals = self.solve(wanteds);

        self.givens.truncate(original_given_len);
        self.local_params.truncate(original_local_param_len);
        self.level = original_level;
        self.touchable_level = original_touchable_level;

        let escape_level = touchable_level.unwrap_or(level);
        if let Some(param) = self.escaping_outer_binding(&local_params, escape_level) {
            self.errors.push((
                TypeError::EscapingExistential {
                    param: param.to_string(),
                },
                node,
            ));
        }

        let mut floatable = vec![];
        for residual in residuals {
            // An equation pinning a constructor-local skolem to a type
            // that mentions it (`U ~ Expr<U>`) is no escape: it is
            // unsatisfiable on its face, so report the occurs failure
            // (Robinson 1965) rather than the escape.
            if let Some(ty) = self.occurs_violation(&residual, &local_params) {
                self.errors.push((
                    TypeError::InfiniteType { ty },
                    residual.origin().node,
                ));
                continue;
            }
            // A rigid value/equality obligation wholly inside the arm is a
            // failed local check, not an escape. Rewrite value adaptations
            // under the arm givens first: unlike Eq solving, Adapt can remain
            // parked on a projection before applying those refinements.
            let local_failure = match &residual {
                Constraint::Eq(expected, found, origin) => {
                    Some((expected.clone(), found.clone(), *origin))
                }
                Constraint::Adapt {
                    expected,
                    found,
                    origin,
                    ..
                } => Some((
                    self.rewrite_ty_with_local_givens(expected.clone(), &givens),
                    self.rewrite_ty_with_local_givens(found.clone(), &givens),
                    *origin,
                )),
                _ => None,
            };
            if let Some((expected, found, origin)) = local_failure
                && expected != found
                && self.ty_mentions_params(&expected, &local_params).is_some()
                && self.ty_mentions_params(&found, &local_params).is_some()
            {
                let expected =
                    self.diagnostic_ty_for_local_params(&expected, &local_params, &givens);
                let found = self.diagnostic_ty_for_local_params(&found, &local_params, &givens);
                self.report_mismatch(&expected, &found, origin);
                continue;
            }
            if let Some(param) = self.constraint_mentions_params(&residual, &local_params) {
                self.errors.push((
                    TypeError::EscapingExistential {
                        param: param.to_string(),
                    },
                    residual.origin().node,
                ));
                continue;
            }
            // Practical OutsideIn extension: after simplifying under local
            // givens, residuals that do not mention constructor-local
            // skolems can float outward. OutsideIn(X) Section 5.6.1 describes this
            // for simple implications; doing it here lets inferred GADT
            // matches discover branch result types without letting hidden
            // existentials escape.
            floatable.push(residual);
        }
        floatable
    }

    fn rewrite_ty_with_local_givens(&mut self, ty: Ty, givens: &[Predicate]) -> Ty {
        let original_given_len = self.givens.len();
        self.givens.extend(givens.iter().cloned());
        let rewritten = self.rewrite_ty_from_givens(ty);
        self.givens.truncate(original_given_len);
        rewritten
    }

    /// Replace an arm-local skolem with the outer type that the constructor
    /// result determines for it. This is diagnostic-only: solving remains
    /// rigid, while messages use the source-visible outer parameter instead
    /// of a synthesized `TypeParameter(...)` identifier.
    fn diagnostic_ty_for_local_params(
        &mut self,
        ty: &Ty,
        local_params: &[Symbol],
        givens: &[Predicate],
    ) -> Ty {
        let mut tys = FxHashMap::default();
        for given in givens {
            let Predicate::TypeEq(left, right) = given else {
                continue;
            };
            for (candidate, replacement) in [(left, right), (right, left)] {
                let Ty::Param(param) = candidate else {
                    continue;
                };
                if local_params.contains(param)
                    && self.ty_mentions_params(replacement, local_params).is_none()
                {
                    tys.entry(*param).or_insert_with(|| replacement.clone());
                }
            }
        }
        let effs = FxHashMap::default();
        let rows = FxHashMap::default();
        ty.substitute(&tys, &effs, &rows)
    }

    pub(super) fn escaping_outer_binding(
        &mut self,
        params: &[Symbol],
        level: Level,
    ) -> Option<Symbol> {
        if params.is_empty() {
            return None;
        }
        for index in 0..self.store.vars.len() {
            let root = self.store.find(index as u32);
            if root != index as u32 || self.store.vars[root as usize].level >= level {
                continue;
            }
            let Some(value) = self.store.vars[root as usize].value.clone() else {
                continue;
            };
            if let Some(param) = self.var_value_mentions_params(&value, params) {
                return Some(param);
            }
        }
        None
    }

    /// Whether an equality residual pins a constructor-local skolem to a
    /// type that mentions the same skolem — the occurs-check shape. Such
    /// an equation is unsatisfiable regardless of scope, so it deserves
    /// the infinite-type diagnostic, not the existential-escape one.
    /// Returns the rendered equation for the message.
    pub(super) fn occurs_violation(
        &mut self,
        constraint: &Constraint,
        params: &[Symbol],
    ) -> Option<String> {
        let Constraint::Eq(a, b, _) = constraint else {
            return None;
        };
        for (needle, haystack) in [(a, b), (b, a)] {
            let Ty::Param(param) = self.store.shallow(needle) else {
                continue;
            };
            if !params.contains(&param) {
                continue;
            }
            let haystack = self.store.shallow(haystack);
            // The identity equation `U ~ U` is no violation: only a
            // skolem occurring inside structure makes the type infinite.
            if matches!(haystack, Ty::Param(other) if other == param) {
                continue;
            }
            if self.ty_mentions_params(&haystack, &[param]).is_some() {
                let haystack = self.store.render(&haystack);
                let param = self.store.render(&Ty::Param(param));
                return Some(format!("{param} = {haystack}"));
            }
        }
        None
    }

    pub(super) fn constraint_mentions_params(
        &mut self,
        constraint: &Constraint,
        params: &[Symbol],
    ) -> Option<Symbol> {
        match constraint {
            Constraint::Eq(a, b, _) => self
                .ty_mentions_params(a, params)
                .or_else(|| self.ty_mentions_params(b, params)),
            Constraint::EffEq(a, b, _) => self
                .eff_mentions_params(a, params)
                .or_else(|| self.eff_mentions_params(b, params)),
            Constraint::EffectSubset {
                inferred, allowed, ..
            } => self
                .eff_mentions_params(inferred, params)
                .or_else(|| self.eff_mentions_params(allowed, params)),
            Constraint::PreferEq(a, b, _) => self
                .ty_mentions_params(a, params)
                .or_else(|| self.ty_mentions_params(b, params)),
            Constraint::HandleEffect { inner, outer, .. } => self
                .eff_mentions_params(inner, params)
                .or_else(|| self.eff_mentions_params(outer, params)),
            Constraint::Conforms { ty, .. } => self.ty_mentions_params(ty, params),
            Constraint::HasMember {
                receiver, member, ..
            } => self
                .ty_mentions_params(receiver, params)
                .or_else(|| self.ty_mentions_params(member, params)),
            Constraint::HasTypeMember {
                receiver,
                payload,
                ctor,
                allowed_effects,
                ..
            } => self
                .ty_mentions_params(receiver, params)
                .or_else(|| {
                    payload
                        .iter()
                        .find_map(|(_, ty)| self.ty_mentions_params(ty, params))
                })
                .or_else(|| {
                    ctor.as_ref()
                        .and_then(|ty| self.ty_mentions_params(ty, params))
                })
                .or_else(|| {
                    allowed_effects
                        .as_ref()
                        .and_then(|effects| self.eff_mentions_params(effects, params))
                }),
            Constraint::HasVariant {
                enum_ty,
                payload,
                ctor,
                ..
            } => self
                .ty_mentions_params(enum_ty, params)
                .or_else(|| {
                    payload
                        .iter()
                        .find_map(|(_, ty)| self.ty_mentions_params(ty, params))
                })
                .or_else(|| {
                    ctor.as_ref()
                        .and_then(|ty| self.ty_mentions_params(ty, params))
                }),
            Constraint::Adapt {
                expected, found, ..
            } => self
                .ty_mentions_params(expected, params)
                .or_else(|| self.ty_mentions_params(found, params)),
            Constraint::PatternView {
                scrutinee, view, ..
            } => self
                .ty_mentions_params(scrutinee, params)
                .or_else(|| self.ty_mentions_params(view, params)),
            Constraint::StringPattern { ty, .. } => self.ty_mentions_params(ty, params),
            Constraint::StaticCmp { lhs, rhs, .. } => self
                .ty_mentions_params(lhs, params)
                .or_else(|| self.ty_mentions_params(rhs, params)),
            Constraint::Implic(implication) => implication
                .givens
                .iter()
                .find_map(|predicate| self.predicate_mentions_params(predicate, params))
                .or_else(|| {
                    implication
                        .wanteds
                        .iter()
                        .find_map(|wanted| self.constraint_mentions_params(wanted, params))
                }),
        }
    }

    pub(super) fn var_value_mentions_params(
        &mut self,
        value: &VarValue,
        params: &[Symbol],
    ) -> Option<Symbol> {
        match value {
            VarValue::Ty(ty) => self.ty_mentions_params(ty, params),
            VarValue::Eff(eff) => self.eff_mentions_params(eff, params),
            VarValue::Row(row) => self.row_mentions_params(row, params),
            VarValue::Perm(perm) => match perm {
                Perm::Param(symbol) if params.contains(symbol) => Some(*symbol),
                _ => None,
            },
        }
    }

    pub(super) fn predicate_mentions_params(
        &mut self,
        predicate: &Predicate,
        params: &[Symbol],
    ) -> Option<Symbol> {
        match predicate {
            Predicate::TypeEq(a, b) => self
                .ty_mentions_params(a, params)
                .or_else(|| self.ty_mentions_params(b, params)),
            Predicate::EffectEq(a, b) => self
                .eff_mentions_params(a, params)
                .or_else(|| self.eff_mentions_params(b, params)),
            Predicate::RowEq(a, b) => self
                .row_mentions_params(a, params)
                .or_else(|| self.row_mentions_params(b, params)),
            Predicate::Conforms { ty, .. } => self.ty_mentions_params(ty, params),
            Predicate::HasMember {
                receiver, member, ..
            } => self
                .ty_mentions_params(receiver, params)
                .or_else(|| self.ty_mentions_params(member, params)),
            Predicate::StaticCmp { lhs, rhs, .. } => self
                .ty_mentions_params(lhs, params)
                .or_else(|| self.ty_mentions_params(rhs, params)),
        }
    }

    pub(super) fn ty_mentions_params(&mut self, ty: &Ty, params: &[Symbol]) -> Option<Symbol> {
        // Only rigid params and *rigid* tail params escape; a tail variable is
        // not yet a local param, so it does not count here.
        let found = self.store.query_resolved(ty, &mut |_, node| match node {
            TyNode::Ty(Ty::Param(symbol)) if params.contains(symbol) => ControlFlow::Break(*symbol),
            TyNode::RowTail(RowTail::Param(symbol)) | TyNode::EffTail(EffTail::Param(symbol))
                if params.contains(symbol) =>
            {
                ControlFlow::Break(*symbol)
            }
            _ => ControlFlow::Continue(()),
        });
        match found {
            ControlFlow::Break(symbol) => Some(symbol),
            ControlFlow::Continue(()) => None,
        }
    }

    pub(super) fn row_mentions_params(&mut self, row: &Row, params: &[Symbol]) -> Option<Symbol> {
        self.ty_mentions_params(&Ty::Record(row.clone()), params)
    }

    pub(super) fn eff_mentions_params(&self, eff: &EffectRow, params: &[Symbol]) -> Option<Symbol> {
        match &eff.tail {
            Some(EffTail::Param(symbol)) if params.contains(symbol) => Some(*symbol),
            _ => None,
        }
    }
}
