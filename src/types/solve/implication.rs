use super::*;

impl<'s> Solver<'s> {
    /// Solve an OutsideIn(X) implication: givens are visible only while
    /// checking the implication's wanteds, and only touchable variables may
    /// be unified. Constructor-local GADT skolems are then checked for the
    /// non-escape condition from Peyton Jones et al. 2006.
    pub(super) fn solve_implication(&mut self, implication: Implication) -> Vec<Constraint> {
        let Implication {
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
        self.givens.extend(givens);
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
                NodeID::SYNTHESIZED,
            ));
        }

        let mut floatable = vec![];
        for residual in residuals {
            if let Some(param) = self.constraint_mentions_params(&residual, &local_params) {
                self.errors.push((
                    TypeError::EscapingExistential {
                        param: param.to_string(),
                    },
                    Self::constraint_origin(&residual)
                        .map_or(NodeID::SYNTHESIZED, |origin| origin.node),
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

    pub(super) fn constraint_origin(constraint: &Constraint) -> Option<CtOrigin> {
        match constraint {
            Constraint::Eq(_, _, origin)
            | Constraint::EffEq(_, _, origin)
            | Constraint::Conforms { origin, .. }
            | Constraint::HasMember { origin, .. }
            | Constraint::HasVariant { origin, .. }
            | Constraint::ApplyBorrow { origin, .. }
            | Constraint::PatternView { origin, .. }
            | Constraint::HandleEffect { origin, .. } => Some(*origin),
            Constraint::Implic(_) => None,
        }
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
            Constraint::HandleEffect { inner, outer, .. } => self
                .eff_mentions_params(inner, params)
                .or_else(|| self.eff_mentions_params(outer, params)),
            Constraint::Conforms { ty, .. } => self.ty_mentions_params(ty, params),
            Constraint::HasMember {
                receiver, member, ..
            } => self
                .ty_mentions_params(receiver, params)
                .or_else(|| self.ty_mentions_params(member, params)),
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
                        .find_map(|ty| self.ty_mentions_params(ty, params))
                })
                .or_else(|| {
                    ctor.as_ref()
                        .and_then(|ty| self.ty_mentions_params(ty, params))
                }),
            Constraint::ApplyBorrow {
                expected_inner,
                found,
                ..
            } => self
                .ty_mentions_params(expected_inner, params)
                .or_else(|| self.ty_mentions_params(found, params)),
            Constraint::PatternView {
                scrutinee, view, ..
            } => self
                .ty_mentions_params(scrutinee, params)
                .or_else(|| self.ty_mentions_params(view, params)),
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
        row.fields
            .iter()
            .find_map(|(_, ty)| self.ty_mentions_params(ty, params))
            .or_else(|| match &row.tail {
                Some(RowTail::Param(symbol)) if params.contains(symbol) => Some(*symbol),
                _ => None,
            })
    }

    pub(super) fn eff_mentions_params(&self, eff: &EffectRow, params: &[Symbol]) -> Option<Symbol> {
        match &eff.tail {
            Some(EffTail::Param(symbol)) if params.contains(symbol) => Some(*symbol),
            _ => None,
        }
    }
}
