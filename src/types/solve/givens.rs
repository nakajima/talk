use super::*;

impl<'s> Solver<'s> {
    pub(super) fn rewrite_ty_from_givens(&mut self, ty: Ty) -> Ty {
        self.rewrite_ty_from_givens_traced(ty).0
    }

    pub(super) fn rewrite_ty_from_givens_traced(&mut self, ty: Ty) -> (Ty, Option<Symbol>) {
        let mut seen = FxHashSet::default();
        self.rewrite_ty_from_givens_inner(ty, &mut seen)
    }

    /// Rewrite a type by the declaration's `where` given equalities, to a
    /// fixpoint, returning the rewritten type plus a trace of which local
    /// (constructor-skolem) param a rewrite leaned on — the escape check needs
    /// that trace.
    ///
    /// Deliberately NOT a `TyFold` (ADR 0005). Two of its obligations don't fit
    /// a structural fold:
    /// - it carries a per-call result (the `Option<Symbol>` trace), where a
    ///   fold yields only a rebuilt `Ty`; and
    /// - `seen` is forked **per child** (`rewrite_child` clones it) so two
    ///   sibling occurrences of the same type are each rewritten. A `TyFold`
    ///   threads one shared state across siblings, which would suppress the
    ///   second occurrence and under-rewrite. The forking is load-bearing, so
    ///   this walk keeps its own recursion.
    pub(super) fn rewrite_ty_from_givens_inner(
        &mut self,
        ty: Ty,
        seen: &mut FxHashSet<Ty>,
    ) -> (Ty, Option<Symbol>) {
        let ty = normalize_ty(self.store, self.catalog, &ty);
        if !seen.insert(ty.clone()) {
            return (ty, None);
        }
        let mut used_local_given = None;
        let rebuilt = match ty {
            Ty::Borrow(kind, inner) => Ty::Borrow(
                kind,
                Box::new(self.rewrite_child(*inner, seen, &mut used_local_given)),
            ),
            Ty::Nominal(symbol, args) => Ty::Nominal(
                symbol,
                args.into_iter()
                    .map(|arg| self.rewrite_child(arg, seen, &mut used_local_given))
                    .collect(),
            ),
            Ty::Tuple(items) => Ty::Tuple(
                items
                    .into_iter()
                    .map(|item| self.rewrite_child(item, seen, &mut used_local_given))
                    .collect(),
            ),
            Ty::Func(params, ret, eff) => Ty::Func(
                params
                    .into_iter()
                    .map(|param| self.rewrite_child(param, seen, &mut used_local_given))
                    .collect(),
                Box::new(self.rewrite_child(*ret, seen, &mut used_local_given)),
                eff,
            ),
            Ty::Record(row) => Ty::Record(Row {
                fields: row
                    .fields
                    .into_iter()
                    .map(|(label, field)| {
                        (
                            label,
                            self.rewrite_child(field, seen, &mut used_local_given),
                        )
                    })
                    .collect(),
                tail: row.tail,
            }),
            Ty::Any { protocol, assoc } => Ty::Any {
                protocol,
                assoc: assoc
                    .into_iter()
                    .map(|(symbol, ty)| {
                        (symbol, self.rewrite_child(ty, seen, &mut used_local_given))
                    })
                    .collect(),
            },
            Ty::Proj(base, protocol, assoc) => {
                let (base, used) = self.rewrite_ty_from_givens_inner(*base, seen);
                used_local_given = used_local_given.or(used);
                normalize_ty(
                    self.store,
                    self.catalog,
                    &Ty::Proj(Box::new(base), protocol, assoc),
                )
            }
            other => other,
        };

        let type_equalities: Vec<(Ty, Ty)> = self
            .givens
            .iter()
            .filter_map(|given| match given {
                Predicate::TypeEq(lhs, rhs) => Some((lhs.clone(), rhs.clone())),
                _ => None,
            })
            .collect();
        for (lhs, rhs) in type_equalities {
            let lhs = normalize_ty(self.store, self.catalog, &lhs);
            let rhs = normalize_ty(self.store, self.catalog, &rhs);
            if lhs == rhs {
                continue;
            }
            let local_given = self.given_mentions_local_params(&lhs, &rhs);
            let (from, to) = Self::oriented_given_rewrite(lhs, rhs);
            // A target containing its source (`Int ~ &Int`) grows the type
            // at every step and never reaches the fixpoint; rewrite such
            // givens in the shrinking direction instead.
            let (from, to) = if self.given_rewrite_occurs(&from, &to) {
                (to, from)
            } else {
                (from, to)
            };
            if rebuilt == from {
                let (rewritten, used) = self.rewrite_ty_from_givens_inner(to, seen);
                return (rewritten, used_local_given.or(local_given).or(used));
            }
        }
        (rebuilt, used_local_given)
    }

    /// Rewrite a child type with a forked `seen` set (so siblings don't share
    /// visited state), threading any local-given usage into `used`.
    pub(super) fn rewrite_child(
        &mut self,
        ty: Ty,
        seen: &FxHashSet<Ty>,
        used: &mut Option<Symbol>,
    ) -> Ty {
        let mut seen = seen.clone();
        let (ty, child_used) = self.rewrite_ty_from_givens_inner(ty, &mut seen);
        *used = (*used).or(child_used);
        ty
    }

    /// Whether `to` structurally contains `from` — the occurs check for an
    /// oriented given rewrite.
    fn given_rewrite_occurs(&mut self, from: &Ty, to: &Ty) -> bool {
        let needle = from.clone();
        self.store
            .query_resolved(to, &mut |_, node| match node {
                TyNode::Ty(ty) if *ty == needle => ControlFlow::Break(()),
                _ => ControlFlow::Continue(()),
            })
            .is_break()
    }

    pub(super) fn given_mentions_local_params(&mut self, lhs: &Ty, rhs: &Ty) -> Option<Symbol> {
        if self.local_params.is_empty() {
            return None;
        }
        let local_params = self.local_params.clone();
        self.ty_mentions_params(lhs, &local_params)
            .or_else(|| self.ty_mentions_params(rhs, &local_params))
    }

    pub(super) fn oriented_given_rewrite(lhs: Ty, rhs: Ty) -> (Ty, Ty) {
        if Self::rewrite_specificity(&lhs) <= Self::rewrite_specificity(&rhs) {
            (lhs, rhs)
        } else {
            (rhs, lhs)
        }
    }

    pub(super) fn rewrite_specificity(ty: &Ty) -> u8 {
        match ty {
            // A projection is a family application: it is always the redex
            // (OutsideIn(X)'s flattening direction), even against a bare
            // param — otherwise a self-referential given like `E.RHS ~ E`
            // rewrites E to E.RHS and diverges.
            Ty::Proj(..) => 0,
            Ty::Var(_) | Ty::Param(_) => 1,
            Ty::Func(..) | Ty::Record(_) | Ty::Tuple(_) => 2,
            Ty::Borrow(..) | Ty::Unique(_) | Ty::Nominal(..) | Ty::Any { .. } | Ty::Eff(_) => 3,
            Ty::Error => 4,
        }
    }

    pub(super) fn given_protocols_for(&mut self, ty: &Ty) -> Vec<ProtocolRef> {
        let ty = normalize_ty(self.store, self.catalog, ty);
        let ty = self.rewrite_ty_from_givens(ty);
        let conformances: Vec<(Ty, ProtocolRef)> = self
            .givens
            .iter()
            .filter_map(|given| match given {
                Predicate::Conforms { ty, protocol } => Some((ty.clone(), protocol.clone())),
                _ => None,
            })
            .collect();
        let mut protocols = vec![];
        for (given_ty, protocol) in conformances {
            let given_ty = normalize_ty(self.store, self.catalog, &given_ty);
            let given_ty = self.rewrite_ty_from_givens(given_ty);
            if given_ty == ty && !protocols.contains(&protocol) {
                protocols.push(protocol);
            }
        }
        protocols
    }

    pub(super) fn given_conformance_satisfies(&mut self, ty: &Ty, protocol: &ProtocolRef) -> bool {
        let conformances: Vec<(Ty, ProtocolRef)> = self
            .givens
            .iter()
            .filter_map(|given| match given {
                Predicate::Conforms { ty, protocol } => Some((ty.clone(), protocol.clone())),
                _ => None,
            })
            .collect();
        for (given_ty, given_protocol) in conformances {
            let given_ty = normalize_ty(self.store, self.catalog, &given_ty);
            let given_ty = self.rewrite_ty_from_givens(given_ty);
            if &given_ty == ty && self.catalog.bounds_satisfy(&[given_protocol], protocol) {
                return true;
            }
        }
        false
    }
}
