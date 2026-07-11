use super::*;

impl<'s> Solver<'s> {
    /// One step on a Conforms constraint: discharge against the conformance
    /// table (OutsideIn's class-constraint reaction; instance contexts will
    /// emit further wanteds when conditional conformance lands).
    pub(super) fn try_conforms(
        &mut self,
        ty: Ty,
        protocol: ProtocolRef,
        origin: CtOrigin,
        queue: &mut Vec<Constraint>,
    ) -> Option<Constraint> {
        let normalized = normalize_ty(self.store, self.catalog, &ty);
        let normalized = self.rewrite_ty_from_givens(normalized);
        let protocol = ProtocolRef {
            protocol: protocol.protocol,
            args: protocol
                .args
                .iter()
                .map(|arg| {
                    let arg = normalize_ty(self.store, self.catalog, arg);
                    let arg = self.rewrite_ty_from_givens(arg);
                    self.catalog.canonical_conformance_arg(arg)
                })
                .collect(),
        };
        if self.given_conformance_satisfies(&normalized, &protocol) {
            return None;
        }
        match normalized.clone() {
            Ty::Var(_) => Some(Constraint::Conforms {
                ty,
                protocol,
                origin,
            }),
            Ty::Error => None,
            Ty::Borrow(_, inner) => self.try_conforms((*inner).clone(), protocol, origin, queue),
            Ty::Any {
                protocol: existential_protocol,
                ..
            } => {
                let goal = ConformanceGoal {
                    ty: normalized,
                    protocol: protocol.clone(),
                };
                if self.try_conforms_via_bounds(
                    protocol.clone(),
                    origin,
                    &[existential_protocol],
                    queue,
                ) || self.try_conforms_via_protocol_head(&goal, origin, queue)
                {
                    None
                } else if protocol.has_unification_vars() {
                    Some(Constraint::Conforms {
                        ty,
                        protocol,
                        origin,
                    })
                } else {
                    self.not_conforming(&ty, protocol, origin)
                }
            }
            Ty::Param(param) => {
                let goal = ConformanceGoal {
                    ty: normalized,
                    protocol: protocol.clone(),
                };
                let bounds = self
                    .catalog
                    .param_bounds
                    .get(&param)
                    .cloned()
                    .unwrap_or_default();
                if self.try_conforms_via_bounds(protocol.clone(), origin, &bounds, queue)
                    || self.try_conforms_via_protocol_head(&goal, origin, queue)
                {
                    None
                } else if protocol.has_unification_vars() {
                    Some(Constraint::Conforms {
                        ty,
                        protocol,
                        origin,
                    })
                } else {
                    self.not_conforming(&ty, protocol, origin)
                }
            }
            // An irreducible projection conforms through the bounds declared
            // on the associated type (`associated T: Iterator`).
            Ty::Proj(base, _, assoc_symbol) => {
                if matches!(self.store.shallow(&base), Ty::Var(_)) {
                    return Some(Constraint::Conforms {
                        ty,
                        protocol,
                        origin,
                    });
                }
                let goal = ConformanceGoal {
                    ty: normalized,
                    protocol: protocol.clone(),
                };
                let bounds = self
                    .catalog
                    .param_bounds
                    .get(&assoc_symbol)
                    .cloned()
                    .unwrap_or_default();
                if self.try_conforms_via_bounds(protocol.clone(), origin, &bounds, queue)
                    || self.try_conforms_via_protocol_head(&goal, origin, queue)
                {
                    None
                } else if protocol.has_unification_vars() {
                    Some(Constraint::Conforms {
                        ty,
                        protocol,
                        origin,
                    })
                } else {
                    self.not_conforming(&ty, protocol, origin)
                }
            }
            Ty::Nominal(symbol, args) => {
                if protocol.has_unification_vars() {
                    return Some(Constraint::Conforms {
                        ty,
                        protocol,
                        origin,
                    });
                }
                if protocol.args.is_empty()
                    && protocol.protocol == Symbol::Copy
                    && self.catalog.grade_of(symbol) == crate::types::catalog::Grade::Copy
                {
                    return None;
                }
                let matches = self.catalog.matching_conformances(symbol, &args, &protocol);
                match matches.as_slice() {
                    [matched] => {
                        let goal = ConformanceGoal {
                            ty: normalized,
                            protocol: protocol.clone(),
                        };
                        let context = matched.conformance.context.clone();
                        let substitution = matched.substitution.clone();
                        self.apply_conformance_context(
                            &goal,
                            &context,
                            &substitution,
                            origin,
                            queue,
                        );
                        None
                    }
                    [] => {
                        if self.try_derive(symbol, &args, &protocol, origin, queue) {
                            return None;
                        }
                        self.not_conforming(&ty, protocol, origin)
                    }
                    many => {
                        self.report_overlapping_conformance(
                            &normalized,
                            &protocol,
                            many[0].protocol,
                            origin,
                        );
                        None
                    }
                }
            }
            other => self.not_conforming(&other, protocol, origin),
        }
    }

    fn try_conforms_via_protocol_head(
        &mut self,
        goal: &ConformanceGoal,
        origin: CtOrigin,
        queue: &mut Vec<Constraint>,
    ) -> bool {
        if goal.protocol.has_unification_vars() {
            return false;
        }
        let matches = self
            .catalog
            .matching_protocol_head_conformances(&goal.ty, &goal.protocol);
        let [matched] = matches.as_slice() else {
            if matches.len() > 1 {
                self.report_overlapping_conformance(
                    &goal.ty,
                    &goal.protocol,
                    matches[0].protocol,
                    origin,
                );
                return true;
            }
            return false;
        };
        let context = matched.conformance.context.clone();
        let substitution = matched.substitution.clone();
        self.apply_conformance_context(goal, &context, &substitution, origin, queue);
        true
    }

    fn report_overlapping_conformance(
        &mut self,
        ty: &Ty,
        protocol: &ProtocolRef,
        existing: &ProtocolRef,
        origin: CtOrigin,
    ) {
        self.errors.push((
            TypeError::OverlappingConformance {
                ty: self.store.render(ty),
                protocol: protocol.to_string(),
                existing: existing.to_string(),
            },
            origin.node,
        ));
    }

    fn apply_conformance_context(
        &mut self,
        goal: &ConformanceGoal,
        context: &[Predicate],
        substitution: &FxHashMap<Symbol, Ty>,
        origin: CtOrigin,
        queue: &mut Vec<Constraint>,
    ) -> bool {
        let mut constraints = Vec::with_capacity(context.len());
        for predicate in context {
            let predicate =
                predicate.substitute(substitution, &Default::default(), &Default::default());
            if let Some(premise) = self.conformance_goal_from_predicate(&predicate)
                && !self.record_conformance_edge(goal, premise, origin)
            {
                return false;
            }
            constraints.push(predicate.into_constraint(origin));
        }
        queue.extend(constraints);
        true
    }

    fn conformance_goal_from_predicate(
        &mut self,
        predicate: &Predicate,
    ) -> Option<ConformanceGoal> {
        let Predicate::Conforms { ty, protocol } = predicate else {
            return None;
        };
        let ty = normalize_ty(self.store, self.catalog, ty);
        let ty = self.rewrite_ty_from_givens(ty);
        let protocol = ProtocolRef {
            protocol: protocol.protocol,
            args: protocol
                .args
                .iter()
                .map(|arg| {
                    let arg = normalize_ty(self.store, self.catalog, arg);
                    let arg = self.rewrite_ty_from_givens(arg);
                    self.catalog.canonical_conformance_arg(arg)
                })
                .collect(),
        };
        Some(ConformanceGoal { ty, protocol })
    }

    fn record_conformance_edge(
        &mut self,
        from: &ConformanceGoal,
        to: ConformanceGoal,
        origin: CtOrigin,
    ) -> bool {
        if &to == from || self.conformance_goal_reaches(&to, from) {
            let constraint = format!(
                "{} conforms to {}",
                self.store.render(&from.ty),
                self.protocol_summary(&from.protocol)
            );
            self.errors
                .push((TypeError::RecursiveConformance { constraint }, origin.node));
            return false;
        }
        self.conformance_edges
            .entry(from.clone())
            .or_default()
            .insert(to);
        true
    }

    fn conformance_goal_reaches(&self, start: &ConformanceGoal, target: &ConformanceGoal) -> bool {
        let mut stack = vec![start];
        let mut seen = FxHashSet::default();
        while let Some(goal) = stack.pop() {
            if goal == target {
                return true;
            }
            if !seen.insert(goal) {
                continue;
            }
            if let Some(next) = self.conformance_edges.get(goal) {
                stack.extend(next.iter());
            }
        }
        false
    }

    fn try_conforms_via_bounds(
        &mut self,
        protocol: ProtocolRef,
        origin: CtOrigin,
        bounds: &[ProtocolRef],
        queue: &mut Vec<Constraint>,
    ) -> bool {
        let candidates: Vec<_> = bounds
            .iter()
            .flat_map(|bound| self.catalog.protocol_and_supers(bound))
            .filter(|candidate| {
                candidate.protocol == protocol.protocol
                    && candidate.args.len() == protocol.args.len()
            })
            .collect();
        if candidates.iter().any(|candidate| candidate == &protocol) {
            return true;
        }
        match candidates.as_slice() {
            [candidate] => {
                for (expected, actual) in protocol.args.iter().zip(&candidate.args) {
                    queue.push(Constraint::Eq(expected.clone(), actual.clone(), origin));
                }
                true
            }
            [] if self.catalog.bounds_satisfy(bounds, &protocol) => true,
            _ => false,
        }
    }

    pub(super) fn not_conforming(
        &mut self,
        ty: &Ty,
        protocol: ProtocolRef,
        origin: CtOrigin,
    ) -> Option<Constraint> {
        let rendered = self.store.render(ty);
        let error = if origin.reason == CtReason::EqualityComparison
            && let [rhs] = protocol.args.as_slice()
        {
            TypeError::EqualityNotSupported {
                lhs: rendered,
                rhs: self.store.render(rhs),
            }
        } else {
            TypeError::NotConforming {
                ty: rendered,
                protocol: protocol.to_string(),
            }
        };
        self.errors.push((error, origin.node));
        None
    }

    /// Auto-derived conformance for structs and enums without an explicit
    /// row. The derived instance's context is structural: every field or
    /// payload conforms to the corresponding defaulted protocol application,
    /// checked coinductively so recursive nominals terminate.
    pub(super) fn try_derive(
        &mut self,
        symbol: Symbol,
        args: &[Ty],
        protocol: &ProtocolRef,
        origin: CtOrigin,
        queue: &mut Vec<Constraint>,
    ) -> bool {
        if !self.catalog.derivable.contains(&protocol.protocol)
            || self.catalog.is_heap(symbol)
            || !(self.catalog.structs.contains_key(&symbol)
                || self.catalog.enums.contains_key(&symbol))
        {
            return false;
        }
        let self_ty = Ty::Nominal(symbol, args.to_vec());
        let Some(derived_protocol) = self
            .catalog
            .derived_protocol_ref(protocol.protocol, &self_ty)
        else {
            return false;
        };
        if &derived_protocol != protocol {
            return false;
        }
        let goal = ConformanceGoal {
            ty: self_ty.clone(),
            protocol: derived_protocol,
        };
        if !self.derived_seen.insert(goal) {
            return true;
        }

        if let Some(info) = self.catalog.structs.get(&symbol) {
            let substitution: FxHashMap<Symbol, Ty> = info
                .params
                .iter()
                .copied()
                .zip(args.iter().cloned())
                .collect();
            for (_, (_, field_ty)) in &info.fields {
                let field_ty =
                    field_ty.substitute(&substitution, &Default::default(), &Default::default());
                let Some(protocol) = self
                    .catalog
                    .derived_protocol_ref(protocol.protocol, &field_ty)
                else {
                    return false;
                };
                queue.push(Constraint::Conforms {
                    ty: field_ty,
                    protocol,
                    origin,
                });
            }
            return true;
        }
        if let Some(info) = self.catalog.enums.get(&symbol) {
            let substitution: FxHashMap<Symbol, Ty> = info
                .params
                .iter()
                .copied()
                .zip(args.iter().cloned())
                .collect();
            for variant in info.variants.values() {
                let Some(instantiation) = variant
                    .instantiate(&substitution, &Default::default(), &Default::default())
                    .refined_by_result(&self_ty)
                else {
                    continue;
                };
                for payload in instantiation.argument_types {
                    let Some(protocol) = self
                        .catalog
                        .derived_protocol_ref(protocol.protocol, &payload)
                    else {
                        return false;
                    };
                    queue.push(Constraint::Conforms {
                        ty: payload,
                        protocol,
                        origin,
                    });
                }
            }
            return true;
        }
        false
    }
}
