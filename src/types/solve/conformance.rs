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
            } => self.conforms_via_bounds(&ty, protocol, origin, &[existential_protocol], queue),
            Ty::Param(param) => {
                let bounds = self
                    .catalog
                    .param_bounds
                    .get(&param)
                    .cloned()
                    .unwrap_or_default();
                self.conforms_via_bounds(&ty, protocol, origin, &bounds, queue)
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
                let bounds = self
                    .catalog
                    .param_bounds
                    .get(&assoc_symbol)
                    .cloned()
                    .unwrap_or_default();
                self.conforms_via_bounds(&ty, protocol, origin, &bounds, queue)
            }
            Ty::Nominal(symbol, args) => {
                if protocol.has_unification_vars() {
                    return Some(Constraint::Conforms {
                        ty,
                        protocol,
                        origin,
                    });
                }
                let matches = self.catalog.matching_conformances(symbol, &args, &protocol);
                match matches.as_slice() {
                    [matched] => {
                        let context = matched.conformance.context.clone();
                        let substitution = matched.substitution.clone();
                        for predicate in &context {
                            queue.push(
                                predicate
                                    .substitute(
                                        &substitution,
                                        &Default::default(),
                                        &Default::default(),
                                    )
                                    .into_constraint(origin),
                            );
                        }
                        None
                    }
                    [] => {
                        if protocol.args.is_empty()
                            && self.try_derive(symbol, &args, protocol.protocol, origin, queue)
                        {
                            return None;
                        }
                        self.not_conforming(&ty, protocol, origin)
                    }
                    _ => self.not_conforming(&ty, protocol, origin),
                }
            }
            other => self.not_conforming(&other, protocol, origin),
        }
    }

    /// Discharge a `Conforms` against the bounds known for a type: satisfied
    /// when the bound set transitively includes the required protocol,
    /// otherwise a `NotConforming` error. Shared by the existential, type
    /// parameter, and projection cases.
    pub(super) fn conforms_via_bounds(
        &mut self,
        ty: &Ty,
        protocol: ProtocolRef,
        origin: CtOrigin,
        bounds: &[ProtocolRef],
        queue: &mut Vec<Constraint>,
    ) -> Option<Constraint> {
        let candidates: Vec<_> = bounds
            .iter()
            .flat_map(|bound| self.catalog.protocol_and_supers(bound))
            .filter(|candidate| {
                candidate.protocol == protocol.protocol
                    && candidate.args.len() == protocol.args.len()
            })
            .collect();
        if candidates.iter().any(|candidate| candidate == &protocol) {
            return None;
        }
        match candidates.as_slice() {
            [candidate] => {
                for (expected, actual) in protocol.args.iter().zip(&candidate.args) {
                    queue.push(Constraint::Eq(expected.clone(), actual.clone(), origin));
                }
                None
            }
            [] if self.catalog.bounds_satisfy(bounds, &protocol) => None,
            _ => self.not_conforming(ty, protocol, origin),
        }
    }

    pub(super) fn not_conforming(
        &mut self,
        ty: &Ty,
        protocol: ProtocolRef,
        origin: CtOrigin,
    ) -> Option<Constraint> {
        let rendered = self.store.render(ty);
        self.errors.push((
            TypeError::NotConforming {
                ty: rendered,
                protocol: protocol.to_string(),
            },
            origin.node,
        ));
        None
    }

    /// Auto-derived conformance (today: Showable) for structs and enums
    /// without an explicit row. The derived instance's context is
    /// structural: every field/payload conforms, checked coinductively so
    /// recursive nominals terminate.
    pub(super) fn try_derive(
        &mut self,
        symbol: Symbol,
        args: &[Ty],
        protocol: Symbol,
        origin: CtOrigin,
        queue: &mut Vec<Constraint>,
    ) -> bool {
        if !self.catalog.derivable.contains(&protocol) {
            return false;
        }
        if self.catalog.is_heap(symbol) {
            return false;
        }
        if !self.derived_seen.insert((symbol, protocol)) {
            return true;
        }
        let protocol_ref = ProtocolRef::bare(protocol);
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
                queue.push(Constraint::Conforms {
                    ty: field_ty,
                    protocol: protocol_ref.clone(),
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
            let self_ty = Ty::Nominal(symbol, args.to_vec());
            for variant in info.variants.values() {
                let Some(instantiation) = variant
                    .instantiate(&substitution, &Default::default(), &Default::default())
                    .refined_by_result(&self_ty)
                else {
                    continue;
                };
                for payload in instantiation.argument_types {
                    queue.push(Constraint::Conforms {
                        ty: payload,
                        protocol: protocol_ref.clone(),
                        origin,
                    });
                }
            }
            return true;
        }
        false
    }
}
