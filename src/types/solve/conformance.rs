use super::*;

impl<'s> Solver<'s> {
    /// One step on a Conforms constraint: discharge against the conformance
    /// table (OutsideIn's class-constraint reaction; instance contexts will
    /// emit further wanteds when conditional conformance lands).
    pub(super) fn try_conforms(
        &mut self,
        ty: Ty,
        protocol: Symbol,
        origin: CtOrigin,
        queue: &mut Vec<Constraint>,
    ) -> Option<Constraint> {
        let normalized = normalize_ty(self.store, self.catalog, &ty);
        let normalized = self.rewrite_ty_from_givens(normalized);
        if self.given_conformance_satisfies(&normalized, protocol) {
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
            } => self.conforms_via_bounds(&ty, protocol, origin, &[existential_protocol]),
            Ty::Param(param) => {
                let bounds = self
                    .catalog
                    .param_bounds
                    .get(&param)
                    .cloned()
                    .unwrap_or_default();
                self.conforms_via_bounds(&ty, protocol, origin, &bounds)
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
                self.conforms_via_bounds(&ty, protocol, origin, &bounds)
            }
            Ty::Nominal(symbol, args) => {
                match self.catalog.conformances.get(&(symbol, protocol)) {
                    Some(conformance) => {
                        let conformance = conformance.clone();
                        // Bind the row's rigid params against the actual
                        // head arguments, then discharge the instance
                        // context as new wanteds (Hall/Hammond/Peyton
                        // Jones/Wadler, *Type Classes in Haskell*).
                        // Associated types are ordinary projections
                        // normalized by `normalize_ty` (Chakravarty/Keller/
                        // Peyton Jones, *Associated Type Synonyms*).
                        let mut substitution: FxHashMap<Symbol, Ty> = FxHashMap::default();
                        for (pattern, actual) in conformance.self_args.iter().zip(&args) {
                            bind_param_pattern(pattern, actual, &mut substitution);
                        }
                        for predicate in &conformance.context {
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
                    None => {
                        if self.try_derive(symbol, &args, protocol, origin, queue) {
                            return None;
                        }
                        self.not_conforming(&ty, protocol, origin)
                    }
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
        protocol: Symbol,
        origin: CtOrigin,
        bounds: &[Symbol],
    ) -> Option<Constraint> {
        if self.catalog.bounds_satisfy(bounds, protocol) {
            None
        } else {
            self.not_conforming(ty, protocol, origin)
        }
    }

    pub(super) fn not_conforming(
        &mut self,
        ty: &Ty,
        protocol: Symbol,
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
    /// structural — every field/payload conforms — checked coinductively so
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
        // A `'heap` struct's derived instance would walk the object graph
        // structurally — cyclic graphs would never terminate at runtime.
        // Require an explicit conformance instead.
        if self.catalog.is_heap(symbol) {
            return false;
        }
        if !self.derived_seen.insert((symbol, protocol)) {
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
