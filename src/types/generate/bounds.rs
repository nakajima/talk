use super::*;

macro_rules! impl_bounds_for {
    ($target:ident<$session:lifetime, $source:lifetime>) => {
        impl<$session, $source> $target<$session, $source> {
            pub(super) fn register_generic_bounds(&mut self, generics: &[GenericDecl]) {
                for generic in generics {
                    let Ok(symbol) = generic.name.symbol() else {
                        continue;
                    };
                    for protocol in generic
                        .conformances
                        .iter()
                        .filter_map(Self::annotation_symbol)
                    {
                        self.register_param_bound(symbol, protocol);
                    }
                }
            }

            pub(super) fn register_func_bounds(&mut self, func: &Func) {
                self.register_generic_bounds(&func.generics);
                self.register_where_bounds(func.where_clause.as_ref());
            }

            pub(super) fn register_where_bounds(&mut self, where_clause: Option<&WhereClause>) {
                let Some(where_clause) = where_clause else {
                    return;
                };
                for predicate in &where_clause.predicates {
                    let WherePredicateKind::Conforms { ty, protocols } = &predicate.kind else {
                        continue;
                    };
                    let TypeAnnotationKind::Nominal { name, .. } = &ty.kind else {
                        continue;
                    };
                    let Ok(param @ (Symbol::TypeParameter(_) | Symbol::AssociatedType(_))) =
                        name.symbol()
                    else {
                        continue;
                    };
                    for protocol in protocols.iter().filter_map(Self::annotation_symbol) {
                        self.register_param_bound(param, protocol);
                    }
                }
            }

            pub(super) fn annotation_symbol(annotation: &TypeAnnotation) -> Option<Symbol> {
                match &annotation.kind {
                    TypeAnnotationKind::Nominal { name, .. }
                    | TypeAnnotationKind::SelfType(name) => name.symbol().ok(),
                    _ => None,
                }
            }

            pub(super) fn register_param_bound(&mut self, param: Symbol, protocol: Symbol) {
                let bounds = self.catalog.param_bounds.entry(param).or_default();
                if !bounds.contains(&protocol) {
                    bounds.push(protocol);
                }
            }

            pub(super) fn declared_predicates(
                &mut self,
                generics: &[GenericDecl],
                where_clause: Option<&WhereClause>,
            ) -> Vec<Predicate> {
                let mut predicates = vec![];
                for generic in generics {
                    let Ok(symbol) = generic.name.symbol() else {
                        continue;
                    };
                    for conformance in &generic.conformances {
                        predicates.extend(
                            self.lower_protocol_application_predicates(
                                Ty::Param(symbol),
                                conformance,
                            ),
                        );
                    }
                }
                if let Some(where_clause) = where_clause {
                    let self_ty = self.self_types.last().cloned();
                    let mut context_params: FxHashSet<Symbol> = generics
                        .iter()
                        .filter_map(|generic| generic.name.symbol().ok())
                        .chain(self_ty.as_ref().and_then(self_context_param))
                        .collect();
                    if let Some(Ty::Param(protocol)) = &self_ty
                        && let Some(info) = self.catalog.protocols.get(protocol)
                    {
                        context_params.extend(info.assoc.values().copied());
                    }
                    predicates.extend(self.lower_where_clause_predicates(
                        where_clause,
                        &context_params,
                        self_ty.as_ref(),
                    ));
                }
                let mut deduped = vec![];
                for predicate in predicates {
                    if !deduped.contains(&predicate) {
                        deduped.push(predicate);
                    }
                }
                deduped
            }

            pub(super) fn lower_where_clause_predicates(
                &mut self,
                where_clause: &WhereClause,
                context_params: &FxHashSet<Symbol>,
                self_ty: Option<&Ty>,
            ) -> Vec<Predicate> {
                let mut predicates = vec![];
                for predicate in &where_clause.predicates {
                    let lowered =
                        match &predicate.kind {
                            WherePredicateKind::TypeEq { lhs, rhs } => vec![Predicate::TypeEq(
                                self.lower_annotation(lhs),
                                self.lower_annotation(rhs),
                            )],
                            WherePredicateKind::Conforms { ty, protocols } => {
                                let ty = self.lower_annotation(ty);
                                let mut lowered = vec![];
                                for protocol in protocols {
                                    lowered.extend(self.lower_protocol_application_predicates(
                                        ty.clone(),
                                        protocol,
                                    ));
                                }
                                lowered
                            }
                        };
                    for lowered in lowered {
                        if !predicate_mentions_context(&lowered, context_params, self_ty)
                            && self
                                .diagnostics
                                .reported_where_diagnostics
                                .insert((predicate.id, "invalid"))
                        {
                            self.diagnostics
                                .errors
                                .push((TypeError::InvalidWherePredicate, predicate.id));
                        }
                        if predicates.contains(&lowered) {
                            if self
                                .diagnostics
                                .reported_where_diagnostics
                                .insert((predicate.id, "duplicate"))
                            {
                                self.diagnostics.warnings.push((
                                    TypeError::DuplicatePredicate {
                                        predicate: lowered.render_mono(),
                                    },
                                    predicate.id,
                                ));
                            }
                        } else {
                            predicates.push(lowered);
                        }
                    }
                }
                predicates
            }

            pub(super) fn lower_protocol_application_predicates(
                &mut self,
                ty: Ty,
                protocol_annotation: &TypeAnnotation,
            ) -> Vec<Predicate> {
                let (protocol, assoc_args) = match &protocol_annotation.kind {
                    TypeAnnotationKind::Nominal { name, generics, .. } => {
                        let Ok(protocol) = name.symbol() else {
                            return vec![];
                        };
                        (protocol, generics.as_slice())
                    }
                    TypeAnnotationKind::SelfType(name) => {
                        let Ok(protocol) = name.symbol() else {
                            return vec![];
                        };
                        (protocol, [].as_slice())
                    }
                    _ => {
                        self.unsupported(
                            protocol_annotation.id,
                            "non-nominal protocol names in where clauses",
                        );
                        return vec![];
                    }
                };

                let mut predicates = vec![Predicate::Conforms {
                    ty: ty.clone(),
                    protocol,
                }];
                self.protocol_refinement_predicates(
                    protocol,
                    ty.clone(),
                    &mut FxHashSet::default(),
                    &mut predicates,
                );
                if assoc_args.is_empty() {
                    return predicates;
                }

                let assoc_symbols: Vec<Symbol> = self
                    .catalog
                    .protocols
                    .get(&protocol)
                    .map(|info| info.assoc.values().copied().collect())
                    .unwrap_or_default();
                if assoc_args.len() != assoc_symbols.len() {
                    self.diagnostics.errors.push((
                        TypeError::ArityMismatch {
                            expected: assoc_symbols.len(),
                            found: assoc_args.len(),
                        },
                        protocol_annotation.id,
                    ));
                    return predicates;
                }
                for (assoc, arg) in assoc_symbols.into_iter().zip(assoc_args) {
                    predicates.push(Predicate::TypeEq(
                        Ty::Proj(Box::new(ty.clone()), protocol, assoc),
                        self.lower_annotation(arg),
                    ));
                }
                predicates
            }

            pub(super) fn protocol_refinement_predicates(
                &mut self,
                protocol: Symbol,
                ty: Ty,
                seen: &mut FxHashSet<Symbol>,
                out: &mut Vec<Predicate>,
            ) {
                if !seen.insert(protocol) {
                    return;
                }
                let Some(info) = self.catalog.protocols.get(&protocol).cloned() else {
                    return;
                };
                let mut substitution = FxHashMap::default();
                substitution.insert(protocol, ty.clone());
                for assoc in info.assoc.values() {
                    substitution.insert(*assoc, Ty::Proj(Box::new(ty.clone()), protocol, *assoc));
                }
                for predicate in info.predicates {
                    let predicate = predicate.substitute(
                        &substitution,
                        &Default::default(),
                        &Default::default(),
                    );
                    if !out.contains(&predicate) {
                        out.push(predicate);
                    }
                }
                for super_protocol in info.supers {
                    self.protocol_refinement_predicates(super_protocol, ty.clone(), seen, out);
                }
            }
        }
    };
}

impl_bounds_for!(CatalogBuilder<'s, 'a>);
impl_bounds_for!(BodyChecker<'s, 'a>);
impl_bounds_for!(BindingGroupChecker<'s, 'a>);
