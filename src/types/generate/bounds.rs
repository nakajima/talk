use super::*;

macro_rules! impl_bounds_for {
    ($target:ident<$session:lifetime, $source:lifetime>) => {
        impl<$session, $source> $target<$session, $source> {
            pub(super) fn register_generic_bounds(&mut self, generics: &[GenericDecl]) {
                for generic in generics {
                    let Ok(symbol) = generic.name.symbol() else {
                        continue;
                    };
                    for conformance in &generic.conformances {
                        if let Some((protocol, _)) =
                            self.lower_protocol_ref_with_self(conformance, Some(&Ty::Param(symbol)))
                        {
                            self.register_param_bound(symbol, protocol);
                        }
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
                    for protocol in protocols {
                        if let Some((protocol, _)) =
                            self.lower_protocol_ref_with_self(protocol, Some(&Ty::Param(param)))
                        {
                            self.register_param_bound(param, protocol);
                        }
                    }
                }
            }

            pub(super) fn register_param_bound(&mut self, param: Symbol, protocol: ProtocolRef) {
                let bounds = self.catalog.param_bounds.entry(param).or_default();
                if !bounds.contains(&protocol) {
                    bounds.push(protocol);
                }
            }

            pub(super) fn lower_protocol_ref_with_self(
                &mut self,
                annotation: &TypeAnnotation,
                self_ty: Option<&Ty>,
            ) -> Option<(ProtocolRef, Vec<TypeAnnotation>)> {
                let (protocol, generics) = match &annotation.kind {
                    TypeAnnotationKind::Nominal { name, generics, .. } => {
                        (name.symbol().ok()?, generics.as_slice())
                    }
                    TypeAnnotationKind::SelfType(name) => (name.symbol().ok()?, [].as_slice()),
                    _ => {
                        self.unsupported(
                            annotation.id,
                            "non-nominal protocol names in where clauses",
                        );
                        return None;
                    }
                };
                let (params, defaults) = self
                    .catalog
                    .protocols
                    .get(&protocol)
                    .map(|info| (info.params.clone(), info.param_defaults.clone()))
                    .unwrap_or_default();
                let param_count = params.len();
                if param_count == 0 {
                    return Some((ProtocolRef::bare(protocol), generics.to_vec()));
                }
                if generics.len() > param_count {
                    self.diagnostics.errors.push((
                        TypeError::ArityMismatch {
                            expected: param_count,
                            found: generics.len(),
                        },
                        annotation.id,
                    ));
                    return Some((ProtocolRef::bare(protocol), vec![]));
                }

                let mut args: Vec<Ty> = generics
                    .iter()
                    .map(|generic| self.lower_annotation(generic))
                    .collect();
                let mut substitution = FxHashMap::default();
                substitution.insert(
                    protocol,
                    self_ty.cloned().unwrap_or_else(|| Ty::Param(protocol)),
                );
                for (param, arg) in params.iter().copied().zip(args.iter().cloned()) {
                    substitution.insert(param, arg);
                }
                let provided = args.len();
                let mut reported_missing_default = false;
                for index in provided..param_count {
                    match defaults.get(index).and_then(Clone::clone) {
                        Some(default) => {
                            let default = default.substitute(
                                &substitution,
                                &Default::default(),
                                &Default::default(),
                            );
                            substitution.insert(params[index], default.clone());
                            args.push(default);
                        }
                        None => {
                            if !reported_missing_default {
                                self.diagnostics.errors.push((
                                    TypeError::ArityMismatch {
                                        expected: param_count,
                                        found: provided,
                                    },
                                    annotation.id,
                                ));
                                reported_missing_default = true;
                            }
                            args.push(Ty::Error);
                        }
                    }
                }
                Some((ProtocolRef { protocol, args }, vec![]))
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
                let Some((protocol, assoc_args)) =
                    self.lower_protocol_ref_with_self(protocol_annotation, Some(&ty))
                else {
                    return vec![];
                };

                let mut predicates = vec![Predicate::Conforms {
                    ty: ty.clone(),
                    protocol: protocol.clone(),
                }];
                self.protocol_refinement_predicates(
                    protocol.clone(),
                    ty.clone(),
                    &mut FxHashSet::default(),
                    &mut predicates,
                );
                if assoc_args.is_empty() {
                    return predicates;
                }

                let assoc_symbols = self.catalog.declared_associated_types_in_ref(&protocol);
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
                for ((_, owner, assoc), arg) in assoc_symbols.into_iter().zip(assoc_args) {
                    predicates.push(Predicate::TypeEq(
                        Ty::Proj(Box::new(ty.clone()), owner, assoc),
                        self.lower_annotation(&arg),
                    ));
                }
                predicates
            }

            pub(super) fn protocol_refinement_predicates(
                &mut self,
                protocol: ProtocolRef,
                ty: Ty,
                seen: &mut FxHashSet<ProtocolRef>,
                out: &mut Vec<Predicate>,
            ) {
                if !seen.insert(protocol.clone()) {
                    return;
                }
                let Some(info) = self.catalog.protocols.get(&protocol.protocol).cloned() else {
                    return;
                };
                let mut substitution = FxHashMap::default();
                substitution.insert(protocol.protocol, ty.clone());
                for (param, arg) in info
                    .params
                    .iter()
                    .copied()
                    .zip(protocol.args.iter().cloned())
                {
                    substitution.insert(param, arg);
                }
                for assoc in info.assoc.values() {
                    substitution.insert(
                        *assoc,
                        Ty::Proj(Box::new(ty.clone()), protocol.clone(), *assoc),
                    );
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
                for super_protocol in self
                    .catalog
                    .protocol_and_supers(&protocol)
                    .into_iter()
                    .skip(1)
                {
                    self.protocol_refinement_predicates(super_protocol, ty.clone(), seen, out);
                }
            }
        }
    };
}

impl_bounds_for!(CatalogBuilder<'s, 'a>);
impl_bounds_for!(BodyChecker<'s, 'a>);
impl_bounds_for!(BindingGroupChecker<'s, 'a>);
