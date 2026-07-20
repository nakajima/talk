use super::*;

macro_rules! impl_bounds_for {
    ($target:ident<$session:lifetime, $source:lifetime>) => {
        impl<$session, $source> $target<$session, $source> {
            pub(super) fn register_generic_bounds(&mut self, generics: &[GenericDecl]) {
                for generic in generics {
                    let Ok(symbol) = generic.name.symbol() else {
                        continue;
                    };
                    if let Some(static_annotation) = &generic.static_ty {
                        self.register_static_param(symbol, static_annotation);
                        continue;
                    }
                    for conformance in &generic.conformances {
                        if let Some((protocol, _)) =
                            self.lower_protocol_ref_with_self(conformance, Some(&Ty::Param(symbol)))
                        {
                            self.register_param_bound(symbol, protocol);
                        }
                    }
                }
            }

            /// Record a static value parameter's declared value type
            /// (ADR 0035). The admitted static domain is `Int`, `Bool`,
            /// and fieldless enums; anything else is rejected and the
            /// parameter is left untagged (it then behaves as an ordinary
            /// type parameter for error recovery).
            pub(super) fn register_static_param(
                &mut self,
                param: Symbol,
                annotation: &TypeAnnotation,
            ) {
                let ty = self.lower_annotation(annotation);
                let admitted = match &ty {
                    Ty::Nominal(symbol, args) if args.is_empty() => {
                        *symbol == Symbol::Int
                            || *symbol == Symbol::Bool
                            || self.catalog.enums.get(symbol).is_some_and(|info| {
                                info.variants
                                    .values()
                                    .all(|variant| variant.payload_labels.is_empty())
                            })
                    }
                    _ => false,
                };
                if !admitted {
                    self.diagnostics.errors.push((
                        TypeError::UnsupportedStaticParamType {
                            ty: ty.render_mono(),
                        },
                        annotation.id,
                    ));
                    return;
                }
                self.catalog.static_params.insert(param, ty);
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

            /// The canonical parameter records for a declared generic
            /// list: symbol, kind (from the registered static value
            /// types), and validated default. Call after
            /// `register_generic_bounds`.
            #[allow(dead_code)]
            pub(super) fn declared_params(&mut self, generics: &[GenericDecl]) -> Vec<SchemeParam> {
                let defaults = self.lower_generic_defaults(generics);
                generics
                    .iter()
                    .zip(defaults)
                    .filter_map(|(generic, default)| {
                        let symbol = generic.name.symbol().ok()?;
                        let mut param = scheme_param(self.catalog, symbol);
                        param.default = default;
                        Some(param)
                    })
                    .collect()
            }

            /// The one owner of generic-parameter defaults (ADR 0035):
            /// (macro-expanded per target; not every checking context
            /// declares generics, hence the allow)
            #[allow(dead_code)]
            /// lowers each declared default according to its parameter's
            /// kind, rejects forward references (a default may mention
            /// only EARLIER parameters), and rejects closed negative
            /// static Int defaults. Nominal annotations, constructors,
            /// protocol applications, and scheme instantiation all
            /// consume the values this produces.
            pub(super) fn lower_generic_defaults(
                &mut self,
                generics: &[GenericDecl],
            ) -> Vec<Option<Ty>> {
                let declared: Vec<Symbol> = generics
                    .iter()
                    .filter_map(|generic| generic.name.symbol().ok())
                    .collect();
                generics
                    .iter()
                    .enumerate()
                    .map(|(index, generic)| {
                        let default = generic.default.as_ref()?;
                        let expected = generic
                            .name
                            .symbol()
                            .ok()
                            .and_then(|param| self.catalog.static_params.get(&param))
                            .cloned();
                        let lowered = match (&expected, default) {
                            (Some(expected), default) => {
                                let mut elab = self.elaborator();
                                elab.lower_static_argument(default, expected)
                            }
                            (None, GenericArg::Type(annotation)) => {
                                self.lower_annotation(annotation)
                            }
                            (None, GenericArg::Static(expr)) => {
                                self.diagnostics
                                    .errors
                                    .push((TypeError::StaticValueInTypePosition, expr.id));
                                Ty::Error
                            }
                        };
                        let earlier = &declared[..index];
                        let mut forward = None;
                        let _ = lowered.try_visit(
                            &mut |ty: &Ty| -> std::ops::ControlFlow<()> {
                                if let Ty::Param(param) = ty
                                    && declared.contains(param)
                                    && !earlier.contains(param)
                                {
                                    forward = Some(*param);
                                    return std::ops::ControlFlow::Break(());
                                }
                                std::ops::ControlFlow::Continue(())
                            },
                        );
                        if let Some(param) = forward {
                            self.diagnostics.errors.push((
                                TypeError::InvalidGenericDefault {
                                    reason: format!(
                                        "a default may mention only earlier parameters, not {param}"
                                    ),
                                },
                                default.id(),
                            ));
                            return Some(Ty::Error);
                        }
                        if matches!(expected, Some(Ty::Nominal(symbol, _)) if symbol == Symbol::Int)
                            && let Some(int) = crate::types::ty::StaticInt::from_ty(&lowered)
                            && let Some(constant) = int.as_constant()
                            && *constant < 0.into()
                        {
                            self.diagnostics.errors.push((
                                TypeError::InvalidGenericDefault {
                                    reason: "a static Int default must be nonnegative".to_string(),
                                },
                                default.id(),
                            ));
                            return Some(Ty::Error);
                        }
                        Some(lowered)
                    })
                    .collect()
            }

            /// The static value domain of a syntactically static operand
            /// (ADR 0035): a literal or arithmetic form, or a bare name
            /// resolving to a registered static parameter. `None` means
            /// the operand is an ordinary type.
            pub(super) fn static_operand_domain(&self, arg: &GenericArg) -> Option<Ty> {
                match arg {
                    GenericArg::Static(expr) => self.static_expr_domain(expr),
                    GenericArg::Type(annotation) => match &annotation.kind {
                        TypeAnnotationKind::Nominal { name, generics, .. }
                            if generics.is_empty() =>
                        {
                            let symbol = name.symbol().ok()?;
                            self.catalog.static_params.get(&symbol).cloned()
                        }
                        _ => None,
                    },
                }
            }

            pub(super) fn static_expr_domain(&self, expr: &StaticExpr) -> Option<Ty> {
                match &expr.kind {
                    StaticExprKind::Int(_) | StaticExprKind::Op { .. } => {
                        Some(Ty::Nominal(Symbol::Int, vec![]))
                    }
                    StaticExprKind::Bool(_) => Some(Ty::Nominal(Symbol::Bool, vec![])),
                    StaticExprKind::Group(inner) => self.static_expr_domain(inner),
                    StaticExprKind::Path(annotation) => {
                        self.static_operand_domain(&GenericArg::Type(annotation.clone()))
                    }
                }
            }

            /// A protocol application argument, interpreted by its
            /// declared parameter's kind (ADR 0035): a `static` slot
            /// takes a static value expression.
            pub(super) fn lower_protocol_generic_arg(
                &mut self,
                params: &[SchemeParam],
                index: usize,
                generic: &GenericArg,
            ) -> Ty {
                let expected = params.get(index).and_then(|param| match &param.kind {
                    crate::types::ty::ParamKind::Static(value_ty) => Some(value_ty.clone()),
                    crate::types::ty::ParamKind::Type => None,
                });
                match (expected, generic) {
                    (Some(expected), generic) => {
                        let mut elab = self.elaborator();
                        let ty = elab.lower_static_argument(generic, &expected);
                        elab.emit_static_nonneg(&expected, &ty, generic.id());
                        let obligations = std::mem::take(&mut elab.obligations);
                        drop(elab);
                        self.absorb_obligations(obligations);
                        ty
                    }
                    (None, GenericArg::Type(annotation)) => self.lower_annotation(annotation),
                    (None, GenericArg::Static(expr)) => {
                        self.diagnostics
                            .errors
                            .push((TypeError::StaticValueInTypePosition, expr.id));
                        Ty::Error
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
            ) -> Option<(ProtocolRef, Vec<GenericArg>)> {
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
                let params = self
                    .catalog
                    .protocols
                    .get(&protocol)
                    .map(|info| info.params.clone())
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
                    .enumerate()
                    .map(|(index, generic)| {
                        self.lower_protocol_generic_arg(&params, index, generic)
                    })
                    .collect();
                let mut substitution = FxHashMap::default();
                substitution.insert(
                    protocol,
                    self_ty.cloned().unwrap_or_else(|| Ty::Param(protocol)),
                );
                for (param, arg) in params.iter().zip(args.iter().cloned()) {
                    substitution.insert(param.symbol, arg);
                }
                let provided = args.len();
                let mut reported_missing_default = false;
                for index in provided..param_count {
                    match params[index].default.clone() {
                        Some(default) => {
                            let default = default.substitute(
                                &substitution,
                                &Default::default(),
                                &Default::default(),
                            );
                            // A materialized default is a formed static
                            // argument like any explicit one (ADR 0035 §2).
                            if let crate::types::ty::ParamKind::Static(expected) =
                                &params[index].kind
                            {
                                let mut elab = self.elaborator();
                                elab.emit_static_nonneg(expected, &default, annotation.id);
                                let obligations = std::mem::take(&mut elab.obligations);
                                drop(elab);
                                self.absorb_obligations(obligations);
                            }
                            substitution.insert(params[index].symbol, default.clone());
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
                            // `==` between static operands is the static
                            // equality relation (ADR 0035 §4), detected by
                            // either side being syntactically static.
                            WherePredicateKind::TypeEq { lhs, rhs } => {
                                match self
                                    .static_operand_domain(lhs)
                                    .or_else(|| self.static_operand_domain(rhs))
                                {
                                    Some(expected) => {
                                        let mut elab = self.elaborator();
                                        let lhs = elab.lower_static_argument(lhs, &expected);
                                        let rhs = elab.lower_static_argument(rhs, &expected);
                                        vec![Predicate::StaticCmp {
                                            op: crate::types::ty::StaticCmpOp::Eq,
                                            lhs,
                                            rhs,
                                        }]
                                    }
                                    None => {
                                        let (Some(lhs), Some(rhs)) = (lhs.as_type(), rhs.as_type())
                                        else {
                                            self.diagnostics.errors.push((
                                                TypeError::InvalidWherePredicate,
                                                predicate.id,
                                            ));
                                            continue;
                                        };
                                        vec![Predicate::TypeEq(
                                            self.lower_annotation(lhs),
                                            self.lower_annotation(rhs),
                                        )]
                                    }
                                }
                            }
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
                            // ADR 0035 §4: a static integer ordering. The
                            // operands lower through the static index
                            // language against the `Int` domain.
                            WherePredicateKind::StaticCmp { strict, lhs, rhs } => {
                                let int = Ty::Nominal(Symbol::Int, vec![]);
                                let mut elab = self.elaborator();
                                let lhs = elab.lower_static_argument(lhs, &int);
                                let rhs = elab.lower_static_argument(rhs, &int);
                                vec![Predicate::StaticCmp {
                                    op: if *strict {
                                        crate::types::ty::StaticCmpOp::Lt
                                    } else {
                                        crate::types::ty::StaticCmpOp::Le
                                    },
                                    lhs,
                                    rhs,
                                }]
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
                    // Associated-type bindings are types.
                    let Some(annotation) = arg.as_type() else {
                        self.diagnostics.errors.push((
                            TypeError::StaticValueInTypePosition,
                            arg.id(),
                        ));
                        continue;
                    };
                    predicates.push(Predicate::TypeEq(
                        Ty::Proj(Box::new(ty.clone()), owner, assoc),
                        self.lower_annotation(annotation),
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
                for (param, arg) in info.params.iter().zip(protocol.args.iter().cloned()) {
                    substitution.insert(param.symbol, arg);
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
