use super::*;

struct Elaborator<'e> {
    store: &'e mut VarStore,
    catalog: &'e TypeCatalog,
    diagnostics: &'e mut DiagnosticSink,
    type_aliases: &'e FxHashMap<Symbol, TypeAliasDef>,
    alias_stack: &'e mut Vec<Symbol>,
    self_types: &'e [Ty],
    resolved: &'e ResolvedNames,
    level: Level,
    obligations: Vec<Constraint>,
}

impl<'e> Elaborator<'e> {
    fn lower_type_alias(
        &mut self,
        symbol: Symbol,
        node: NodeID,
        owner_args: Option<(Symbol, Vec<Ty>)>,
    ) -> Ty {
        if self.alias_stack.contains(&symbol) {
            self.diagnostics.errors.push((
                TypeError::Unsupported(format!("recursive type alias {symbol}")),
                node,
            ));
            return Ty::Error;
        }

        if let Some(alias) = self.type_aliases.get(&symbol).cloned() {
            self.alias_stack.push(symbol);
            let ty = self.lower_annotation(&alias.rhs);
            self.alias_stack.pop();
            return self.substitute_alias_owner(alias.owner, ty, owner_args);
        }

        if let Some(alias) = self.catalog.type_aliases.get(&symbol).cloned() {
            return self.instantiate_catalog_alias(symbol, &alias, node, owner_args);
        }

        self.unsupported(node, "unknown type alias");
        Ty::Error
    }

    fn substitute_alias_owner(
        &mut self,
        owner: Option<Symbol>,
        ty: Ty,
        owner_args: Option<(Symbol, Vec<Ty>)>,
    ) -> Ty {
        let Some(alias_owner) = owner else {
            return ty;
        };
        let Some((path_owner, args)) = owner_args else {
            return ty;
        };
        if alias_owner != path_owner {
            return ty;
        }
        let params = nominal_params(self.catalog, alias_owner);
        let substitution = param_subst(&params, &args);
        ty.substitute(&substitution, &Default::default(), &Default::default())
    }

    fn instantiate_catalog_alias(
        &mut self,
        symbol: Symbol,
        alias: &TypeAliasInfo,
        node: NodeID,
        owner_args: Option<(Symbol, Vec<Ty>)>,
    ) -> Ty {
        let mut tys = FxHashMap::default();
        if let Some((_, args)) = owner_args {
            tys.extend(alias.params.iter().copied().zip(args));
        }
        let mut effs = FxHashMap::default();
        effs.insert(symbol, EffTail::Var(self.store.fresh_eff(self.level, node)));
        let mut rows = FxHashMap::default();
        rows.insert(symbol, RowTail::Var(self.store.fresh_row(self.level, node)));
        alias.ty.substitute(&tys, &effs, &rows)
    }

    fn lower_nominal_path(
        &mut self,
        base: &TypeAnnotation,
        member: &Label,
        member_generics: &[TypeAnnotation],
        node: NodeID,
    ) -> Ty {
        let base_ty = self.lower_annotation(base);
        let label = member.to_string();
        match self.store.shallow(&base_ty) {
            Ty::Nominal(owner, args) => {
                self.lower_nominal_child(owner, args, &label, member_generics, node)
            }
            Ty::Param(param) => {
                self.lower_associated_projection(Ty::Param(param), param, &label, node)
            }
            Ty::Proj(_, _, assoc) => self.lower_associated_projection(base_ty, assoc, &label, node),
            Ty::Error => Ty::Error,
            other => {
                let receiver = self.store.render(&other);
                self.diagnostics
                    .errors
                    .push((TypeError::UnknownMember { receiver, label }, node));
                Ty::Error
            }
        }
    }

    fn lower_nominal_child(
        &mut self,
        owner: Symbol,
        args: Vec<Ty>,
        label: &str,
        member_generics: &[TypeAnnotation],
        node: NodeID,
    ) -> Ty {
        let Some(child) = self
            .resolved
            .child_types
            .get(&owner)
            .and_then(|children| children.get(&Label::Named(label.to_string())))
            .copied()
        else {
            self.diagnostics.errors.push((
                TypeError::UnknownMember {
                    receiver: owner.to_string(),
                    label: label.to_string(),
                },
                node,
            ));
            return Ty::Error;
        };

        match child {
            Symbol::TypeAlias(_) => {
                if !member_generics.is_empty() {
                    self.diagnostics.errors.push((
                        TypeError::ArityMismatch {
                            expected: 0,
                            found: member_generics.len(),
                        },
                        node,
                    ));
                }
                self.lower_type_alias(child, node, Some((owner, args)))
            }
            Symbol::AssociatedType(_) => {
                if !member_generics.is_empty() {
                    self.diagnostics.errors.push((
                        TypeError::ArityMismatch {
                            expected: 0,
                            found: member_generics.len(),
                        },
                        node,
                    ));
                }
                Ty::Param(child)
            }
            Symbol::Struct(_) | Symbol::Enum(_) | Symbol::Protocol(_) | Symbol::Builtin(_) => {
                let lowered_args = member_generics
                    .iter()
                    .map(|generic| self.lower_annotation(generic))
                    .collect();
                Ty::Nominal(child, lowered_args)
            }
            _ => {
                self.diagnostics.errors.push((
                    TypeError::UnknownMember {
                        receiver: owner.to_string(),
                        label: label.to_string(),
                    },
                    node,
                ));
                Ty::Error
            }
        }
    }

    fn lower_associated_projection(
        &mut self,
        base: Ty,
        param: Symbol,
        label: &str,
        node: NodeID,
    ) -> Ty {
        let bounds = self
            .catalog
            .param_bounds
            .get(&param)
            .cloned()
            .unwrap_or_default();
        for protocol in bounds {
            if let Some((owner, assoc)) = self.catalog.associated_type_in(protocol, label) {
                return Ty::Proj(Box::new(base), owner, assoc);
            }
        }
        let receiver = self.store.render(&base);
        self.diagnostics.errors.push((
            TypeError::UnknownMember {
                receiver,
                label: label.to_string(),
            },
            node,
        ));
        Ty::Error
    }

    fn require_nominal_well_formed(&mut self, symbol: Symbol, args: &[Ty], node: NodeID) {
        for predicate in nominal_predicates_for(self.catalog, &Ty::Nominal(symbol, args.to_vec())) {
            self.obligations
                .push(predicate.into_constraint(CtOrigin::new(node, CtReason::Annotation)));
        }
    }

    fn lower_annotation(&mut self, annotation: &TypeAnnotation) -> Ty {
        match &annotation.kind {
            TypeAnnotationKind::Borrow { mutable, inner } => {
                let kind = if *mutable {
                    BorrowKind::Mutable
                } else {
                    BorrowKind::Shared
                };
                Ty::Borrow(kind, Box::new(self.lower_annotation(inner)))
            }
            TypeAnnotationKind::Nominal { name, generics, .. } => {
                if name.name_str() == "Self"
                    && generics.is_empty()
                    && let Some(self_ty) = self.self_types.last()
                {
                    return self_ty.clone();
                }
                let Ok(symbol) = name.symbol() else {
                    return Ty::Error;
                };
                if matches!(symbol, Symbol::TypeAlias(_)) {
                    if !generics.is_empty() {
                        self.diagnostics.errors.push((
                            TypeError::ArityMismatch {
                                expected: 0,
                                found: generics.len(),
                            },
                            annotation.id,
                        ));
                    }
                    return self.lower_type_alias(symbol, annotation.id, None);
                }
                let args: Vec<Ty> = generics.iter().map(|g| self.lower_annotation(g)).collect();
                match symbol {
                    Symbol::TypeParameter(_) | Symbol::AssociatedType(_) => Ty::Param(symbol),
                    _ => {
                        self.require_nominal_well_formed(symbol, &args, annotation.id);
                        Ty::Nominal(symbol, args)
                    }
                }
            }
            TypeAnnotationKind::Func { params, returns } => {
                let params = params.iter().map(|p| self.lower_annotation(p)).collect();
                let ret = self.lower_annotation(returns);
                let eff = EffectRow::open(self.store.fresh_eff(self.level, annotation.id));
                Ty::Func(params, Box::new(ret), eff)
            }
            TypeAnnotationKind::Tuple(items) => match items.as_slice() {
                [] => Ty::unit(),
                [single] => self.lower_annotation(single),
                _ => Ty::Tuple(items.iter().map(|i| self.lower_annotation(i)).collect()),
            },
            TypeAnnotationKind::Record { fields } => {
                let fields = fields
                    .iter()
                    .map(|field| {
                        (
                            Label::Named(field.label.name_str()),
                            self.lower_annotation(&field.value),
                        )
                    })
                    .collect();
                Ty::Record(Row::closed(fields))
            }
            TypeAnnotationKind::Any {
                protocol,
                assoc_bindings,
            } => self.lower_any_annotation(protocol, assoc_bindings, annotation.id),
            TypeAnnotationKind::SelfType(_) => match self.self_types.last() {
                Some(self_ty) => self_ty.clone(),
                None => {
                    self.unsupported(annotation.id, "Self outside a nominal declaration");
                    Ty::Error
                }
            },
            TypeAnnotationKind::NominalPath {
                base,
                member,
                member_generics,
                ..
            } => self.lower_nominal_path(base, member, member_generics, annotation.id),
        }
    }

    fn lower_any_annotation(
        &mut self,
        protocol_annotation: &TypeAnnotation,
        assoc_bindings: &[AnyAssocBinding],
        node: NodeID,
    ) -> Ty {
        let protocol_ty = self.lower_annotation(protocol_annotation);
        let Ty::Nominal(protocol, args) = protocol_ty else {
            self.diagnostics.errors.push((
                TypeError::InvalidExistentialProtocol {
                    ty: protocol_ty.render_mono(),
                },
                node,
            ));
            return Ty::Error;
        };

        if !args.is_empty() || !self.catalog.protocols.contains_key(&protocol) {
            self.diagnostics.errors.push((
                TypeError::InvalidExistentialProtocol {
                    ty: Ty::Nominal(protocol, args).render_mono(),
                },
                node,
            ));
            return Ty::Error;
        }

        let required = self.catalog.associated_types_in(protocol);
        let mut required_by_name: FxHashMap<String, Symbol> = FxHashMap::default();
        for (name, symbol) in &required {
            required_by_name.insert(name.clone(), *symbol);
        }

        let mut assoc: Vec<(Symbol, Ty)> = vec![];
        let mut seen = FxHashSet::default();
        for binding in assoc_bindings {
            let name = binding.name.name_str();
            let Some(symbol) = required_by_name.get(&name).copied() else {
                self.diagnostics.errors.push((
                    TypeError::UnknownAssociatedTypeBinding {
                        protocol: protocol.to_string(),
                        assoc: name,
                    },
                    binding.id,
                ));
                continue;
            };
            if !seen.insert(symbol) {
                self.diagnostics.errors.push((
                    TypeError::DuplicateAssociatedTypeBinding { assoc: name },
                    binding.id,
                ));
                continue;
            }
            assoc.push((symbol, self.lower_annotation(&binding.value)));
        }

        for (name, symbol) in required {
            if !seen.contains(&symbol) {
                self.diagnostics.errors.push((
                    TypeError::MissingAssociatedTypeBinding {
                        protocol: protocol.to_string(),
                        assoc: name,
                    },
                    node,
                ));
            }
        }

        self.validate_object_safe_existential(protocol, node);

        assoc.sort_by_key(|(symbol, _)| *symbol);
        Ty::Any { protocol, assoc }
    }

    fn validate_object_safe_existential(&mut self, protocol: Symbol, node: NodeID) {
        let mut queue = vec![protocol];
        let mut seen = FxHashSet::default();
        while let Some(current) = queue.pop() {
            if !seen.insert(current) {
                continue;
            }
            let Some(info) = self.catalog.protocols.get(&current) else {
                continue;
            };
            let assoc_symbols: FxHashSet<Symbol> = self
                .catalog
                .associated_types_in(current)
                .into_iter()
                .map(|(_, symbol)| symbol)
                .collect();
            let supers = info.supers.clone();
            let requirements: Vec<(String, Ty, Vec<Predicate>)> = info
                .requirements
                .iter()
                .map(|(label, requirement)| {
                    (
                        label.clone(),
                        requirement.sig.clone(),
                        requirement.predicates.clone(),
                    )
                })
                .collect();
            for (label, sig, predicates) in requirements {
                self.validate_object_safe_requirement(
                    protocol,
                    current,
                    &assoc_symbols,
                    &label,
                    &sig,
                    &predicates,
                    node,
                );
            }
            queue.extend(supers);
        }
    }

    fn validate_object_safe_requirement(
        &mut self,
        existential_protocol: Symbol,
        requirement_protocol: Symbol,
        assoc_symbols: &FxHashSet<Symbol>,
        label: &str,
        sig: &Ty,
        predicates: &[Predicate],
        node: NodeID,
    ) {
        let Ty::Func(params, ret, _) = sig else {
            self.object_safety_error(
                existential_protocol,
                format!("requirement {label} is not a method"),
                node,
            );
            return;
        };
        for param in params.iter().skip(1) {
            if ty_mentions_param(param, requirement_protocol) {
                self.object_safety_error(
                    existential_protocol,
                    format!("requirement {label} mentions Self outside the receiver"),
                    node,
                );
                return;
            }
        }
        if ty_mentions_param(ret, requirement_protocol) {
            self.object_safety_error(
                existential_protocol,
                format!("requirement {label} mentions Self outside the receiver"),
                node,
            );
            return;
        }
        for predicate in predicates {
            if predicate_mentions_param(predicate, requirement_protocol) {
                self.object_safety_error(
                    existential_protocol,
                    format!("requirement {label} has a Self-bearing where predicate"),
                    node,
                );
                return;
            }
        }

        let mut params_in_requirement = FxHashSet::default();
        collect_ty_params(sig, None, &mut params_in_requirement);
        for predicate in predicates {
            collect_predicate_params(predicate, None, &mut params_in_requirement);
        }
        params_in_requirement.remove(&requirement_protocol);
        for assoc in assoc_symbols {
            params_in_requirement.remove(assoc);
        }
        if !params_in_requirement.is_empty() {
            self.object_safety_error(
                existential_protocol,
                format!("requirement {label} is generic"),
                node,
            );
        }
    }

    fn object_safety_error(&mut self, protocol: Symbol, reason: String, node: NodeID) {
        self.diagnostics.errors.push((
            TypeError::NonObjectSafeExistential {
                protocol: protocol.to_string(),
                reason,
            },
            node,
        ));
    }

    fn unsupported(&mut self, node: NodeID, what: &str) {
        self.diagnostics.unsupported(node, what);
    }
}

impl<'s, 'a> CatalogBuilder<'s, 'a> {
    fn elaborator(&mut self) -> Elaborator<'_> {
        Elaborator {
            store: &mut *self.store,
            catalog: &*self.catalog,
            diagnostics: &mut *self.diagnostics,
            type_aliases: &*self.type_aliases,
            alias_stack: &mut *self.alias_stack,
            self_types: self.self_types.as_slice(),
            resolved: self.resolved,
            level: self.level,
            obligations: vec![],
        }
    }

    pub(super) fn lower_annotation(&mut self, annotation: &TypeAnnotation) -> Ty {
        let mut elab = self.elaborator();
        elab.lower_annotation(annotation)
    }

    pub(super) fn lower_type_alias(
        &mut self,
        symbol: Symbol,
        node: NodeID,
        owner_args: Option<(Symbol, Vec<Ty>)>,
    ) -> Ty {
        let mut elab = self.elaborator();
        elab.lower_type_alias(symbol, node, owner_args)
    }
}

macro_rules! impl_checking_elaboration_for {
    ($target:ident<$session:lifetime, $source:lifetime>) => {
        impl<$session, $source> $target<$session, $source> {
            fn elaborator(&mut self) -> Elaborator<'_> {
                Elaborator {
                    store: &mut *self.store,
                    catalog: &*self.catalog,
                    diagnostics: &mut *self.diagnostics,
                    type_aliases: &*self.type_aliases,
                    alias_stack: &mut *self.alias_stack,
                    self_types: self.self_types.as_slice(),
                    resolved: self.resolved,
                    level: self.level,
                    obligations: vec![],
                }
            }

            pub(super) fn lower_annotation(&mut self, annotation: &TypeAnnotation) -> Ty {
                let (ty, obligations) = {
                    let mut elab = self.elaborator();
                    let ty = elab.lower_annotation(annotation);
                    (ty, std::mem::take(&mut elab.obligations))
                };
                self.wanteds.extend(obligations);
                ty
            }
        }
    };
}

impl_checking_elaboration_for!(BodyChecker<'s, 'a>);
impl_checking_elaboration_for!(BindingGroupChecker<'s, 'a>);

impl<'s, 'a> BodyChecker<'s, 'a> {
    pub(super) fn emit_nominal_well_formedness(
        &mut self,
        symbol: Symbol,
        args: &[Ty],
        node: NodeID,
    ) {
        self.emit_nominal_well_formedness_for_ty(&Ty::Nominal(symbol, args.to_vec()), node);
    }

    pub(super) fn emit_nominal_well_formedness_for_ty(&mut self, ty: &Ty, node: NodeID) {
        let Ty::Nominal(symbol, args) = self.store.shallow(ty) else {
            return;
        };
        for predicate in nominal_predicates_for(self.catalog, &Ty::Nominal(symbol, args)) {
            self.wanteds
                .push(predicate.into_constraint(CtOrigin::new(node, CtReason::Annotation)));
        }
    }
}
