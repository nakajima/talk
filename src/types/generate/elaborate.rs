use super::*;

use crate::node_kinds::type_application::TypeApplication;

/// Apply a parameter's ownership mode to its lowered annotation type
/// (ADR 0018). Explicit `borrow`/`mut` wrap the type in a borrow;
/// `consume` (and unadorned, until the borrow-by-default flip) lowers as
/// written. A user-written `mut`/`consume` on an annotation that already
/// spells a borrow is a declaration-site conflict — the mode and the `&`
/// are rival spellings of the same decision (a desugar-stamped default on
/// a legacy `&T` annotation is not: `init(c: &T)` still means borrow).
/// Shared borrows of Copy-grade heads erase (`&Int` never surfaces —
/// ADR 0014): a scalar borrow IS a value copy, and keeping it bare keeps
/// schemes, flow provenance, and renderings scalar-shaped.
pub(super) fn apply_param_mode(
    catalog: &TypeCatalog,
    param: &Parameter,
    ty: Ty,
    diagnostics: &mut DiagnosticSink,
) -> Ty {
    if let Some(mode @ (ParamMode::Mut | ParamMode::Consume | ParamMode::ConsumeMut)) = param.mode
        && param.mode_span.is_some()
        && matches!(ty, Ty::Borrow(..))
    {
        diagnostics.errors.push((
            TypeError::ParamModeBorrowConflict {
                mode: mode.keyword().to_string(),
                annotation: ty.render_mono(),
            },
            param.id,
        ));
        return ty;
    }
    let perm = match param.mode {
        None | Some(ParamMode::Consume | ParamMode::ConsumeMut) => return ty,
        Some(ParamMode::Borrow) => Perm::Shared,
        Some(ParamMode::Mut) => Perm::Exclusive,
    };
    if perm == Perm::Shared && copy_grade_head(catalog, &ty) {
        return ty;
    }
    match ty {
        Ty::Borrow(..) => ty,
        ty => Ty::Borrow(perm, Box::new(ty)),
    }
}

/// A nominal application whose grade is `Copy` (borrows of it erase).
pub(super) fn copy_grade_head(catalog: &TypeCatalog, ty: &Ty) -> bool {
    matches!(ty, Ty::Nominal(symbol, args)
        if catalog.grade_of_application(*symbol, args) == crate::types::catalog::Grade::Copy)
}

pub(super) struct Elaborator<'e> {
    store: &'e mut VarStore,
    catalog: &'e TypeCatalog,
    schemes: &'e FxHashMap<Symbol, Scheme>,
    diagnostics: &'e mut DiagnosticSink,
    type_aliases: &'e FxHashMap<Symbol, TypeAliasDef>,
    alias_stack: &'e mut Vec<Symbol>,
    self_types: &'e [Ty],
    resolved: &'e ResolvedNames,
    level: Level,
    pub(super) obligations: Vec<Constraint>,
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
        member_generics: &[GenericArg],
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
        member_generics: &[GenericArg],
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
            Symbol::TypeParameter(_) => {
                if !member_generics.is_empty() {
                    self.diagnostics.errors.push((
                        TypeError::ArityMismatch {
                            expected: 0,
                            found: member_generics.len(),
                        },
                        node,
                    ));
                }
                nominal_params(self.catalog, owner)
                    .iter()
                    .position(|param| param.symbol == child)
                    .and_then(|index| args.get(index).cloned())
                    .unwrap_or(Ty::Error)
            }
            Symbol::Struct(_) | Symbol::Enum(_) | Symbol::Protocol(_) | Symbol::Builtin(_) => {
                let lowered_args = self.lower_generic_args(child, member_generics);
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
            if let Some((owner, assoc)) = self.catalog.associated_type_in_ref(&protocol, label) {
                // Inside the owning protocol's own context, `Self.A` is
                // the assoc param itself, not a projection to reduce.
                if base == Ty::Param(owner.protocol) {
                    return Ty::Param(assoc);
                }
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

    fn lower_effect_set(&mut self, effects: &EffectSet, node: NodeID) -> EffectRow {
        let entries = effects
            .names
            .iter()
            .filter_map(|name| name.symbol().ok())
            .map(EffectEntry::label)
            .collect();
        let tail = if effects.is_open {
            Some(EffTail::Var(self.store.fresh_eff(self.level, node)))
        } else {
            None
        };
        EffectRow::new(entries, tail)
    }

    /// Lower a name applied to generic arguments. Shared by ordinary
    /// nominal annotations and extension heads (`TypeApplication`), so
    /// concrete head arguments get argument kinds, static values, defaults,
    /// aliases, and well-formedness exactly like every other application.
    fn lower_nominal_application(
        &mut self,
        name: &Name,
        generics: &[GenericArg],
        node: NodeID,
    ) -> Ty {
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
                    node,
                ));
            }
            return self.lower_type_alias(symbol, node, None);
        }
        let mut args: Vec<Ty> = self.lower_generic_args(symbol, generics);
        self.pad_default_args(symbol, &mut args, node);
        match symbol {
            Symbol::TypeParameter(_) | Symbol::AssociatedType(_) => {
                // A static parameter is a value, not a type; only
                // generic-argument slots (ADR 0035) may name it.
                if self.catalog.static_params.contains_key(&symbol) {
                    self.diagnostics
                        .errors
                        .push((TypeError::StaticValueInTypePosition, node));
                    return Ty::Error;
                }
                Ty::Param(symbol)
            }
            _ => {
                self.require_nominal_well_formed(symbol, &args, node);
                // Implicit effect args: annotations never spell
                // them, so `Wrapper` means "Wrapper with SOME
                // rows" — fresh here, pinned by whatever this
                // annotation meets (a declared return type's rows
                // are solved by the body and generalize with the
                // scheme). Collection-time leftovers sanitize to
                // owner-keyed params at the module boundary.
                if let Some(info) = self.catalog.structs.get(&symbol) {
                    args.extend(info.eff_params.iter().map(|_| {
                        Ty::Eff(EffectRow::open(self.store.fresh_eff(self.level, node)))
                    }));
                }
                Ty::Nominal(symbol, args)
            }
        }
    }

    fn lower_type_application(&mut self, head: &TypeApplication) -> Ty {
        self.lower_nominal_application(&head.name, &head.args, head.id)
    }

    fn lower_annotation(&mut self, annotation: &TypeAnnotation) -> Ty {
        match &annotation.kind {
            TypeAnnotationKind::Borrow { mutable, inner } => {
                let inner = self.lower_annotation(inner);
                // `&Int` never surfaces (ADR 0014): a shared borrow of a
                // Copy-grade head lowers to the bare type.
                if !*mutable && copy_grade_head(self.catalog, &inner) {
                    return inner;
                }
                let kind = if *mutable {
                    Perm::Exclusive
                } else {
                    Perm::Shared
                };
                Ty::Borrow(kind, Box::new(inner))
            }
            TypeAnnotationKind::Unique { inner } => {
                Ty::Unique(Box::new(self.lower_annotation(inner)))
            }
            TypeAnnotationKind::Nominal { name, generics, .. } => {
                self.lower_nominal_application(name, generics, annotation.id)
            }
            TypeAnnotationKind::Func {
                params,
                effects,
                returns,
            } => {
                let params = params.iter().map(|p| self.lower_annotation(p)).collect();
                let ret = self.lower_annotation(returns);
                let eff = self.lower_effect_set(effects, annotation.id);
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

    /// Lower a nominal application's generic arguments, interpreting each
    /// slot according to its declared parameter (ADR 0035 §1): a slot
    /// declared `static` takes a static value expression; every other
    /// slot takes a type.
    fn lower_generic_args(&mut self, head: Symbol, generics: &[GenericArg]) -> Vec<Ty> {
        let params = nominal_params(self.catalog, head);
        generics
            .iter()
            .enumerate()
            .map(|(index, generic)| {
                let expected = params.get(index).and_then(|param| match &param.kind {
                    crate::types::ty::ParamKind::Static(value_ty) => Some(value_ty.clone()),
                    crate::types::ty::ParamKind::Type => None,
                });
                match expected {
                    Some(expected) => {
                        let arg = self.lower_static_argument(generic, &expected);
                        self.emit_static_nonneg(&expected, &arg, generic.id());
                        arg
                    }
                    None => match generic {
                        GenericArg::Type(annotation) => self.lower_annotation(annotation),
                        GenericArg::Static(expr) => {
                            self.diagnostics
                                .errors
                                .push((TypeError::StaticValueInTypePosition, expr.id));
                            Ty::Error
                        }
                    },
                }
            })
            .collect()
    }

    /// Fill omitted trailing generic arguments from declared defaults,
    /// substituting earlier arguments left-to-right — the nominal twin of
    /// the protocol-application defaulting in `lower_protocol_ref_with_self`.
    /// A slot without a default keeps today's under-applied behavior (the
    /// mismatch surfaces at unification).
    fn pad_default_args(&mut self, head: Symbol, args: &mut Vec<Ty>, node: NodeID) {
        let params = nominal_params(self.catalog, head);
        if args.len() >= params.len() {
            return;
        }
        let mut substitution: FxHashMap<Symbol, Ty> = params
            .iter()
            .map(|param| param.symbol)
            .zip(args.iter().cloned())
            .collect();
        for index in args.len()..params.len() {
            let Some(default) = params[index].default.clone() else {
                return;
            };
            let default =
                default.substitute(&substitution, &Default::default(), &Default::default());
            // A materialized default is a formed static argument like any
            // explicit one (ADR 0035 §2): it owes the same nonnegativity
            // obligation, so `Pair<static A, static B = A - 1>` demands a
            // context proving `0 <= A - 1`.
            if let crate::types::ty::ParamKind::Static(expected) = &params[index].kind {
                self.emit_static_nonneg(expected, &default, node);
            }
            substitution.insert(params[index].symbol, default.clone());
            args.push(default);
        }
    }

    /// ADR 0035 §2: forming an application emits a nonnegativity wanted
    /// for every integer static argument.
    pub(super) fn emit_static_nonneg(&mut self, expected: &Ty, arg: &Ty, node: NodeID) {
        if matches!(expected, Ty::Nominal(symbol, _) if *symbol == Symbol::Int)
            && !matches!(arg, Ty::Error)
        {
            self.obligations.push(Constraint::StaticCmp {
                op: crate::types::ty::StaticCmpOp::Le,
                lhs: Ty::Static(StaticValue::Int(StaticInt::constant(0))),
                rhs: arg.clone(),
                origin: CtOrigin::new(node, CtReason::Annotation),
            });
        }
    }

    /// Lower a static generic argument (ADR 0035 §3): a static
    /// expression, or a name-like annotation reinterpreted against the
    /// declared parameter (a bare static-param reference or a fieldless
    /// enum case path).
    pub(super) fn lower_static_argument(&mut self, arg: &GenericArg, expected: &Ty) -> Ty {
        match arg {
            GenericArg::Static(expr) => self.lower_static_expr(expr, expected),
            GenericArg::Type(annotation) => self.lower_static_path(annotation, expected),
        }
    }

    /// The static index language proper: literals, grouping, `+`, `-`,
    /// and multiplication by a literal, normalized to canonical affine
    /// form.
    pub(super) fn lower_static_expr(&mut self, expr: &StaticExpr, expected: &Ty) -> Ty {
        let expected_head = match expected {
            Ty::Nominal(symbol, _) => *symbol,
            _ => return Ty::Error,
        };
        let mismatch = |this: &mut Self, found: &str| {
            this.diagnostics.errors.push((
                TypeError::Mismatch {
                    expected: expected.render_mono(),
                    found: found.to_string(),
                    reason: CtReason::Annotation,
                },
                expr.id,
            ));
            Ty::Error
        };
        match &expr.kind {
            StaticExprKind::Int(literal) => {
                if expected_head != Symbol::Int {
                    return mismatch(self, "Int");
                }
                match literal.parse::<i64>() {
                    Ok(value) => Ty::Static(StaticValue::Int(StaticInt::constant(value))),
                    Err(_) => {
                        self.diagnostics.errors.push((
                            TypeError::IntegerLiteralOutOfRange {
                                literal: literal.clone(),
                            },
                            expr.id,
                        ));
                        Ty::Error
                    }
                }
            }
            StaticExprKind::Bool(value) => {
                if expected_head != Symbol::Bool {
                    return mismatch(self, "Bool");
                }
                Ty::Static(StaticValue::Bool(*value))
            }
            StaticExprKind::Group(inner) => self.lower_static_expr(inner, expected),
            StaticExprKind::Path(annotation) => self.lower_static_path(annotation, expected),
            StaticExprKind::Op { op, lhs, rhs } => {
                if expected_head != Symbol::Int {
                    return mismatch(self, "Int");
                }
                let lhs = self.lower_static_expr(lhs, expected);
                let rhs = self.lower_static_expr(rhs, expected);
                let (Some(lhs), Some(rhs)) = (StaticInt::from_ty(&lhs), StaticInt::from_ty(&rhs))
                else {
                    // A poisoned or non-index operand already reported.
                    return Ty::Error;
                };
                let combined = match op {
                    StaticOpKind::Add => lhs.add(&rhs),
                    StaticOpKind::Sub => lhs.sub(&rhs),
                    StaticOpKind::Mul => match (lhs.as_constant(), rhs.as_constant()) {
                        (Some(factor), _) => rhs.scale(&factor.clone()),
                        (_, Some(factor)) => lhs.scale(&factor.clone()),
                        (None, None) => {
                            self.diagnostics
                                .errors
                                .push((TypeError::NonlinearStaticExpression, expr.id));
                            return Ty::Error;
                        }
                    },
                };
                // Normalization is over the mathematical integers; a
                // CLOSED result must fit Talk's signed 64-bit Int
                // (ADR 0035 §3) the moment it is formed.
                match combined.as_constant() {
                    Some(constant) if i64::try_from(constant.clone()).is_err() => {
                        self.diagnostics.errors.push((
                            TypeError::IntegerLiteralOutOfRange {
                                literal: constant.to_string(),
                            },
                            expr.id,
                        ));
                        Ty::Error
                    }
                    _ => combined.into_ty(),
                }
            }
        }
    }

    /// A name-like static operand: a bare reference to a declared static
    /// parameter, or a fieldless enum case path (`Color.red`).
    fn lower_static_path(&mut self, annotation: &TypeAnnotation, expected: &Ty) -> Ty {
        let expected_head = match expected {
            Ty::Nominal(symbol, _) => *symbol,
            _ => return Ty::Error,
        };
        match &annotation.kind {
            // A parenthesized name parses as the 1-tuple spelling.
            TypeAnnotationKind::Tuple(items) if items.len() == 1 => {
                self.lower_static_path(&items[0], expected)
            }
            TypeAnnotationKind::Nominal { name, generics, .. } if generics.is_empty() => {
                let Ok(symbol) = name.symbol() else {
                    return Ty::Error;
                };
                match self.catalog.static_params.get(&symbol) {
                    Some(declared) if declared == expected => Ty::Param(symbol),
                    Some(declared) => {
                        let declared = declared.render_mono();
                        self.diagnostics.errors.push((
                            TypeError::Mismatch {
                                expected: expected.render_mono(),
                                found: declared,
                                reason: CtReason::Annotation,
                            },
                            annotation.id,
                        ));
                        Ty::Error
                    }
                    None => {
                        let found = self.lower_annotation(annotation);
                        self.diagnostics.errors.push((
                            TypeError::ExpectedStaticArgument {
                                found: found.render_mono(),
                            },
                            annotation.id,
                        ));
                        Ty::Error
                    }
                }
            }
            // A fieldless enum case, spelled `Color.red`.
            TypeAnnotationKind::NominalPath {
                base,
                member,
                member_generics,
                ..
            } if member_generics.is_empty() => {
                let case = match &base.kind {
                    TypeAnnotationKind::Nominal { name, generics, .. } if generics.is_empty() => {
                        name.symbol().ok().filter(|owner| *owner == expected_head)
                    }
                    _ => None,
                }
                .and_then(|owner| {
                    self.catalog
                        .enums
                        .get(&owner)
                        .and_then(|info| info.variants.get(&member.to_string()))
                        .map(|variant| (owner, variant.symbol))
                });
                match case {
                    Some((owner, case)) => Ty::Static(StaticValue::Case(owner, case)),
                    None => {
                        let found = self.lower_annotation(annotation);
                        self.diagnostics.errors.push((
                            TypeError::ExpectedStaticArgument {
                                found: found.render_mono(),
                            },
                            annotation.id,
                        ));
                        Ty::Error
                    }
                }
            }
            _ => {
                let found = self.lower_annotation(annotation);
                self.diagnostics.errors.push((
                    TypeError::ExpectedStaticArgument {
                        found: found.render_mono(),
                    },
                    annotation.id,
                ));
                Ty::Error
            }
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

        let Some(protocol_info) = self.catalog.protocols.get(&protocol) else {
            self.diagnostics.errors.push((
                TypeError::InvalidExistentialProtocol {
                    ty: Ty::Nominal(protocol, args).render_mono(),
                },
                node,
            ));
            return Ty::Error;
        };
        if args.len() != protocol_info.params.len() {
            self.diagnostics.errors.push((
                TypeError::ArityMismatch {
                    expected: protocol_info.params.len(),
                    found: args.len(),
                },
                node,
            ));
            return Ty::Error;
        }

        let protocol_ref = ProtocolRef {
            protocol,
            args: args.clone(),
        };
        let required: Vec<(String, Symbol)> = self
            .catalog
            .associated_types_in_ref(&protocol_ref)
            .into_iter()
            .map(|(name, _, assoc)| (name, assoc))
            .collect();
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

        self.validate_object_safe_existential(&protocol_ref, node);

        assoc.sort_by_key(|(symbol, _)| *symbol);
        Ty::Any {
            protocol: protocol_ref,
            assoc,
        }
    }

    fn validate_object_safe_existential(&mut self, protocol: &ProtocolRef, node: NodeID) {
        let mut queue = vec![protocol.clone()];
        let mut seen = FxHashSet::default();
        while let Some(current) = queue.pop() {
            if !seen.insert(current.clone()) {
                continue;
            }
            let Some(info) = self.catalog.protocols.get(&current.protocol) else {
                continue;
            };
            let assoc_symbols: FxHashSet<Symbol> = self
                .catalog
                .associated_types_in_ref(&current)
                .into_iter()
                .map(|(_, _, symbol)| symbol)
                .collect();
            let supers: Vec<ProtocolRef> = self
                .catalog
                .protocol_and_supers(&current)
                .into_iter()
                .skip(1)
                .collect();
            let requirements: Vec<(String, Ty, Vec<Predicate>)> = info
                .requirements
                .iter()
                .filter_map(|(label, requirement)| {
                    let scheme = self.schemes.get(&requirement.symbol)?;
                    Some((label.clone(), scheme.ty.clone(), scheme.predicates.clone()))
                })
                .collect();
            for (label, sig, predicates) in requirements {
                self.validate_object_safe_requirement(
                    (protocol.protocol, current.protocol),
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
        protocols: (Symbol, Symbol),
        assoc_symbols: &FxHashSet<Symbol>,
        label: &str,
        sig: &Ty,
        predicates: &[Predicate],
        node: NodeID,
    ) {
        let (existential_protocol, requirement_protocol) = protocols;
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

/// A declaration's canonical checking context: its parameter records
/// and given predicates, computed once by `in_declaration_context`.
pub(super) struct DeclContext {
    pub(super) params: Vec<SchemeParam>,
    pub(super) predicates: Vec<Predicate>,
}

impl<'s, 'a> CatalogBuilder<'s, 'a> {
    pub(super) fn elaborator(&mut self) -> Elaborator<'_> {
        Elaborator {
            store: &mut *self.store,
            catalog: &*self.catalog,
            schemes: &*self.schemes,
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
        self.absorb_obligations(obligations);
        ty
    }

    pub(super) fn lower_type_application(&mut self, head: &TypeApplication) -> Ty {
        let (ty, obligations) = {
            let mut elab = self.elaborator();
            let ty = elab.lower_type_application(head);
            (ty, std::mem::take(&mut elab.obligations))
        };
        self.absorb_obligations(obligations);
        ty
    }

    pub(super) fn lower_type_alias(
        &mut self,
        symbol: Symbol,
        node: NodeID,
        owner_args: Option<(Symbol, Vec<Ty>)>,
    ) -> Ty {
        let (ty, obligations) = {
            let mut elab = self.elaborator();
            let ty = elab.lower_type_alias(symbol, node, owner_args);
            (ty, std::mem::take(&mut elab.obligations))
        };
        self.absorb_obligations(obligations);
        ty
    }

    /// Static formation obligations (ADR 0035 §2) have no later
    /// checkpoint — queue them for the first checking solve, wrapped per
    /// declaration by `finish_declaration_obligations`. Well-formedness
    /// `Conforms` obligations keep their long-standing use-site checking
    /// (construction and member sites re-emit them); queueing those here
    /// would need per-path given contexts (protocol Self bounds,
    /// requirement scheme contexts) this seam does not carry.
    pub(super) fn absorb_obligations(&mut self, obligations: Vec<Constraint>) {
        self.obligations.extend(
            obligations
                .into_iter()
                .filter(|obligation| matches!(obligation, Constraint::StaticCmp { .. })),
        );
    }

    /// The declaration-context scope: the one owner of the sequence
    /// every declaration follows — register generic bounds, compute the
    /// declaration's given predicates, lower its annotations, and wrap
    /// the formation obligations that lowering produced under those
    /// givens. `self_ty` is pushed only around predicate lowering (a
    /// where clause may mention Self); sites that need Self visible for
    /// their whole body push it themselves. The body may extend
    /// `context.predicates` (protocol heads add Self bindings, protocol
    /// where clauses lower after associated types register) and the
    /// exit wrap honors the final set. Calls nest: an inner declaration
    /// (a requirement signature, an extension method) proves its
    /// obligations under its OWN where clause before the enclosing
    /// declaration's.
    pub(super) fn in_declaration_context<R>(
        &mut self,
        self_ty: Option<Ty>,
        generics: &[GenericDecl],
        where_clause: Option<&WhereClause>,
        body: impl FnOnce(&mut Self, &mut DeclContext) -> R,
    ) -> R {
        let start = self.obligations.len();
        self.register_generic_bounds(generics);
        self.register_where_bounds(where_clause);
        let params = self.declared_params(generics);
        if let Some(ty) = &self_ty {
            self.self_types.push(ty.clone());
        }
        let predicates = self.declared_predicates(generics, where_clause);
        if self_ty.is_some() {
            self.self_types.pop();
        }
        let mut context = DeclContext { params, predicates };
        let result = body(self, &mut context);
        self.finish_declaration_obligations(start, &context.predicates);
        result
    }

    /// Wrap the obligations a declaration's annotations produced (from
    /// `start` on) under the declaration's own predicates, so a
    /// conditional context (`where 0 < N`) proves them exactly as it
    /// would for a body.
    fn finish_declaration_obligations(&mut self, start: usize, givens: &[Predicate]) {
        if self.obligations.len() <= start || givens.is_empty() {
            return;
        }
        let wanteds = self.obligations.split_off(start);
        self.obligations
            .push(Constraint::Implic(Box::new(Implication {
                level: self.level,
                givens: givens.to_vec(),
                wanteds,
                local_params: vec![],
                touchable_level: None,
            })));
    }
}

macro_rules! impl_checking_elaboration_for {
    ($target:ident<$session:lifetime, $source:lifetime>) => {
        impl<$session, $source> $target<$session, $source> {
            pub(super) fn elaborator(&mut self) -> Elaborator<'_> {
                Elaborator {
                    store: &mut *self.store,
                    catalog: &*self.catalog,
                    schemes: &*self.schemes,
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

            /// Formation obligations from out-of-band elaboration (e.g.
            /// protocol static arguments) join this checker's wanteds.
            pub(super) fn absorb_obligations(&mut self, obligations: Vec<Constraint>) {
                self.wanteds.extend(obligations);
            }
        }
    };
}

impl_checking_elaboration_for!(BodyChecker<'s, 'a>);
impl_checking_elaboration_for!(BindingGroupChecker<'s, 'a>);

impl<'s, 'a> BodyChecker<'s, 'a> {
    /// Lower an explicit generic argument according to its declared
    /// parameter's kind (ADR 0035): a `static` slot takes a static value
    /// expression, any other slot a type.
    pub(super) fn lower_generic_arg_for_param(&mut self, param: Symbol, arg: &GenericArg) -> Ty {
        match (self.catalog.static_params.get(&param).cloned(), arg) {
            (Some(expected), arg) => {
                let (ty, obligations) = {
                    let mut elab = self.elaborator();
                    let ty = elab.lower_static_argument(arg, &expected);
                    elab.emit_static_nonneg(&expected, &ty, arg.id());
                    (ty, std::mem::take(&mut elab.obligations))
                };
                self.wanteds.extend(obligations);
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
