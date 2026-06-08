use indexmap::{IndexMap, IndexSet};
use itertools::Itertools;
use tracing::instrument;

use super::{InferencePass, TypedRet};
use crate::{
    label::Label,
    name::Name,
    name_resolution::symbol::Symbol,
    node_kinds::{
        block::Block,
        body::Body,
        decl::{Decl, DeclKind},
        expr::Expr,
        func::{EffectSet, Func},
        generic_decl::GenericDecl,
        parameter::Parameter,
        type_annotation::TypeAnnotation,
    },
    types::{
        call_site::CallerContext,
        constraints::constraint::ConstraintCause,
        infer_row::Row,
        infer_ty::Ty,
        scheme::ForAll,
        solve_context::SolveContext,
        type_catalog::Nominal,
        type_error::TypeError,
        type_operations::{curry, substitute},
        typed_ast::{TypedDecl, TypedDeclKind, TypedFunc},
    },
};

impl InferencePass<'_> {
    #[instrument(level = tracing::Level::TRACE, skip(self, decl, generics, conformances, body, context))]
    pub(super) fn visit_nominal(
        &mut self,
        decl: &Decl,
        name: &Name,
        generics: &[GenericDecl],
        conformances: &[TypeAnnotation],
        body: &Body,
        context: &mut SolveContext,
    ) -> TypedRet<TypedDecl> {
        let Ok(nominal_symbol) = name.symbol() else {
            return Err(TypeError::NameNotResolved(name.clone()));
        };

        let mut type_params = vec![];
        let is_extend = matches!(decl.kind, DeclKind::Extend { .. });
        for generic in generics.iter() {
            let sym = generic
                .name
                .symbol()
                .map_err(|_| TypeError::NameNotResolved(generic.name.clone()))?;

            // For extend blocks, a generic might resolve to a concrete type (e.g. Void)
            // rather than a type parameter declaration
            if is_extend && !matches!(sym, Symbol::TypeParameter(..)) {
                let ty = if matches!(sym, Symbol::Builtin(..)) {
                    Ty::Primitive(sym)
                } else {
                    Ty::Nominal {
                        symbol: sym,
                        type_args: vec![],
                    }
                };
                type_params.push(ty);
                self.session
                    .type_catalog
                    .child_types
                    .entry(nominal_symbol)
                    .or_default()
                    .insert(generic.name.name_str().into(), sym);
                continue;
            }

            let id = self.register_generic(generic, context);
            let bounds = match self.session.lookup(&sym) {
                Some(entry) => match entry._as_ty() {
                    Ty::Param(_, bounds) => bounds,
                    _ => vec![],
                },
                None => vec![],
            };
            type_params.push(Ty::Param(id, bounds));
            self.session
                .type_catalog
                .child_types
                .entry(nominal_symbol)
                .or_default()
                .insert(generic.name.name_str().into(), sym);
        }

        // For extend blocks without explicit generics, use the existing nominal's type params
        if matches!(decl.kind, DeclKind::Extend { .. })
            && type_params.is_empty()
            && let Some(nominal) = self.session.lookup_nominal(&nominal_symbol)
        {
            type_params = nominal.type_params.clone();
        }

        let ty = if matches!(nominal_symbol, Symbol::Builtin(..)) {
            Ty::Primitive(nominal_symbol)
        } else {
            Ty::Nominal {
                symbol: nominal_symbol,
                type_args: type_params.clone(),
            }
        };

        if !matches!(decl.kind, DeclKind::Extend { .. })
            && !self
                .session
                .type_catalog
                .nominals
                .contains_key(&nominal_symbol)
        {
            self.session
                .insert(nominal_symbol, ty.clone(), &mut self.constraints);
        }

        let mut row_types = vec![];
        let mut initializers = IndexMap::<Label, TypedFunc>::default();
        let mut instance_methods = IndexMap::<Label, TypedFunc>::default();
        let mut properties: IndexMap<Label, Ty> = IndexMap::default();
        let mut variants: IndexMap<Label, Vec<Ty>> = IndexMap::default();
        let mut typealiases: IndexMap<Label, Ty> = IndexMap::default();

        // Set current_self_ty for proper SelfType resolution in extensions
        let old_self_ty = self.current_self_ty.replace(ty.clone());

        for decl in body.decls.iter() {
            match &decl.kind {
                DeclKind::Init { name, params, body } => {
                    let func =
                        self.visit_init(decl, ty.clone(), name, params, body, &mut context.next())?;
                    initializers.insert("init".into(), func);
                    self.session
                        .type_catalog
                        .initializers
                        .entry(nominal_symbol)
                        .or_default()
                        .insert(
                            name.name_str().into(),
                            name.symbol()
                                .map_err(|_| TypeError::NameNotResolved(name.clone()))?,
                        );
                }
                DeclKind::Method { func, is_static } => {
                    let func_name = &func.name;
                    let func =
                        self.visit_method(nominal_symbol, func, *is_static, &mut context.next())?;
                    instance_methods.insert(func.name.to_string().into(), func);

                    self.session
                        .type_catalog
                        .instance_methods
                        .entry(nominal_symbol)
                        .or_default()
                        .insert(
                            func_name.name_str().into(),
                            func_name
                                .symbol()
                                .map_err(|_| TypeError::NameNotResolved(name.clone()))?,
                        );
                }
                DeclKind::EnumVariant(name @ Name::Resolved(sym, name_str), _, values) => {
                    self.session
                        .type_catalog
                        .variants
                        .entry(nominal_symbol)
                        .or_default()
                        .insert(name_str.into(), *sym);

                    let tys: Vec<_> = values
                        .iter()
                        .map(|v| self.visit_type_annotation(v, &mut context.next()))
                        .try_collect()?;

                    variants.insert(name.name_str().into(), tys.clone());

                    let values_ty = match tys.len() {
                        0 => Ty::Void,
                        1 => tys[0].clone(),
                        _ => Ty::Tuple(tys.to_vec()),
                    };
                    self.session
                        .insert(*sym, values_ty.clone(), &mut self.constraints);
                    row_types.push((name.name_str(), values_ty));
                    self.session
                        .type_catalog
                        .variants
                        .entry(nominal_symbol)
                        .or_default()
                        .insert(
                            name.name_str().into(),
                            name.symbol()
                                .map_err(|_| TypeError::NameNotResolved(name.clone()))?,
                        );
                }
                DeclKind::Property {
                    name,
                    is_static,
                    type_annotation,
                    default_value,
                    ..
                } => {
                    properties.insert(
                        name.name_str().into(),
                        self.visit_property(
                            decl,
                            nominal_symbol,
                            name,
                            *is_static,
                            type_annotation,
                            default_value,
                            context,
                        )?,
                    );
                }
                DeclKind::TypeAlias(lhs, .., rhs) => {
                    let rhs_ty = self.visit_type_annotation(rhs, context)?;

                    // Quantify over the enclosing nominal's generics so the alias can be
                    // instantiated at use sites (e.g., Person<A>.T = A => T specializes to A).
                    let mut foralls: IndexSet<ForAll> = IndexSet::new();
                    for g in generics {
                        if let Ok(sym) = g.name.symbol()
                            && let Some(entry) = self.session.lookup(&sym)
                            && let Ty::Param(pid, _) = entry._as_ty()
                        {
                            foralls.insert(ForAll::Ty(pid));
                        }
                    }

                    typealiases.insert(lhs.name_str().into(), rhs_ty.clone());

                    let Ok(lhs_sym) = lhs.symbol() else {
                        return Err(TypeError::NameNotResolved(lhs.clone()));
                    };

                    self.session
                        .type_catalog
                        .child_types
                        .entry(nominal_symbol)
                        .or_default()
                        .insert(lhs.name_str().into(), lhs_sym);

                    self.session.insert(lhs_sym, rhs_ty, &mut self.constraints);
                }
                DeclKind::Extend {
                    conformances: nested_conformances,
                    body: nested_body,
                    ..
                } => {
                    // Register conformances from the nested extend block
                    for conformance in nested_conformances {
                        let Ok(sym) = conformance.symbol() else {
                            continue;
                        };
                        let Symbol::Protocol(protocol_id) = sym else {
                            continue;
                        };

                        self.session
                            .declare_conformance(Self::conformance_claim_from_body(
                                nominal_symbol,
                                protocol_id,
                                conformance.id,
                                conformance.span,
                                nested_body,
                            ));

                        self.register_conformance(
                            nominal_symbol,
                            sym,
                            conformance.id,
                            conformance.span,
                            context,
                        )
                        .ok();

                        self.constraints.wants_conforms(
                            conformance.id,
                            ty.clone(),
                            protocol_id,
                            &context.group_info(),
                        );
                    }

                    // Process methods in the nested extend body
                    for nested_decl in &nested_body.decls {
                        if let DeclKind::Method { func, is_static } = &nested_decl.kind {
                            let func_name = &func.name;
                            let func = self.visit_method(
                                nominal_symbol,
                                func,
                                *is_static,
                                &mut context.next(),
                            )?;
                            instance_methods.insert(func.name.to_string().into(), func);

                            // Also register in the type catalog (like regular methods)
                            self.session
                                .type_catalog
                                .instance_methods
                                .entry(nominal_symbol)
                                .or_default()
                                .insert(
                                    func_name.name_str().into(),
                                    func_name
                                        .symbol()
                                        .map_err(|_| TypeError::NameNotResolved(name.clone()))?,
                                );
                        }
                    }
                }
                DeclKind::Struct { .. } | DeclKind::Enum { .. } | DeclKind::Protocol { .. } => {
                    // Nested nominal declarations must be fully typechecked so their
                    // constructors/methods are available from child-type access
                    // (for example `HTTP.Server()`).
                    self.visit_decl(decl, &mut context.next())?;
                }
                _ => tracing::warn!("Unhandled nominal decl: {:?}", decl.kind),
            }
        }

        for conformance in conformances {
            let Ok(sym) = conformance.symbol() else {
                tracing::error!("skipping {conformance:?} due to unresolved name");
                continue;
            };

            let Symbol::Protocol(protocol_id) = sym else {
                continue;
            };

            // self.register_conformance(
            //     &ty,
            //     nominal_symbol,
            //     sym,
            //     conformance.id,
            //     conformance.span,
            //     context,
            // )?;

            self.constraints.wants_conforms(
                conformance.id,
                ty.clone(),
                protocol_id,
                &context.group_info(),
            );
        }

        let kind = match &decl.kind {
            DeclKind::Struct { .. } => TypedDeclKind::StructDef {
                initializers,
                symbol: nominal_symbol,
                properties: properties.clone(),
                instance_methods,
                typealiases,
            },
            DeclKind::Enum { .. } => TypedDeclKind::EnumDef {
                symbol: nominal_symbol,
                variants: variants.clone(),
                instance_methods,
                typealiases,
            },
            DeclKind::Extend { .. } => TypedDeclKind::Extend {
                symbol: nominal_symbol,
                instance_methods,
                typealiases,
            },
            _ => unreachable!(),
        };

        if !matches!(decl.kind, DeclKind::Extend { .. }) {
            self.session.type_catalog.nominals.insert(
                nominal_symbol,
                Nominal {
                    properties,
                    variants,
                    type_params,
                },
            );

            if let Some((id, level)) = self.nominal_placeholders.remove(&nominal_symbol) {
                self.constraints.wants_equals_at(
                    decl.id,
                    ty.clone(),
                    Ty::Var { id, level },
                    &context.group_info(),
                );
            }
        }

        // Restore old_self_ty
        self.current_self_ty = old_self_ty;

        Ok(TypedDecl {
            id: decl.id,
            ty,
            kind,
        })
    }

    #[instrument(level = tracing::Level::TRACE, skip(self, context, func))]
    fn visit_method(
        &mut self,
        owner_symbol: Symbol,
        func: &Func,
        is_static: bool,
        context: &mut SolveContext,
    ) -> TypedRet<TypedFunc> {
        let Ok(func_sym) = func.name.symbol() else {
            return Err(TypeError::NameNotResolved(func.name.clone()));
        };

        if is_static {
            self.session
                .type_catalog
                .static_methods
                .entry(owner_symbol)
                .or_default()
                .insert(func.name.name_str().into(), func_sym);
        } else {
            self.session
                .type_catalog
                .instance_methods
                .entry(owner_symbol)
                .or_default()
                .insert(func.name.name_str().into(), func_sym);
        }

        let func_ty = self.visit_func(func, context)?;

        // For instance methods, ensure the self parameter is unified with the enclosing type.
        // This is critical for nested extend blocks where self needs to be the struct type.
        if !is_static
            && let Some(self_param) = func_ty.params.first()
            && let Some(self_ty) = &self.current_self_ty
        {
            self.constraints.wants_equals_at_with_cause(
                func.id,
                self_param.ty.clone(),
                self_ty.clone(),
                &context.group_info(),
                Some(ConstraintCause::Internal),
            );
        }

        self.session.insert(
            func_sym,
            curry(
                func_ty.params.iter().map(|p| p.ty.clone()),
                func_ty.ret.clone(),
                func_ty.effects_row.clone().into(),
            ),
            &mut self.constraints,
        );

        Ok(func_ty)
    }

    #[instrument(level = tracing::Level::TRACE, skip(self, context))]
    #[allow(clippy::too_many_arguments)]
    fn visit_property(
        &mut self,
        decl: &Decl,
        struct_symbol: Symbol,
        name: &Name,
        is_static: bool,
        type_annotation: &Option<TypeAnnotation>,
        default_value: &Option<Expr>,
        context: &mut SolveContext,
    ) -> TypedRet<Ty> {
        let Ok(sym) = name.symbol() else {
            return Err(TypeError::NameNotResolved(name.clone()));
        };

        self.session
            .type_catalog
            .properties
            .entry(struct_symbol)
            .or_default()
            .insert(name.name_str().into(), sym);

        let ty = if let Some(anno) = type_annotation {
            self.visit_type_annotation(anno, context)?
        } else {
            self.session.new_type_param(None)
        };

        if let Some(default_value) = default_value {
            let default_ty = self.visit_expr(default_value, context)?;
            self.constraints.wants_equals_at_with_cause(
                default_value.id,
                default_ty.ty.clone(),
                ty.clone(),
                &context.group_info(),
                Some(ConstraintCause::Annotation(default_value.id)),
            );
        }

        if is_static {
            self.session
                .type_catalog
                .static_methods
                .entry(struct_symbol)
                .or_default()
                .insert(name.name_str().into(), sym);
        } else {
            self.session
                .type_catalog
                .properties
                .entry(struct_symbol)
                .or_default()
                .insert(name.name_str().into(), sym);
        }

        Ok(ty)
    }

    #[instrument(level = tracing::Level::TRACE, skip(self, context, _decl))]
    fn visit_init(
        &mut self,
        _decl: &Decl,
        struct_ty: Ty,
        name: &Name,
        params: &[Parameter],
        body: &Block,
        context: &mut SolveContext,
    ) -> TypedRet<TypedFunc> {
        let Ok(sym) = name.symbol() else {
            return Err(TypeError::NameNotResolved(name.clone()));
        };

        // Handle self param directly with struct_ty - don't instantiate!
        let params = self.visit_params(params, context)?;

        let effects = self.tracking_effects(&EffectSet::default(), context)?;

        // Init blocks always return self
        let block = self.with_current_caller(CallerContext::Callable(sym), |this| {
            this.infer_block(body, context)
        })?;

        let ty = curry(
            params.iter().map(|p| p.ty.clone()),
            struct_ty.clone(),
            Row::Empty.into(),
        );

        let Ty::Nominal { symbol, .. } = &struct_ty else {
            unreachable!()
        };

        let effects_row = self
            .tracked_effect_rows
            .pop()
            .unwrap_or_else(|| unreachable!("we just pushed it pal"));

        self.session
            .type_catalog
            .initializers
            .entry(*symbol)
            .or_default()
            .insert(Label::Named("init".into()), sym);

        let foralls = ty.collect_foralls();
        let ty = substitute(&ty, &self.session.skolem_map);
        self.session.insert(sym, ty, &mut self.constraints);

        Ok(TypedFunc {
            name: sym,
            params,
            body: block,
            effects_row,
            foralls,
            effects,
            ret: struct_ty,
        })
    }
}
