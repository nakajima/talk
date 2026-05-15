use indexmap::{IndexMap, IndexSet, indexset};
use tracing::instrument;

use super::{InferencePass, ProtocolAssociatedTypeRequirements, TypedRet};
use crate::{
    diagnostic::{AnyDiagnostic, Diagnostic, Severity},
    label::Label,
    name::Name,
    name_resolution::symbol::{ProtocolId, Symbol},
    node_kinds::{
        body::Body,
        decl::{Decl, DeclKind},
        func_signature::FuncSignature,
        generic_decl::GenericDecl,
        type_annotation::TypeAnnotation,
    },
    types::{
        infer_row::Row,
        infer_ty::Ty,
        predicate::Predicate,
        scheme::{ForAll, Scheme},
        solve_context::SolveContext,
        term_environment::EnvEntry,
        type_error::TypeError,
        type_operations::curry,
        typed_ast::{TypedDecl, TypedDeclKind, TypedFunc},
    },
};

#[derive(Clone, Copy, Debug)]
struct ProtocolScope {
    symbol: Symbol,
    id: ProtocolId,
    self_param: Symbol,
}

impl ProtocolScope {
    fn self_ty(self) -> Ty {
        Ty::Param(self.self_param, vec![self.id])
    }

    fn self_conformance(self) -> Predicate {
        Predicate::Conforms {
            param: self.self_param,
            protocol_id: self.id,
        }
    }
}

impl InferencePass<'_> {
    fn visit_func_signature(
        &mut self,
        protocol_self_id: Symbol,
        protocol_id: ProtocolId,
        func_signature: &FuncSignature,
        context: &mut SolveContext,
    ) -> TypedRet<Ty> {
        for generic in func_signature.generics.iter() {
            self.register_generic(generic, context);
        }

        let mut effects_row = if func_signature.effects.is_open {
            self.session.new_row_type_param(None)
        } else {
            Row::Empty
        };
        for effect in func_signature.effects.names.iter() {
            let Ok(symbol) = effect.symbol() else {
                return Err(TypeError::NameNotResolved(effect.clone()));
            };

            let Some(effect) = self.session.lookup_effect(&symbol) else {
                return Err(TypeError::EffectNotFound(effect.name_str()));
            };

            effects_row = Row::Extend {
                row: effects_row.into(),
                label: Label::_Symbol(symbol),
                ty: effect.clone(),
            };
        }

        let params = self.visit_params(&func_signature.params, context)?;
        _ = self.tracking_effects(&func_signature.effects, context)?;
        let effects_row = self
            .tracked_effect_rows
            .pop()
            .unwrap_or_else(|| unreachable!("we just pushed it pal"));

        let ret = if let Some(ret) = &func_signature.ret {
            self.visit_type_annotation(ret, context)?
        } else {
            Ty::Void
        };

        let ty = curry(params.iter().map(|p| p.ty.clone()), ret, effects_row.into());
        let mut foralls: IndexSet<_> = ty.collect_foralls().into_iter().collect();
        foralls.insert(ForAll::Ty(protocol_self_id));
        let predicates = vec![Predicate::Conforms {
            param: protocol_self_id,
            protocol_id,
        }];

        self.session.insert_term(
            func_signature
                .name
                .symbol()
                .unwrap_or_else(|_| unreachable!()),
            EnvEntry::Scheme(Scheme {
                ty: ty.clone(),
                foralls,
                predicates,
            }),
            &mut self.constraints,
        );

        self.session
            .type_catalog
            .method_requirements
            .entry(protocol_id.into())
            .or_default()
            .insert(
                func_signature.name.name_str().into(),
                func_signature.name.symbol().map_err(|_| {
                    TypeError::NameNotResolved(Name::Raw(format!("{protocol_id}")).clone())
                })?,
            );

        Ok(ty)
    }

    fn visit_associated_type(
        &mut self,
        generic: &GenericDecl,
        protocol_self_id: Symbol,
        protocol_symbol: Symbol,
        context: &mut SolveContext,
    ) -> TypedRet<Ty> {
        let Symbol::Protocol(protocol_id) = protocol_symbol else {
            unreachable!()
        };

        let ret_id = self.session.new_type_param_id(None);

        // Collect bounds from conformances for the associated type
        let mut bounds = vec![];
        let mut conformance_predicates = vec![];
        for conformance in generic.conformances.iter() {
            let Ok(Symbol::Protocol(conforms_to_id)) = conformance.symbol() else {
                tracing::warn!("could not determine associated type conformance: {conformance:?}");
                continue;
            };

            bounds.push(conforms_to_id);

            let predicate = Predicate::Conforms {
                param: ret_id,
                protocol_id: conforms_to_id,
            };

            conformance_predicates.push(predicate.clone());

            // Add to context givens so member resolution works within protocol methods
            context.givens_mut().insert(predicate.clone());
        }

        let ret = Ty::Param(ret_id, bounds.clone());

        let mut predicates = vec![Predicate::Projection {
            base: Ty::Param(protocol_self_id, vec![protocol_id]),
            label: generic.name.name_str().into(),
            protocol_id: Some(protocol_id),
            returns: ret.clone(),
        }];

        predicates.extend(conformance_predicates);

        let scheme = Scheme {
            ty: ret.clone(),
            foralls: indexset! { ForAll::Ty(protocol_self_id), ForAll::Ty(ret_id) },
            predicates,
        };

        let Ok(generic_sym) = generic.name.symbol() else {
            self.diagnostics.insert(AnyDiagnostic::Typing(Diagnostic {
                id: generic.id,
                severity: Severity::Error,
                kind: TypeError::NameNotResolved(generic.name.clone()),
            }));
            return Err(TypeError::NameNotResolved(generic.name.clone()));
        };

        self.session
            .insert_term(generic_sym, EnvEntry::Scheme(scheme), &mut self.constraints);
        self.session
            .type_catalog
            .associated_types
            .entry(protocol_symbol)
            .or_default()
            .insert(generic.name.name_str().into(), generic_sym);

        Ok(ret)
    }

    fn collect_assoc_requirements(
        &mut self,
        body: &Body,
        protocol: ProtocolScope,
        context: &mut SolveContext,
    ) -> (IndexMap<Label, Ty>, ProtocolAssociatedTypeRequirements) {
        let mut associated_types: IndexMap<Label, Ty> = IndexMap::default();
        let mut assoc_type_params: IndexSet<Symbol> = IndexSet::default();
        let mut assoc_type_predicates: IndexSet<Predicate> = IndexSet::default();

        for decl in &body.decls {
            if let DeclKind::Associated { generic } = &decl.kind
                && let Ok(ty) = self.visit_associated_type(
                    generic,
                    protocol.self_param,
                    protocol.symbol,
                    context,
                )
            {
                let label: Label = generic.name.name_str().into();
                let assoc_param_id = match &ty {
                    Ty::Param(param_id, _) => {
                        assoc_type_params.insert(*param_id);
                        Some(*param_id)
                    }
                    _ => None,
                };

                associated_types.insert(label.clone(), ty.clone());

                if assoc_param_id.is_some() {
                    // Use ty.clone() here instead of creating a new Param with empty bounds,
                    // because ty already has the correct protocol bounds from visit_associated_type
                    assoc_type_predicates.insert(Predicate::Projection {
                        base: protocol.self_ty(),
                        label: label.clone(),
                        returns: ty.clone(),
                        protocol_id: Some(protocol.id),
                    });
                }

                // Collect any conformance predicates for this associated type
                for conformance in generic.conformances.iter() {
                    if let Ok(Symbol::Protocol(conforms_to_id)) = conformance.symbol() {
                        let assoc_param = assoc_param_id.or_else(|| {
                            let Ok(generic_sym) = generic.name.symbol() else {
                                return None;
                            };
                            let entry = self.session.lookup(&generic_sym)?;
                            entry.foralls().iter().find_map(|fa| {
                                if let ForAll::Ty(param_id) = fa
                                    && *param_id != protocol.self_param
                                {
                                    Some(*param_id)
                                } else {
                                    None
                                }
                            })
                        });

                        // Get the type param ID for this associated type
                        if let Some(assoc_param) = assoc_param {
                            assoc_type_predicates.insert(Predicate::Conforms {
                                param: assoc_param,
                                protocol_id: conforms_to_id,
                            });
                        }
                    }
                }
            }
        }

        let requirements = ProtocolAssociatedTypeRequirements {
            assoc_params: assoc_type_params,
            predicates: assoc_type_predicates,
        };
        if !requirements.is_empty() {
            tracing::debug!(
                "Inserting protocol_associated_type_requirements for {:?}: {:?}",
                protocol.id,
                requirements
            );
            self.protocol_associated_type_requirements
                .insert(protocol.id, requirements.clone());
        }

        (associated_types, requirements)
    }

    fn register_superprotocols(
        &mut self,
        protocol: ProtocolScope,
        conformances: &[TypeAnnotation],
        context: &mut SolveContext,
    ) {
        for conformance in conformances {
            let Ok(Symbol::Protocol(conforms_to_id)) = conformance.symbol() else {
                tracing::error!("did not get protocol for conforms_to");
                continue;
            };

            self.register_conformance(
                protocol.symbol,
                conforms_to_id.into(),
                conformance.id,
                conformance.span,
                context,
            )
            .ok();

            let inherited_methods = self.session.lookup_instance_methods(&conforms_to_id.into());
            if !inherited_methods.is_empty() {
                self.session
                    .type_catalog
                    .instance_methods
                    .entry(protocol.symbol)
                    .or_default()
                    .extend(inherited_methods);
            }
        }
    }

    fn collect_method_requirements(
        &mut self,
        body: &Body,
        protocol: ProtocolScope,
        associated_type_requirements: &ProtocolAssociatedTypeRequirements,
        context: &mut SolveContext,
        binders: &mut IndexMap<Symbol, Ty>,
    ) -> TypedRet<IndexMap<Label, Ty>> {
        let mut requirements = IndexMap::default();

        for decl in &body.decls {
            let (DeclKind::MethodRequirement(func_signature)
            | DeclKind::FuncSignature(func_signature)) = &decl.kind
            else {
                continue;
            };

            let ty = self.visit_func_signature(
                protocol.self_param,
                protocol.id,
                func_signature,
                context,
            )?;
            let func_sym = func_signature
                .name
                .symbol()
                .map_err(|_| TypeError::NameNotResolved(func_signature.name.clone()))?;
            if let Some(entry) = self.session.lookup(&func_sym) {
                let entry = self.apply_protocol_associated_type_requirements(
                    entry,
                    associated_type_requirements,
                );
                self.session.promote(func_sym, entry, &mut self.constraints);
            }
            binders.insert(func_sym, ty.clone());
            requirements.insert(func_signature.name.name_str().into(), ty);
        }

        Ok(requirements)
    }

    fn infer_default_methods(
        &mut self,
        body: &Body,
        protocol: ProtocolScope,
        associated_type_requirements: &ProtocolAssociatedTypeRequirements,
        context: &mut SolveContext,
        binders: &mut IndexMap<Symbol, Ty>,
    ) -> TypedRet<IndexMap<Label, TypedFunc>> {
        let mut methods = IndexMap::default();

        for decl in &body.decls {
            match &decl.kind {
                DeclKind::Method {
                    func,
                    is_static: false,
                } => {
                    let func_sym = func
                        .name
                        .symbol()
                        .map_err(|_| TypeError::NameNotResolved(func.name.clone()))?;

                    self.session
                        .type_catalog
                        .instance_methods
                        .entry(protocol.symbol)
                        .or_default()
                        .insert(func.name.name_str().into(), func_sym);

                    let typed_func = self.visit_func(func, context)?;
                    let func_ty = curry(
                        typed_func.params.iter().map(|p| p.ty.clone()),
                        typed_func.ret.clone(),
                        typed_func.effects_row.clone().into(),
                    );

                    let entry = EnvEntry::Scheme(Scheme {
                        foralls: func_ty.collect_foralls(),
                        predicates: vec![protocol.self_conformance()],
                        ty: func_ty.clone(),
                    });
                    let entry = self.apply_protocol_associated_type_requirements(
                        entry,
                        associated_type_requirements,
                    );

                    self.session.promote(func_sym, entry, &mut self.constraints);

                    methods.insert(func.name.name_str().into(), typed_func.clone());
                    binders.insert(func_sym, func_ty);
                }
                DeclKind::Associated { .. }
                | DeclKind::MethodRequirement(_)
                | DeclKind::FuncSignature(_) => {}
                _ => {
                    tracing::error!("unhandled decl: {decl:?}");
                    continue;
                }
            }
        }

        Ok(methods)
    }

    #[instrument(level = tracing::Level::TRACE, skip(self, decl, _generics, conformances, body, context))]
    pub(super) fn visit_protocol(
        &mut self,
        decl: &Decl,
        name: &Name,
        _generics: &[GenericDecl],
        conformances: &[TypeAnnotation],
        body: &Body,
        context: &mut SolveContext,
    ) -> TypedRet<(TypedDecl, IndexMap<Symbol, Ty>)> {
        let Ok(protocol_symbol @ Symbol::Protocol(protocol_id)) = name.symbol() else {
            return Err(TypeError::NameNotResolved(name.clone()));
        };

        let Some(Ty::Param(protocol_self_id, _)) =
            self.session.lookup(&protocol_symbol).map(|s| s._as_ty())
        else {
            return Err(TypeError::TypeNotFound(
                "Didn't get self id for {protocol_symbol:?}".into(),
            ));
        };

        let protocol = ProtocolScope {
            symbol: protocol_symbol,
            id: protocol_id,
            self_param: protocol_self_id,
        };
        let mut binders: IndexMap<Symbol, Ty> = IndexMap::default();

        self.register_superprotocols(protocol, conformances, context);

        context.givens_mut().insert(protocol.self_conformance());

        self.session
            .insert(protocol.symbol, protocol.self_ty(), &mut self.constraints);

        let (associated_types, protocol_associated_type_requirements) =
            self.collect_assoc_requirements(body, protocol, context);
        let instance_method_requirements = self.collect_method_requirements(
            body,
            protocol,
            &protocol_associated_type_requirements,
            context,
            &mut binders,
        )?;
        let instance_methods = self.infer_default_methods(
            body,
            protocol,
            &protocol_associated_type_requirements,
            context,
            &mut binders,
        )?;

        if let Some(child_types) = self
            .session
            .resolved_names
            .child_types
            .get(&protocol_symbol)
        {
            self.session
                .type_catalog
                .associated_types
                .entry(protocol_symbol)
                .or_default()
                .extend(child_types.clone());
        }

        Ok((
            TypedDecl {
                id: decl.id,
                ty: self
                    .session
                    .lookup(&protocol_symbol)
                    .unwrap_or_else(|| unreachable!("did not find ty for {protocol_symbol:?}"))
                    ._as_ty(),
                kind: TypedDeclKind::ProtocolDef {
                    symbol: protocol_symbol,
                    instance_methods,
                    instance_method_requirements,
                    typealiases: Default::default(),
                    associated_types,
                },
            },
            binders,
        ))
    }
}
