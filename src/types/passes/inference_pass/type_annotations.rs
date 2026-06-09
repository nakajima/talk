use itertools::Itertools;
use tracing::instrument;

use super::{InferencePass, TypedRet};
use crate::{
    diagnostic::{AnyDiagnostic, Diagnostic, Severity},
    name_resolution::symbol::Symbol,
    node_kinds::{
        generic_decl::GenericDecl,
        parameter::Parameter,
        type_annotation::{TypeAnnotation, TypeAnnotationKind},
    },
    types::{
        builtins::resolve_builtin_type,
        constraints::constraint::ConstraintCause,
        infer_row::Row,
        infer_ty::Ty,
        predicate::Predicate,
        scheme::ForAll,
        solve_context::{SolveContext, SolveContextKind},
        type_error::TypeError,
        type_operations::curry,
        typed_ast::TypedParameter,
    },
};

impl InferencePass<'_> {
    pub(super) fn visit_params(
        &mut self,
        params: &[Parameter],
        context: &mut SolveContext,
    ) -> TypedRet<Vec<TypedParameter>> {
        params
            .iter()
            .map(|param| self.visit_param(param, context))
            .try_collect()
    }

    fn visit_param(
        &mut self,
        param: &Parameter,
        context: &mut SolveContext,
    ) -> TypedRet<TypedParameter> {
        let Ok(sym) = param.name.symbol() else {
            return Err(TypeError::NameNotResolved(param.name.clone()));
        };

        // If there's an existing entry (e.g., from capture placeholder), get its type
        // so we can unify with it if we have a type annotation
        let existing_ty = self.session.lookup(&sym).map(|e| e._as_ty());

        let ty = if let Some(type_annotation) = &param.type_annotation {
            let annotation_ty = self.visit_type_annotation(type_annotation, context)?;
            // If there was a placeholder, unify it with the annotated type
            if let Some(existing) = existing_ty {
                self.constraints.wants_equals_at_with_cause(
                    type_annotation.id,
                    existing,
                    annotation_ty.clone(),
                    &context.group_info(),
                    Some(ConstraintCause::Annotation(type_annotation.id)),
                );
            }
            annotation_ty
        } else if let Some(existing) = existing_ty {
            // No annotation but have existing - use it
            return Ok(TypedParameter {
                name: sym,
                ty: existing,
            });
        } else {
            self.session.new_ty_meta_var(context.level())
        };

        // I feel like params are always monotypes? But tests were failing when we
        // made them all mono..., i dont know
        if param.name.name_str() == "self" {
            self.session
                .insert_mono(sym, ty.clone(), &mut self.constraints);
        } else {
            self.session.insert(sym, ty.clone(), &mut self.constraints);
        }

        Ok(TypedParameter { name: sym, ty })
    }

    #[instrument(level = tracing::Level::TRACE, skip(self, context))]
    pub(super) fn visit_type_annotation(
        &mut self,
        type_annotation: &TypeAnnotation,
        context: &mut SolveContext,
    ) -> TypedRet<Ty> {
        match &type_annotation.kind {
            TypeAnnotationKind::Nominal { name, generics, .. } => {
                let Ok(sym) = name.symbol() else {
                    return Err(TypeError::NameNotResolved(name.clone()));
                };

                let generic_args: Vec<_> = generics
                    .iter()
                    .map(|g| self.visit_type_annotation(g, context))
                    .try_collect::<Ty, Vec<_>, TypeError>()?
                    .into_iter()
                    .zip(generics.iter().map(|g| g.id))
                    .collect();

                if let (
                    SolveContextKind::Protocol {
                        protocol_self,
                        protocol_id,
                    },
                    Symbol::AssociatedType(..),
                ) = (context.kind(), sym)
                {
                    if let Some(entry) = self.session.lookup(&sym)
                        && let Some(ForAll::Ty(assoc_param)) = entry
                            .foralls()
                            .iter()
                            .find(|fa| matches!(fa, ForAll::Ty(p) if *p != protocol_self))
                    {
                        // Get bounds directly from the entry's type if it's a Param
                        let bounds = if let Ty::Param(_, bounds) = entry._as_ty() {
                            bounds
                        } else {
                            vec![]
                        };
                        return Ok(Ty::Param(*assoc_param, bounds));
                    }

                    // Fallback: fresh variable for the associated type's value in this position.
                    let result = self.session.new_ty_meta_var(context.level());

                    // Base is the protocol "Self" variable in this requirement.
                    let base = Ty::Param(protocol_self, vec![protocol_id]);

                    self.constraints.wants_projection(
                        type_annotation.id,
                        base,
                        name.name_str().into(), // "T"
                        Some(protocol_id),
                        result.clone(),
                        &context.group_info(),
                    );

                    return Ok(result);
                }

                if matches!(name.symbol(), Ok(Symbol::Builtin(..))) {
                    if !generic_args.is_empty() {
                        return Err(self.report_error(
                            type_annotation.id,
                            TypeError::GenericArgCount {
                                expected: 0,
                                actual: generic_args.len() as u8,
                            },
                        ));
                    }

                    return Ok(resolve_builtin_type(
                        &name
                            .symbol()
                            .map_err(|_| TypeError::NameNotResolved(name.clone()))?,
                    )
                    .0);
                }

                if let Some(nominal) = self.session.lookup_nominal(&sym)
                    && !generic_args.is_empty()
                    && generic_args.len() != nominal.type_params.len()
                {
                    return Err(self.report_error(
                        type_annotation.id,
                        TypeError::GenericArgCount {
                            expected: nominal.type_params.len() as u8,
                            actual: generic_args.len() as u8,
                        },
                    ));
                }

                // Do we know about this already? Cool.
                if let Some(entry) = self.session.lookup(&sym) {
                    let instantiated = entry.instantiate_with_args(
                        type_annotation.id,
                        &generic_args,
                        self.session,
                        context,
                        &mut self.constraints,
                    );

                    self.instantiations
                        .insert(type_annotation.id, instantiated.type_args.clone());

                    return Ok(instantiated.value);
                } else {
                    tracing::warn!("nope, did not find anything in the env for {name:?}");
                }

                Ok(Ty::Nominal {
                    symbol: sym,
                    type_args: generic_args.into_iter().map(|a| a.0).collect(),
                })
            }
            TypeAnnotationKind::SelfType(name) => {
                if let SolveContextKind::Protocol {
                    protocol_self,
                    protocol_id,
                } = context.kind()
                {
                    return Ok(Ty::Param(protocol_self, vec![protocol_id]));
                }

                let Some(self_ty) = &self.current_self_ty else {
                    return Err(TypeError::TypeNotFound(format!(
                        "SelfType outside of nominal context: {name:?}"
                    )));
                };

                Ok(self_ty.clone())
            }
            TypeAnnotationKind::Record { fields } => {
                let mut row = Row::Empty;
                for field in fields.iter().rev() {
                    row = Row::Extend {
                        row: Box::new(row),
                        label: field.label.name_str().into(),
                        ty: self.visit_type_annotation(&field.value, context)?,
                    };
                }

                Ok(Ty::Record(None, Box::new(row)))
            }
            TypeAnnotationKind::NominalPath {
                base,
                member,
                member_generics,
                ..
            } => {
                let base_ty = self.visit_type_annotation(base, context)?;
                let generics = member_generics
                    .iter()
                    .map(|t| self.visit_type_annotation(t, context))
                    .try_collect()?;
                let ret = self.session.new_ty_meta_var(context.level());

                if matches!(&base_ty, Ty::Param(..) | Ty::Rigid(..)) {
                    self.constraints.wants_projection(
                        type_annotation.id,
                        base_ty,
                        member.clone(),
                        None,
                        ret.clone(),
                        &context.group_info(),
                    );
                } else {
                    self.constraints.wants_type_member(
                        base_ty,
                        member.clone(),
                        generics,
                        ret.clone(),
                        type_annotation.id,
                        &context.group_info(),
                        ConstraintCause::Annotation(type_annotation.id),
                    );
                }

                Ok(ret)
            }
            TypeAnnotationKind::Tuple(items) => {
                if items.is_empty() {
                    return Ok(Ty::Void);
                }

                Ok(Ty::Tuple(
                    items
                        .iter()
                        .map(|t| self.visit_type_annotation(t, context))
                        .try_collect()?,
                ))
            }
            TypeAnnotationKind::Func { params, returns } => {
                let param_tys: Vec<Ty> = params
                    .iter()
                    .map(|p| self.visit_type_annotation(p, context))
                    .try_collect()?;
                let return_ty = self.visit_type_annotation(returns, context)?;

                Ok(curry(param_tys, return_ty, Row::Empty.into()))
            }
        }
    }

    pub(super) fn register_generic(
        &mut self,
        generic: &GenericDecl,
        context: &mut SolveContext,
    ) -> Symbol {
        // Check if this generic has already been registered (e.g., in a previous pass)
        if let Ok(sym) = generic.name.symbol()
            && let Some(entry) = self.session.lookup(&sym)
            && let Ty::Param(existing_id, _) = entry._as_ty()
        {
            return existing_id;
        }

        let param_id = self.session.new_type_param_id(None);

        tracing::debug!(
            "register_generic: {:?}, conformances: {:?}, available requirements: {:?}",
            generic.name,
            generic.conformances,
            self.protocol_associated_type_requirements
                .keys()
                .collect::<Vec<_>>()
        );

        // Collect protocol bounds for the type param
        let mut bounds = vec![];

        for conformance in generic.conformances.iter() {
            let Ok(Symbol::Protocol(protocol_id)) = conformance.symbol() else {
                tracing::warn!("could not determine conformance: {conformance:?}");
                continue;
            };

            tracing::debug!("Processing conformance to protocol_id: {:?}", protocol_id);

            bounds.push(protocol_id);

            let predicate = Predicate::Conforms {
                param: param_id,
                protocol_id,
            };

            context.givens_mut().insert(predicate.clone());

            // Also add associated type predicates from this protocol to context.givens
            // This enables member resolution on associated types (e.g., T.Food: Named)
            if let Some(requirements) = self.protocol_associated_type_requirements.get(&protocol_id)
            {
                tracing::debug!(
                    "Found protocol_associated_type_requirements for {:?}: {:?}",
                    protocol_id,
                    requirements
                );
                for assoc_predicate in &requirements.predicates {
                    tracing::debug!("Adding assoc_predicate to givens: {:?}", assoc_predicate);
                    context.givens_mut().insert(assoc_predicate.clone());
                }
            } else {
                tracing::debug!(
                    "No protocol_associated_type_requirements found for {:?}",
                    protocol_id
                );
            }
        }

        let Ok(sym) = generic.name.symbol() else {
            self.diagnostics.insert(AnyDiagnostic::Typing(Diagnostic {
                id: generic.id,
                severity: Severity::Error,
                kind: TypeError::NameNotResolved(generic.name.clone()),
            }));
            return Symbol::IR_TYPE_PARAM;
        };

        self.session
            .insert_mono(sym, Ty::Param(param_id, bounds), &mut self.constraints);

        param_id
    }
}
