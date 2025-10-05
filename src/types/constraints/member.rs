use crate::{
    label::Label,
    name_resolution::symbol::Symbol,
    span::Span,
    types::{
        constraints::{
            conforms::TakeToSlot,
            constraint::{Constraint, ConstraintCause},
        },
        infer_row::InferRow,
        infer_ty::{InferTy, Level, Primitive},
        passes::{dependencies_pass::ConformanceRequirement, inference_pass::curry},
        term_environment::EnvEntry,
        type_catalog::NominalForm,
        type_error::TypeError,
        type_operations::{
            InstantiationSubstitutions, UnificationSubstitutions, instantiate_ty, unify,
        },
        type_session::{TypeDefKind, TypeSession},
        wants::Wants,
    },
};

#[derive(Debug, Clone)]
pub struct Member {
    pub receiver: InferTy,
    pub label: Label,
    pub ty: InferTy,
    pub cause: ConstraintCause,
    pub span: Span,
}

impl Member {
    pub fn solve(
        &self,
        session: &mut TypeSession,
        level: Level,
        next_wants: &mut Wants,
        substitutions: &mut UnificationSubstitutions,
    ) -> Result<bool, TypeError> {
        let receiver = self.receiver.clone();
        let ty = self.ty.clone();

        tracing::debug!(
            "Member::solve receiver={receiver:?}, label={:?}",
            self.label
        );

        if matches!(
            receiver,
            InferTy::UnificationVar { .. } | InferTy::Rigid(_) | InferTy::Param(_)
        ) {
            // If we don't know what the receiver is yet, we can't do much
            tracing::debug!("deferring member constraint");
            next_wants.push(Constraint::Member(self.clone()));
            return Ok(false);
        }

        if let InferTy::Nominal { id: type_id, .. } | InferTy::Constructor { type_id, .. } =
            &receiver
            && let Some(nominal) = session.type_catalog.nominals.get(&type_id.into()).cloned()
        {
            // First, check if any conforming protocols have this method with predicates
            let mut protocol_method = None;
            let conformances = TakeToSlot::new(&mut session.type_catalog.conformances);
            for conformance_key in conformances.keys() {
                if conformance_key.conforming_id == (*type_id).into() {
                    let protocol_id = conformance_key.protocol_id;
                    if let Some(protocol) =
                        session.type_catalog.protocols.get(&protocol_id).cloned()
                        && let Some(requirement) = protocol.requirements.get(&self.label)
                        && let ConformanceRequirement::Unfulfilled(req_sym) = requirement
                        && let Some(entry) = session.lookup(req_sym)
                    {
                        // Check if this protocol method has predicates - if so, prefer it
                        if let crate::types::term_environment::EnvEntry::Scheme(ref scheme) = entry
                            && !scheme.predicates.is_empty()
                        {
                            tracing::debug!("Found protocol method with predicates: {req_sym:?}");
                            protocol_method = Some((*req_sym, entry));
                            break;
                        }
                    }
                }
            }

            // Use protocol method if found, otherwise use the nominal's method
            let (sym, entry) = if let Some((sym, entry)) = protocol_method {
                (sym, entry)
            } else if let Some(sym) = nominal.member_symbol(&self.label) {
                if let Some(entry) = session.lookup(sym) {
                    (*sym, entry)
                } else {
                    return Err(TypeError::MemberNotFound(receiver, self.label.to_string()));
                }
            } else {
                return Err(TypeError::MemberNotFound(receiver, self.label.to_string()));
            };

            tracing::debug!("Member::solve looking up {sym:?}, got entry: {entry:?}");
            match sym {
                Symbol::InstanceMethod(_) => {
                    let scheme_ty = entry.solver_instantiate(
                        session,
                        level,
                        substitutions,
                        next_wants,
                        self.span,
                    );
                    if let InferTy::Func(first, box _rest) = scheme_ty.clone() {
                        unify(&receiver, &first, substitutions, session)?;
                        unify(&ty, &scheme_ty, substitutions, session)
                    } else {
                        unreachable!("instance method must be a function")
                    }
                }
                Symbol::StaticMethod(_) => {
                    let scheme_ty = entry.solver_instantiate(
                        session,
                        level,
                        substitutions,
                        next_wants,
                        self.span,
                    );

                    unify(&ty, &scheme_ty, substitutions, session)
                }
                Symbol::Property(..) => {
                    tracing::trace!("got a property (row lookup)");
                    // Use the *receiver’s* row so we pick up the ctor’s instantiation.
                    let (InferTy::Record(row) | InferTy::Nominal { row, .. }) = &receiver else {
                        return Err(TypeError::ExpectedRow(receiver));
                    };

                    // Apply current subs to normalize any Row::Var links produced by the ctor unification.
                    next_wants._has_field(
                        *row.clone(),
                        self.label.clone(),
                        ty.clone(),
                        self.cause,
                        self.span,
                    );

                    Ok(true)
                }
                Symbol::Variant(_) => {
                    let (payload_ty, inst_subs) = match entry {
                        EnvEntry::Mono(t) => (t, InstantiationSubstitutions::default()),
                        EnvEntry::Scheme(s) => s.solver_instantiate(
                            session,
                            level,
                            next_wants,
                            self.span,
                            substitutions,
                        ),
                    };

                    let NominalForm::Enum { variants, .. } = &nominal.form else {
                        unreachable!()
                    };

                    if let InferTy::Func(param, rest) = payload_ty {
                        // It's an instance method on the enum. Strip `self` like struct methods.
                        unify(&receiver, &param, substitutions, session)?;
                        let applied = if !matches!(*rest, InferTy::Func(..)) {
                            InferTy::Func(Box::new(InferTy::Void), rest)
                        } else {
                            *rest
                        };
                        return unify(&ty, &applied, substitutions, session);
                    }

                    let mut row = InferRow::Empty(TypeDefKind::Enum);
                    for (label, sym) in variants.iter() {
                        let base_vty = match session.lookup(sym).expect("variant missing").clone() {
                            EnvEntry::Mono(t) => t,
                            EnvEntry::Scheme(s) => s.ty,
                        };
                        let vty = instantiate_ty(base_vty, &inst_subs, level);
                        row = InferRow::Extend {
                            row: Box::new(row),
                            label: label.clone(),
                            ty: vty,
                        };
                    }

                    let result_enum = InferTy::Nominal {
                        id: *type_id,
                        row: Box::new(row),
                        type_args: vec![],
                    };

                    // 3) Build the constructor’s type from payload → result_enum
                    let ctor_ty = match &payload_ty {
                        InferTy::Primitive(Primitive::Void) => result_enum.clone(),
                        InferTy::Tuple(items) if items.is_empty() => result_enum.clone(),
                        InferTy::Tuple(items) if items.len() == 1 => {
                            InferTy::Func(Box::new(items[0].clone()), Box::new(result_enum.clone()))
                        }
                        InferTy::Tuple(items) => curry(items.clone(), result_enum.clone()),
                        other => {
                            InferTy::Func(Box::new(other.clone()), Box::new(result_enum.clone()))
                        }
                    };

                    unify(&ty, &ctor_ty, substitutions, session)
                }
                other => {
                    unreachable!("other: {other:?}");
                }
            }
        } else if let InferTy::Record(row) = receiver {
            next_wants._has_field(
                *row.clone(),
                self.label.clone(),
                ty.clone(),
                self.cause,
                self.span,
            );
            Ok(true)
        } else {
            Err(TypeError::MemberNotFound(receiver, self.label.to_string()))
        }
    }
}
