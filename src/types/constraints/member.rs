use crate::{
    label::Label,
    name_resolution::symbol::Symbol,
    span::Span,
    types::{
        constraints::constraint::{Constraint, ConstraintCause},
        passes::{
            dependencies_pass::{ConformanceRequirement, SCCResolved},
            inference_pass::curry,
        },
        row::Row,
        term_environment::EnvEntry,
        ty::{Level, Primitive, Ty},
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
    pub receiver: Ty,
    pub label: Label,
    pub ty: Ty,
    pub cause: ConstraintCause,
    pub span: Span,
}

impl Member {
    pub fn solve(
        &self,
        session: &mut TypeSession<SCCResolved>,
        level: Level,
        next_wants: &mut Wants,
        substitutions: &mut UnificationSubstitutions,
    ) -> Result<bool, TypeError> {
        let mut receiver = self.receiver.clone();
        let ty = self.ty.clone();

        tracing::debug!(
            "Member::solve receiver={receiver:?}, label={:?}",
            self.label
        );

        if matches!(
            receiver,
            Ty::UnificationVar { .. } | Ty::Rigid(_) | Ty::Param(_)
        ) {
            // If we don't know what the receiver is yet, we can't do much
            tracing::debug!("deferring member constraint");
            next_wants.push(Constraint::Member(self.clone()));
            return Ok(false);
        }

        if let Ty::TypeConstructor(type_id) = receiver {
            receiver = Ty::Nominal {
                id: type_id,
                type_args: vec![],
                row: Box::new(session.new_row_meta_var(level)),
            };
        }

        if let Ty::Nominal { id: type_id, .. } | Ty::Constructor { type_id, .. } = &receiver
            && let Some(nominal) = session
                .phase
                .type_catalog
                .nominals
                .get(&type_id.into())
                .cloned()
        {
            // First, check if any conforming protocols have this method with predicates
            let mut protocol_method = None;
            for conformance_key in session.phase.type_catalog.conformances.keys() {
                if conformance_key.conforming_id == (*type_id).into() {
                    let protocol_id = conformance_key.protocol_id;
                    if let Some(protocol) = session.phase.type_catalog.protocols.get(&protocol_id)
                        && let Some(requirement) = protocol.requirements.get(&self.label)
                        && let ConformanceRequirement::Unfulfilled(req_sym) = requirement
                        && let Some(entry) = session.term_env.lookup(req_sym).cloned()
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
                if let Some(entry) = session.term_env.lookup(sym).cloned() {
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
                    if let Ty::Func(first, box _rest) = scheme_ty.clone() {
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
                    let (Ty::Record(row) | Ty::Nominal { row, .. }) = &receiver else {
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

                    if let Ty::Func(param, rest) = payload_ty {
                        // It's an instance method on the enum. Strip `self` like struct methods.
                        unify(&receiver, &param, substitutions, session)?;
                        let applied = if !matches!(*rest, Ty::Func(..)) {
                            Ty::Func(Box::new(Ty::Void), rest)
                        } else {
                            *rest
                        };
                        return unify(&ty, &applied, substitutions, session);
                    }

                    let mut row = Row::Empty(TypeDefKind::Enum);
                    for (label, sym) in variants.iter() {
                        let base_vty = match session
                            .term_env
                            .lookup(sym)
                            .expect("variant missing")
                            .clone()
                        {
                            EnvEntry::Mono(t) => t,
                            EnvEntry::Scheme(s) => s.ty,
                        };
                        let vty = instantiate_ty(base_vty, &inst_subs, level);
                        row = Row::Extend {
                            row: Box::new(row),
                            label: label.clone(),
                            ty: vty,
                        };
                    }

                    let result_enum = Ty::Nominal {
                        id: *type_id,
                        row: Box::new(row),
                        type_args: vec![],
                    };

                    // 3) Build the constructor’s type from payload → result_enum
                    let ctor_ty = match &payload_ty {
                        Ty::Primitive(Primitive::Void) => result_enum.clone(),
                        Ty::Tuple(items) if items.is_empty() => result_enum.clone(),
                        Ty::Tuple(items) if items.len() == 1 => {
                            Ty::Func(Box::new(items[0].clone()), Box::new(result_enum.clone()))
                        }
                        Ty::Tuple(items) => curry(items.clone(), result_enum.clone()),
                        other => Ty::Func(Box::new(other.clone()), Box::new(result_enum.clone())),
                    };

                    unify(&ty, &ctor_ty, substitutions, session)
                }
                other => {
                    unreachable!("other: {other:?}");
                }
            }
        } else if let Ty::Record(row) = receiver {
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
