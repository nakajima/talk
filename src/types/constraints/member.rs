use crate::{
    label::Label,
    span::Span,
    types::{
        constraint::{Constraint, ConstraintCause},
        passes::dependencies_pass::SCCResolved,
        term_environment::EnvEntry,
        ty::{Level, Ty},
        type_error::TypeError,
        type_operations::{UnificationSubstitutions, apply, unify},
        type_session::TypeSession,
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
        let receiver = apply(self.receiver.clone(), substitutions);
        let ty = apply(self.ty.clone(), substitutions);

        if matches!(receiver, Ty::UnificationVar { .. }) {
            // If we don't know what the receiver is yet, we can't do much
            next_wants.push(Constraint::Member(self.clone()));
            return Ok(false);
        }

        if let Ty::Nominal { id: type_id, .. } = &receiver
            && let Some(nominal) = session.phase.type_catalog.nominals.get(type_id).cloned()
            && let Some(sym) = nominal.member_symbol(&self.label)
            && let Some(entry) = session.term_env.lookup(sym).cloned()
        {
            // Remember where next_wants currently ends,
            // so we can consume only the constraints emitted during instantiation.
            let start_ix = next_wants.0.len();

            // Instantiate as you already do (keep your type-arg substitution if you want).
            let member_ty = match entry {
                EnvEntry::Mono(ty) => ty.clone(),
                EnvEntry::Scheme(scheme) => {
                    scheme
                        .solver_instantiate(session, level, next_wants, self.span, substitutions)
                        .0
                }
            };

            // If it's a function (method or property-getter), tie Self := receiver.
            if let Ty::Func(self_param, ret) = &member_ty {
                let _ = unify(self_param, &receiver, substitutions, &mut session.vars)?;
                // For a property-as-getter, we want the *value* of the projection:
                // unifying `ty` with the function’s *return* type makes that happen.
                let _ = unify(&ty, ret, substitutions, &mut session.vars)?;
            } else {
                // Property-as-value encoding (if you move to that later).
                let _ = unify(&ty, &member_ty, substitutions, &mut session.vars)?;
            }

            // Consume any freshly-emitted Member predicates equivalent to this one,
            // and solve them inline to avoid re-queuing/looping.
            // (Keep unrelated predicates in the queue.)
            let mut i = start_ix;
            while i < next_wants.0.len() {
                match &next_wants.0[i] {
                    Constraint::Member(m) if m.label == self.label => {
                        // Tie the scheme’s Self and result to *our* receiver/result.
                        let _ = unify(
                            &apply(m.receiver.clone(), substitutions),
                            &receiver,
                            substitutions,
                            &mut session.vars,
                        )?;
                        let _ = unify(
                            &apply(m.ty.clone(), substitutions),
                            &ty,
                            substitutions,
                            &mut session.vars,
                        )?;
                        next_wants.0.remove(i);
                        continue;
                    }
                    _ => {}
                }
                i += 1;
            }

            return Ok(true);
        }

        // If it's not a method, figure out the row and emit a has field constraint
        let Ty::Record(row) = receiver else {
            return Err(TypeError::ExpectedRow(receiver));
        };

        next_wants._has_field(
            *row,
            self.label.clone(),
            self.ty.clone(),
            self.cause,
            self.span,
        );

        Ok(true)
    }
}
