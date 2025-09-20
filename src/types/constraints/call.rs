use crate::{
    span::Span,
    types::{
        constraint::{Constraint, ConstraintCause},
        passes::{dependencies_pass::SCCResolved, inference_pass::curry},
        ty::Ty,
        type_error::TypeError,
        type_operations::{UnificationSubstitutions, apply, apply_mult, unify},
        type_session::TypeSession,
        wants::Wants,
    },
};

#[derive(Debug, Clone)]
pub struct Call {
    pub callee: Ty,
    pub args: Vec<Ty>,
    pub returns: Ty,
    pub receiver: Option<Ty>, // If it's a method
    pub span: Span,
    pub cause: ConstraintCause,
}

impl Call {
    pub fn solve(
        &self,
        session: &mut TypeSession<SCCResolved>,
        next_wants: &mut Wants,
        substitutions: &mut UnificationSubstitutions,
    ) -> Result<bool, TypeError> {
        // Get everything up to date
        let callee = apply(self.callee.clone(), substitutions);

        if matches!(callee, Ty::UnificationVar { .. }) {
            tracing::warn!(
                "unable to determine callee type: {callee:?}, substitutions: {substitutions:?}"
            );
            // We don't know the callee yet, defer
            next_wants.push(Constraint::Call(self.clone()));
            return Ok(false);
        }

        let mut args = apply_mult(self.args.to_vec(), substitutions);
        let returns = apply(self.returns.clone(), substitutions);

        if let Some(receiver) = &self.receiver {
            let receiver = apply(receiver.clone(), substitutions);
            // receiver is the first parameter for instance methods
            //args.insert(0, receiver);
        }

        tracing::debug!("callee: {callee:?} {args:?} {returns:?}");

        match &callee {
            Ty::Constructor {
                params, box ret, ..
            } => unify(
                &curry(params.clone(), ret.clone()),
                &curry(args, returns),
                substitutions,
                &mut session.vars,
            ),
            Ty::Func(..) => {
                if args.is_empty() {
                    unify(
                        &callee,
                        &Ty::Func(Ty::Void.into(), returns.into()),
                        substitutions,
                        &mut session.vars,
                    )
                } else {
                    unify(
                        &callee,
                        &curry(args, returns),
                        substitutions,
                        &mut session.vars,
                    )
                }
            }
            ty => Err(TypeError::CalleeNotCallable(ty.clone())),
        }
    }
}
