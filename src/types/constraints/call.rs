use crate::{
    span::Span,
    types::{
        constraint::{Constraint, ConstraintCause},
        passes::inference_pass::{InferencePass, Wants, curry},
        ty::Ty,
        type_error::TypeError,
        type_operations::{UnificationSubstitutions, apply, apply_mult, unify},
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
        pass: &mut InferencePass,
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

        tracing::debug!("callee: {callee:?} {args:?} {returns:?}");

        match &callee {
            Ty::Constructor { param, ret, .. } => {
                args.insert(0, returns.clone());
                unify(
                    &Ty::Func(Box::new(*param.clone()), Box::new(*ret.clone())),
                    &curry(args, returns),
                    substitutions,
                    &mut pass.session.vars,
                )
            }
            Ty::Variant(_, ty) => {
                println!("oh hi it's call {args:?}, ty: {ty:?}");
                let args_ty = if args.len() == 1 {
                    args[0].clone()
                } else {
                    Ty::Tuple(args.to_vec())
                };

                let args_ok = unify(ty, &args_ty, substitutions, &mut pass.session.vars)?;
                let returns_ok = unify(&returns, &callee, substitutions, &mut pass.session.vars)?;
                Ok(args_ok || returns_ok)
            }
            Ty::Func(..) => {
                // if let Some(receiver) = &self.receiver {
                //     tracing::trace!("prepending receiver to method: {receiver:?}");
                //     args.insert(0, receiver.clone());
                // } else {
                //     tracing::trace!("no receiver");
                // }

                tracing::debug!(
                    "Call solve: callee={callee:?}, args={args:?}, returns={returns:?}"
                );
                if args.is_empty() {
                    unify(
                        &callee,
                        &Ty::Func(Ty::Void.into(), returns.into()),
                        substitutions,
                        &mut pass.session.vars,
                    )
                } else {
                    unify(
                        &callee,
                        &curry(args, returns),
                        substitutions,
                        &mut pass.session.vars,
                    )
                }
            }
            ty => Err(TypeError::CalleeNotCallable(ty.clone())),
        }
    }
}
