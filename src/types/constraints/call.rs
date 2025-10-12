use crate::{
    span::Span,
    types::{
        constraints::constraint::{Constraint, ConstraintCause},
        infer_ty::{InferTy, Level},
        passes::inference_pass::curry,
        term_environment::EnvEntry,
        type_error::TypeError,
        type_operations::{UnificationSubstitutions, unify},
        type_session::TypeSession,
        wants::Wants,
    },
};

#[derive(Debug, Clone)]
pub struct Call {
    pub callee: InferTy,
    pub args: Vec<InferTy>,
    pub returns: InferTy,
    pub receiver: Option<InferTy>, // If it's a method
    pub span: Span,
    pub cause: ConstraintCause,
}

impl Call {
    pub fn solve(
        &self,
        session: &mut TypeSession,
        next_wants: &mut Wants,
        substitutions: &mut UnificationSubstitutions,
    ) -> Result<bool, TypeError> {
        if matches!(&self.callee, InferTy::UnificationVar { .. }) {
            tracing::trace!(
                "unable to determine callee type: {:?}, substitutions: {substitutions:?}",
                self.callee
            );
            // We don't know the callee yet, defer
            next_wants.push(Constraint::Call(self.clone()));
            return Ok(false);
        }

        let mut args = self.args.to_vec();

        if let Some(receiver) = &self.receiver
            && !matches!(receiver, InferTy::Constructor { .. })
        {
            args.insert(0, receiver.clone());
        }

        match &self.callee {
            InferTy::Constructor { name, .. } => {
                // TODO: Figure out if we're dealing with a struct vs an enum here and be more explicit.
                // This is ok for now since enums can't have initializers and structs always have them.
                let init_ty = if let Some(initializer) = session
                    .lookup_initializers(&name.symbol().unwrap())
                    .and_then(|i| i.values().next().copied())
                {
                    let entry = session
                        .lookup(&initializer)
                        .expect("constructor scheme missing");
                    entry.inference_instantiate(session, Level(1), next_wants, self.span)
                } else {
                    match session
                        .lookup(&name.symbol().unwrap())
                        .expect("enum type missing from env")
                    {
                        EnvEntry::Mono(ty) => ty,
                        EnvEntry::Scheme(s) => s.ty.clone(),
                    }
                };

                unify(
                    &init_ty,
                    &curry(args, self.returns.clone()),
                    substitutions,
                    session,
                )
            }
            InferTy::Func(..) => {
                if args.is_empty() {
                    unify(
                        &self.callee,
                        &InferTy::Func(InferTy::Void.into(), self.returns.clone().into()),
                        substitutions,
                        session,
                    )
                } else {
                    unify(
                        &self.callee,
                        &curry(args, self.returns.clone()),
                        substitutions,
                        session,
                    )
                }
            }
            ty => Err(TypeError::CalleeNotCallable(ty.clone())),
        }
    }
}
