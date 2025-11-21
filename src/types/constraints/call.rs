use crate::{
    node_id::NodeID,
    span::Span,
    types::{
        constraints::constraint::{Constraint, ConstraintCause},
        infer_ty::{InferTy, Level},
        solve_context::SolveContext,
        term_environment::EnvEntry,
        type_error::TypeError,
        type_operations::{apply, curry, unify},
        type_session::TypeSession,
    },
};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Call {
    pub callee_id: NodeID,
    pub callee: InferTy,
    pub args: Vec<InferTy>,
    pub type_args: Vec<InferTy>,
    pub returns: InferTy,
    pub receiver: Option<InferTy>, // If it's a method
    pub span: Span,
    pub cause: ConstraintCause,
    pub level: Level,
}

impl Call {
    pub fn solve(
        &self,
        context: &mut SolveContext,
        session: &mut TypeSession,
    ) -> Result<bool, TypeError> {
        let callee = apply(self.callee.clone(), &mut context.substitutions);
        let returns = apply(self.returns.clone(), &mut context.substitutions);

        if matches!(&callee, InferTy::Var { .. }) {
            tracing::trace!(
                "unable to determine callee type: {:?}, substitutions: {returns:?}",
                self.callee
            );
            // We don't know the callee yet, defer
            context.wants.push(Constraint::Call(self.clone()));
            return Ok(false);
        }

        let mut args = self.args.to_vec();

        match &self.callee {
            InferTy::Constructor { name, .. } => {
                let Some(returns_type_entry) = session.lookup(&name.symbol()) else {
                    context.wants.defer(Constraint::Call(self.clone()));
                    return Ok(false);
                };
                let returns_type =
                    returns_type_entry.instantiate(self.callee_id, context, session, self.span);

                // TODO: Figure out if we're dealing with a struct vs an enum here and be more explicit.
                // This is ok for now since enums can't have initializers and structs always have them.
                let init_ty = if let Some(initializer) = session
                    .lookup_initializers(&name.symbol())
                    .and_then(|i| i.values().next().copied())
                {
                    args.insert(0, returns_type.clone());

                    let entry = session
                        .lookup(&initializer)
                        .expect("constructor scheme missing");

                    entry.instantiate(self.callee_id, context, session, self.span)
                } else {
                    match session
                        .lookup(&name.symbol())
                        .expect("enum type missing from env")
                    {
                        EnvEntry::Mono(ty) => ty,
                        EnvEntry::Scheme(s) => s.ty.clone(),
                    }
                };

                context.wants.equals(
                    self.returns.clone(),
                    returns_type.clone(),
                    ConstraintCause::Internal,
                    self.span,
                );

                unify(&init_ty, &curry(args, returns_type), context, session)
            }
            InferTy::Func(..) => {
                if args.is_empty() {
                    unify(
                        &self.callee,
                        &InferTy::Func(InferTy::Void.into(), self.returns.clone().into()),
                        context,
                        session,
                    )
                } else {
                    unify(
                        &self.callee,
                        &curry(args, self.returns.clone()),
                        context,
                        session,
                    )
                }
            }
            ty => Err(TypeError::CalleeNotCallable(ty.clone())),
        }
    }
}
