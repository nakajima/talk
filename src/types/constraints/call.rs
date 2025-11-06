use crate::{
    node_id::NodeID,
    span::Span,
    types::{
        constraints::constraint::{Constraint, ConstraintCause},
        infer_ty::{InferTy, Level},
        term_environment::EnvEntry,
        type_error::TypeError,
        type_operations::{UnificationSubstitutions, curry, unify},
        type_session::TypeSession,
        wants::Wants,
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
        session: &mut TypeSession,
        next_wants: &mut Wants,
        substitutions: &mut UnificationSubstitutions,
    ) -> Result<bool, TypeError> {
        if matches!(&self.callee, InferTy::Var { .. }) {
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
                let Some(returns_type_entry) = session.lookup(&name.symbol()) else {
                    tracing::trace!("no type found for {name:?}, deferring");
                    next_wants.push(Constraint::Call(self.clone()));
                    return Ok(false);
                };
                let returns_type = returns_type_entry
                    .instantiate(self.callee_id, session, self.level, next_wants, self.span)
                    .0;

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

                    entry
                        .instantiate(self.callee_id, session, self.level, next_wants, self.span)
                        .0
                } else {
                    println!("CALL: {:?}", self);
                    match session
                        .lookup(&name.symbol())
                        .expect("enum type missing from env")
                    {
                        EnvEntry::Mono(ty) => ty,
                        EnvEntry::Scheme(s) => s.ty.clone(),
                    }
                };

                next_wants.equals(
                    self.returns.clone(),
                    returns_type.clone(),
                    ConstraintCause::Internal,
                    self.span,
                );

                unify(&init_ty, &curry(args, returns_type), substitutions, session)
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
