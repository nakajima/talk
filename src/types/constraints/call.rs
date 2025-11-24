use crate::{
    node_id::NodeID,
    types::{
        constraint_solver::{DeferralReason, SolveResult},
        constraints::store::{ConstraintId, ConstraintStore},
        infer_ty::{InferTy, Meta},
        solve_context::SolveContext,
        term_environment::EnvEntry,
        type_error::TypeError,
        type_operations::{apply, curry, unify},
        type_session::TypeSession,
    },
};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Call {
    pub id: ConstraintId,
    pub callee_id: NodeID,
    pub callee: InferTy,
    pub args: Vec<InferTy>,
    pub type_args: Vec<InferTy>,
    pub returns: InferTy,
    pub receiver: Option<InferTy>, // If it's a method
}

impl Call {
    pub fn solve(
        &self,
        constraints: &mut ConstraintStore,
        context: &mut SolveContext,
        session: &mut TypeSession,
    ) -> SolveResult {
        let callee = apply(self.callee.clone(), &mut context.substitutions);
        let returns = apply(self.returns.clone(), &mut context.substitutions);

        if let InferTy::Var { id, .. } = &callee {
            tracing::trace!(
                "unable to determine callee type: {:?}, substitutions: {returns:?}",
                self.callee
            );

            // We don't know the callee yet, defer
            return SolveResult::Defer(DeferralReason::WaitingOnMeta(Meta::Ty(*id)));
        }

        let mut args = self.args.to_vec();

        match &self.callee {
            InferTy::Constructor { name, .. } => {
                let Ok(sym) = name.symbol() else {
                    return SolveResult::Err(TypeError::NameNotResolved(name.clone()));
                };

                let Some(returns_type_entry) = session.lookup(&sym) else {
                    return SolveResult::Defer(DeferralReason::WaitingOnSymbol(sym));
                };

                let returns_type =
                    returns_type_entry.instantiate(self.callee_id, constraints, context, session);

                // TODO: Figure out if we're dealing with a struct vs an enum here and be more explicit.
                // This is ok for now since enums can't have initializers and structs always have them.
                let init_ty = if let Some(initializer) = session
                    .lookup_initializers(&sym)
                    .and_then(|i| i.values().next().copied())
                {
                    args.insert(0, returns_type.clone());

                    if let Some(entry) = session.lookup(&initializer) {
                        entry.instantiate(self.callee_id, constraints, context, session)
                    } else {
                        InferTy::Error(TypeError::TypeNotFound(format!("{initializer:?}")).into())
                    }
                } else {
                    match session.lookup(&sym) {
                        Some(EnvEntry::Mono(ty)) => ty,
                        Some(EnvEntry::Scheme(s)) => s.ty.clone(),
                        _ => InferTy::Error(
                            TypeError::TypeNotFound(format!("Missing {name:?}")).into(),
                        ),
                    }
                };

                constraints.wants_equals(self.returns.clone(), returns_type.clone());

                match unify(&init_ty, &curry(args, returns_type), context, session) {
                    Ok(metas) => SolveResult::Solved(metas),
                    Err(e) => SolveResult::Err(e),
                }
            }
            InferTy::Func(..) => {
                let res = if args.is_empty() {
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
                };

                match res {
                    Ok(metas) => SolveResult::Solved(metas),
                    Err(e) => SolveResult::Err(e),
                }
            }
            ty => SolveResult::Err(TypeError::CalleeNotCallable(ty.clone())),
        }
    }
}
