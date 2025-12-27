use tracing::instrument;

use crate::{
    node_id::NodeID,
    types::{
        constraint_solver::{DeferralReason, SolveResult},
        constraints::{constraint::ConstraintCause, store::{ConstraintId, ConstraintStore}},
        infer_ty::{InferTy, Meta},
        solve_context::{Solve, SolveContext},
        term_environment::EnvEntry,
        type_error::TypeError,
        type_operations::{curry, unify},
        type_session::TypeSession,
    },
};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Call {
    pub id: ConstraintId,
    pub call_node_id: NodeID,
    pub callee_id: NodeID,
    pub callee: InferTy,
    pub args: Vec<InferTy>,
    pub type_args: Vec<InferTy>,
    pub returns: InferTy,
    pub receiver: Option<InferTy>, // If it's a method
}

impl Call {
    #[instrument(skip(constraints, context, session))]
    pub fn solve(
        &self,
        constraints: &mut ConstraintStore,
        context: &mut SolveContext,
        session: &mut TypeSession,
    ) -> SolveResult {
        let cause = ConstraintCause::Call(self.call_node_id);
        let callee = session.apply(self.callee.clone(), &mut context.substitutions);
        let returns = session.apply(self.returns.clone(), &mut context.substitutions);

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

                let Some(nominal) = session.lookup_nominal(&sym) else {
                    return SolveResult::Defer(DeferralReason::WaitingOnSymbol(sym));
                };

                let type_args = if nominal.type_params.is_empty() {
                    vec![]
                } else if self.type_args.is_empty() {
                    nominal
                        .type_params
                        .iter()
                        .map(|_| session.new_ty_meta_var(context.level().next()))
                        .collect()
                } else if self.type_args.len() != nominal.type_params.len() {
                    return SolveResult::Err(TypeError::GenericArgCount {
                        expected: nominal.type_params.len() as u8,
                        actual: self.type_args.len() as u8,
                    });
                } else {
                    self.type_args.clone()
                };

                let returns_type = InferTy::Nominal {
                    symbol: sym,
                    type_args,
                };

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
                        InferTy::Error(
                            TypeError::TypeNotFound(format!(
                                "Initializer not found {initializer:?}"
                            ))
                            .into(),
                        )
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

                let group = constraints.copy_group(self.id);
                constraints.wants_equals_at(
                    self.call_node_id,
                    self.returns.clone(),
                    returns_type.clone(),
                    &group,
                );

                match unify(&init_ty, &curry(args, returns_type), context, session) {
                    Ok(metas) => SolveResult::Solved(metas),
                    Err(e) => SolveResult::Err(e.with_cause(cause)),
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
                    Err(e) => SolveResult::Err(e.with_cause(cause)),
                }
            }
            ty => SolveResult::Err(TypeError::CalleeNotCallable(ty.clone())),
        }
    }
}
