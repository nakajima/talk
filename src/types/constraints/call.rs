use tracing::instrument;

use crate::{
    node_id::NodeID,
    types::{
        constraint_solver::{DeferralReason, SolveResult},
        constraints::{
            constraint::ConstraintCause,
            store::{ConstraintId, ConstraintStore},
        },
        infer_row::InferRow,
        infer_ty::{InferTy, Meta},
        solve_context::{Solve, SolveContext},
        term_environment::EnvEntry,
        type_error::TypeError,
        type_operations::{curry, unify},
        type_session::TypeSession,
    },
};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct CallId(pub(crate) NodeID);

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Call {
    pub id: ConstraintId,
    pub call_id: CallId,
    pub call_node_id: NodeID,
    pub callee_id: NodeID,
    pub callee: InferTy,
    pub args: Vec<InferTy>,
    pub type_args: Vec<InferTy>,
    pub returns: InferTy,
    pub receiver: Option<InferTy>, // If it's a method
    pub effect_context_row: Option<InferRow>,
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
                    let level = context.level().next();
                    nominal
                        .type_params
                        .iter()
                        .map(|param| {
                            if let Some(existing) = session
                                .instantiations_by_call
                                .get(&self.call_id)
                                .and_then(|inst| inst.ty.get(param))
                                .cloned()
                            {
                                return existing;
                            }

                            let var = session.new_ty_meta_var(level);
                            session
                                .instantiations_by_call
                                .entry(self.call_id)
                                .or_default()
                                .ty
                                .insert(*param, var.clone());
                            var
                        })
                        .collect()
                } else if self.type_args.len() != nominal.type_params.len() {
                    return SolveResult::Err(TypeError::GenericArgCount {
                        expected: nominal.type_params.len() as u8,
                        actual: self.type_args.len() as u8,
                    });
                } else {
                    let call_entry = session.instantiations_by_call.entry(self.call_id).or_default();
                    for (param, arg_ty) in nominal.type_params.iter().zip(self.type_args.iter()) {
                        call_entry
                            .ty
                            .entry(*param)
                            .or_insert_with(|| arg_ty.clone());
                    }
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
                        let ty = entry.instantiate(self.callee_id, constraints, context, session);
                        let call_entry =
                            session.instantiations_by_call.entry(self.call_id).or_default();
                        for (param_id, ty) in context.instantiations.ty.iter() {
                            call_entry
                                .ty
                                .entry(*param_id)
                                .or_insert_with(|| ty.clone());
                        }
                        for (row_param_id, row) in context.instantiations.row.iter() {
                            call_entry
                                .row
                                .entry(*row_param_id)
                                .or_insert_with(|| row.clone());
                        }
                        ty
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

                match unify(
                    &init_ty,
                    &curry(args, returns_type, InferRow::Empty.into()),
                    context,
                    session,
                ) {
                    Ok(metas) => SolveResult::Solved(metas),
                    Err(e) => SolveResult::Err(e.with_cause(cause)),
                }
            }
            InferTy::Func(.., effects) => {
                let res = if args.is_empty() {
                    unify(
                        &self.callee,
                        &InferTy::Func(
                            InferTy::Void.into(),
                            self.returns.clone().into(),
                            effects.clone(),
                        ),
                        context,
                        session,
                    )
                } else {
                    unify(
                        &self.callee,
                        &curry(args, self.returns.clone(), effects.clone()),
                        context,
                        session,
                    )
                };

                if let Some(row) = self.effect_context_row.clone() {
                    constraints.wants_row_subset(
                        Some(self.call_node_id),
                        *effects.clone(),
                        row,
                        &context.group_info(),
                    );
                }

                match res {
                    Ok(metas) => SolveResult::Solved(metas),
                    Err(e) => SolveResult::Err(e.with_cause(cause)),
                }
            }
            ty => SolveResult::Err(TypeError::CalleeNotCallable(ty.clone())),
        }
    }
}
