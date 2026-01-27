use tracing::instrument;

use crate::{
    node_id::NodeID,
    types::{
        constraint_solver::{DeferralReason, SolveResult},
        constraints::{
            constraint::ConstraintCause,
            store::{ConstraintId, ConstraintStore},
        },
        infer_row::Row,
        infer_ty::{Meta, Ty},
        solve_context::SolveContext,
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
    pub callee: Ty,
    pub callee_type: Ty,
    pub args: Vec<Ty>,
    pub type_args: Vec<Ty>,
    pub returns: Ty,
    pub receiver: Option<Ty>, // If it's a method
    pub effect_context_row: Row,
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
        let callee = session.apply(&self.callee, &mut context.substitutions_mut());
        let returns = session.apply(&self.returns, &mut context.substitutions_mut());

        if let Ty::Var { id, .. } = &callee {
            tracing::trace!(
                "unable to determine callee type: {:?}, substitutions: {returns:?}",
                self.callee
            );

            // For unqualified variant calls like `.foo(123)`, if we know the return type
            // is a Nominal and we have an unknown receiver, unify them since the receiver
            // of a variant constructor is the same type as its return value.
            if let Some(receiver_ty) = &self.receiver {
                let applied_receiver =
                    session.apply(receiver_ty, &mut context.substitutions_mut());
                if let Ty::Var { .. } = applied_receiver
                    && let Ty::Nominal { .. } = &returns
                    && let Ok(metas) = unify(receiver_ty, &returns, context, session)
                {
                    return SolveResult::Solved(metas);
                }
            }

            // We don't know the callee yet, defer
            return SolveResult::Defer(DeferralReason::WaitingOnMeta(Meta::Ty(*id)));
        }

        let mut args = self.args.to_vec();

        match &self.callee {
            Ty::Constructor { name, box ret, .. } => {
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

                let returns_type = Ty::Nominal {
                    symbol: sym,
                    type_args,
                };

                constraints.wants_equals(ret.clone(), returns_type.clone());

                // TODO: Figure out if we're dealing with a struct vs an enum here and be more explicit.
                // This is ok for now since enums can't have initializers and structs always have them.
                let init_ty = if let Some(initializer) = session
                    .lookup_initializers(&sym)
                    .and_then(|i| i.values().next().copied())
                {
                    args.insert(0, returns_type.clone());

                    if let Some(entry) = session.lookup(&initializer) {
                        if !self.type_args.is_empty() {
                            // When explicit type args are provided, use instantiate_with_args
                            // to constrain the init's type params to match
                            let type_arg_pairs: Vec<_> = self
                                .type_args
                                .iter()
                                .cloned()
                                .map(|ty| (ty, self.callee_id))
                                .collect();
                            let (ty, _) = entry.instantiate_with_args(
                                self.callee_id,
                                &type_arg_pairs,
                                session,
                                context,
                                constraints,
                            );
                            ty
                        } else {
                            entry.instantiate(self.callee_id, constraints, context, session)
                        }
                    } else {
                        Ty::Error(
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
                        _ => Ty::Error(
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

                let mut metas = vec![];
                match unify(&init_ty, &self.callee_type, context, session) {
                    Ok(vars) => metas.extend(vars),
                    Err(e) => return SolveResult::Err(e.with_cause(cause)),
                }

                match unify(
                    &init_ty,
                    &curry(args, returns_type, Row::Empty.into()),
                    context,
                    session,
                ) {
                    Ok(vars) => metas.extend(vars),
                    Err(e) => return SolveResult::Err(e.with_cause(cause)),
                }

                SolveResult::Solved(metas)
            }
            Ty::Func(.., effects) => {
                let reversed = self.callee.clone().mapping(
                    &mut |t| {
                        if let Ty::Var { id, .. } = t
                            && let Some(param) = session.reverse_instantiations.ty.get(&id)
                        {
                            return param.clone();
                        }

                        t
                    },
                    &mut |r| r,
                );

                unify(&reversed, &self.callee_type, context, session).ok();

                let res = if args.is_empty() {
                    unify(
                        &self.callee,
                        &Ty::Func(
                            Ty::Void.into(),
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

                constraints.wants_row_subset(
                    Some(self.call_node_id),
                    *effects.clone(),
                    self.effect_context_row.clone(),
                    &context.group_info(),
                );

                match res {
                    Ok(metas) => SolveResult::Solved(metas),
                    Err(e) => SolveResult::Err(e.with_cause(cause)),
                }
            }
            ty => SolveResult::Err(TypeError::CalleeNotCallable(ty.clone())),
        }
    }
}
