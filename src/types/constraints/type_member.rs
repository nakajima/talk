use itertools::Itertools;
use tracing::instrument;

use crate::{
    label::Label,
    name_resolution::symbol::Symbol,
    node_id::NodeID,
    types::{
        constraint_solver::{DeferralReason, SolveResult},
        constraints::store::{ConstraintId, ConstraintStore},
        infer_ty::{InferTy, Meta, TypeParamId},
        predicate::Predicate,
        solve_context::SolveContext,
        type_error::TypeError,
        type_operations::unify,
        type_session::TypeSession,
    },
};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct TypeMember {
    pub id: ConstraintId,
    pub base: InferTy,
    pub name: Label,
    pub node_id: NodeID,
    pub generics: Vec<InferTy>,
    pub result: InferTy,
}

impl TypeMember {
    #[instrument(skip(constraints, context, session,))]
    pub fn solve(
        &self,
        constraints: &mut ConstraintStore,
        context: &mut SolveContext,
        session: &mut TypeSession,
    ) -> SolveResult {
        self.solve_for(&self.base, constraints, context, session)
    }

    fn solve_for(
        &self,
        ty: &InferTy,
        constraints: &mut ConstraintStore,
        context: &mut SolveContext,
        session: &mut TypeSession,
    ) -> SolveResult {
        match ty {
            InferTy::Var { id, .. } => {
                SolveResult::Defer(DeferralReason::WaitingOnMeta(Meta::Ty(*id)))
            }
            InferTy::Param(type_param_id) => {
                self.lookup_for_type_param(constraints, context, session, *type_param_id)
            }
            InferTy::Rigid(skolem_id) => {
                let Some(InferTy::Param(type_param_id)) =
                    session.skolem_map.get(&InferTy::Rigid(*skolem_id))
                else {
                    unreachable!();
                };

                self.lookup_for_type_param(constraints, context, session, *type_param_id)
            }
            #[allow(clippy::todo)]
            InferTy::Constructor { .. } => todo!(),
            #[allow(clippy::todo)]
            InferTy::Nominal { symbol, type_args } => {
                if let Some(children) = session.type_catalog.child_types.get(symbol)
                    && let Some(child_sym) = children.get(&self.name).copied()
                    && let Some(ty) = session.lookup(&child_sym)
                {
                    if !type_args.is_empty() {
                        let ty = ty
                            .instantiate_with_args(
                                self.node_id,
                                type_args
                                    .iter()
                                    .map(|a| (a.clone(), NodeID::SYNTHESIZED))
                                    .collect_vec()
                                    .as_slice(),
                                session,
                                context,
                                constraints,
                            )
                            .0;
                        match unify(&ty, &self.result, context, session) {
                            Ok(vars) => return SolveResult::Solved(vars),
                            Err(e) => return SolveResult::Err(e),
                        }
                    }
                    self.solve_for(&ty._as_ty(), constraints, context, session)
                } else {
                    SolveResult::Err(TypeError::TypeNotFound(format!(
                        "Did not find child type {symbol:?}.{}",
                        self.name
                    )))
                }
            }
            _ => SolveResult::Err(TypeError::TypeNotFound(format!(
                "Could not find child type {:?} for {:?}",
                self.name, self.base
            ))),
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn lookup_for_type_param(
        &self,
        constraints: &mut ConstraintStore,
        context: &mut SolveContext,
        session: &mut TypeSession,
        type_param_id: TypeParamId,
    ) -> SolveResult {
        let mut candidates = vec![];
        for given in &context.givens {
            if let Predicate::Conforms {
                param, protocol_id, ..
            } = given
                && param == &type_param_id
            {
                candidates.push(protocol_id);
            };
        }

        for candidate in candidates {
            if let Some(child_types) = session
                .resolved_names
                .child_types
                .get(&Symbol::Protocol(*candidate))
                .cloned()
                && let Some(child_sym) = child_types.get(&self.name)
            {
                let Some(child_entry) = session.lookup(child_sym) else {
                    return SolveResult::Err(TypeError::TypeNotFound(format!(
                        "Child entry not found for type member {child_sym:?}"
                    )));
                };

                let child_ty = child_entry.instantiate(self.node_id, constraints, context, session);
                return match unify(&child_ty, &self.result, context, session) {
                    Ok(metas) => SolveResult::Solved(metas),
                    Err(e) => SolveResult::Err(e),
                };
            };
        }

        SolveResult::Err(TypeError::TypeNotFound(format!(
            "{:?}.{:?}",
            self.base, self.name
        )))
    }
}
