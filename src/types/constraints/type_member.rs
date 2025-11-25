use tracing::instrument;

use crate::{
    ast::AST,
    label::Label,
    name_resolution::name_resolver::NameResolved,
    node_id::NodeID,
    types::{
        constraint_solver::SolveResult,
        constraints::store::{ConstraintId, ConstraintStore},
        infer_ty::{InferTy, TypeParamId},
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
    #[instrument(skip(constraints, context, session, asts))]
    pub fn solve(
        &self,
        constraints: &mut ConstraintStore,
        context: &mut SolveContext,
        session: &mut TypeSession,
        asts: &[AST<NameResolved>],
    ) -> SolveResult {
        #[warn(clippy::todo)]
        match &self.base {
            InferTy::Var { .. } => todo!(),
            InferTy::Param(type_param_id) => {
                self.lookup_for_type_param(constraints, context, session, asts, *type_param_id)
            }
            InferTy::Rigid(skolem_id) => {
                let Some(InferTy::Param(type_param_id)) =
                    session.skolem_map.get(&InferTy::Rigid(*skolem_id))
                else {
                    unreachable!();
                };

                self.lookup_for_type_param(constraints, context, session, asts, *type_param_id)
            }
            InferTy::Constructor { .. } => todo!(),
            InferTy::Nominal { .. } => todo!(),
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
        asts: &[AST<NameResolved>],
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
            if let Some(child_types) = asts
                .iter()
                .find_map(|ast| ast.phase.child_types.get(&candidate.into()))
                && let Some(child_sym) = child_types.get(&self.name)
            {
                let Some(child_entry) = session.lookup(child_sym) else {
                    return SolveResult::Err(TypeError::TypeNotFound(format!("{child_sym:?}")));
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
