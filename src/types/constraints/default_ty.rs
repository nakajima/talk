use crate::node_id::NodeID;
use crate::types::constraint_solver::SolveResult;
use crate::types::solve_context::SolveContext;
use crate::types::type_operations::unify;
use crate::types::type_session::TypeSession;
use crate::types::{
    constraints::{constraint::ConstraintCause, store::ConstraintId},
    infer_ty::InferTy,
};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct DefaultTy {
    pub id: ConstraintId,
    pub node_id: NodeID,
    pub var: InferTy,
    pub ty: InferTy,
    pub allowed: Vec<InferTy>,
    pub cause: ConstraintCause,
}

impl DefaultTy {
    pub fn solve(&self, context: &mut SolveContext, session: &mut TypeSession) -> SolveResult {
        match &self.var {
            InferTy::Var { .. } => match unify(&self.var, &self.ty, context, session) {
                Ok(vars) => SolveResult::Solved(vars),
                Err(e) => SolveResult::Err(e),
            },
            resolved => {
                if self.allowed.iter().any(|ty| ty == resolved) {
                    SolveResult::Solved(Default::default())
                } else {
                    SolveResult::Err(crate::types::type_error::TypeError::invalid_unification(
                        resolved.clone(),
                        self.ty.clone(),
                    ))
                }
            }
        }
    }
}
