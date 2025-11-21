use crate::{
    name_resolution::symbol::Symbol,
    node_id::NodeID,
    span::Span,
    types::{
        constraints::constraint::{Constraint, ConstraintCause},
        infer_ty::InferTy,
        solve_context::{Solve, SolveContext},
        type_error::TypeError,
        type_operations::unify,
        type_session::TypeSession,
    },
};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct InstanceOf {
    pub node_id: NodeID,
    pub var: InferTy,
    pub instance_of: Symbol,
    pub args: Vec<(InferTy, NodeID)>,
    pub cause: ConstraintCause,
    pub span: Span,
}

impl InstanceOf {
    pub fn solve(
        &self,
        context: &mut SolveContext,
        session: &mut TypeSession,
    ) -> Result<bool, TypeError> {
        let Some(entry) = session.lookup(&self.instance_of) else {
            context
                .wants_mut()
                .push(Constraint::InstanceOf(self.clone()));
            return Ok(false);
        };

        let instance = if self.args.is_empty() {
            entry.instantiate(self.node_id, context, session, self.span)
        } else {
            entry
                .instantiate_with_args(
                    self.node_id,
                    &self.args,
                    session,
                    context.level(),
                    context.wants_mut(),
                    self.span,
                )
                .0
        };

        unify(&self.var, &instance, context, session)
    }
}
