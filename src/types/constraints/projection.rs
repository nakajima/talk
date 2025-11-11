use crate::{
    label::Label,
    node_id::NodeID,
    span::Span,
    types::{
        constraints::constraint::ConstraintCause,
        infer_ty::InferTy,
        solve_context::{Solve, SolveContext},
        type_error::TypeError,
        type_operations::apply,
        type_session::TypeSession,
    },
};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Projection {
    pub node_id: NodeID,
    pub base: InferTy,
    pub label: Label,
    pub result: InferTy,
    pub cause: ConstraintCause,
    pub span: Span,
}

impl Projection {
    pub fn solve(
        &self,
        context: &mut SolveContext,
        session: &mut TypeSession,
    ) -> Result<bool, TypeError> {
        let base = apply(self.base.clone(), &mut context.substitutions);
        let result = apply(self.result.clone(), &mut context.substitutions);

        // Try to reduce when base is a concrete nominal
        if let InferTy::Nominal {
            symbol: base_sym, ..
        } = base
        {
            // Find conformance for this base that defines label p.label
            if let Some(conformance) = session
                .type_catalog
                .conformances
                .values()
                .find(|conf| {
                    conf.conforming_id == base_sym
                        && conf.associated_types.contains_key(&self.label)
                })
                .cloned()
            {
                // Get the concrete associated type into this context
                let concrete = conformance.associated_types.get(&self.label).unwrap();

                // result must equal the concrete witness type
                context.wants_mut().equals(
                    result,
                    concrete.clone(),
                    ConstraintCause::Internal,
                    self.span,
                );
                return Ok(true);
            }
        }

        Ok(false)
    }
}
