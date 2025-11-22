use crate::{
    name_resolution::symbol::ProtocolId,
    span::Span,
    types::{
        constraints::constraint::Constraint,
        infer_ty::InferTy,
        solve_context::{Solve, SolveContext},
        type_catalog::ConformanceKey,
        type_error::TypeError,
        type_session::TypeSession,
    },
};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Conforms {
    pub ty: InferTy,
    pub protocol_id: ProtocolId,
    pub span: Span,
}

impl Conforms {
    pub fn solve(
        &self,
        context: &mut SolveContext,
        session: &mut TypeSession,
        last_try: bool,
    ) -> Result<bool, TypeError> {
        let symbol = match &self.ty {
            InferTy::Var { .. } => {
                if last_try {
                    // Let it just be generalized
                } else {
                    // Not ready
                    context.wants_mut().push(Constraint::Conforms(self.clone()));
                }

                return Ok(false);
            }
            InferTy::Primitive(symbol) => *symbol,
            InferTy::Nominal { symbol, .. } => *symbol,
            _ => {
                return Err(TypeError::TypesCannotConform {
                    ty: self.ty.clone(),
                    protocol_id: self.protocol_id,
                });
            }
        };

        if !session
            .type_catalog
            .conformances
            .contains_key(&ConformanceKey {
                conforming_id: symbol,
                protocol_id: self.protocol_id,
            })
        {
            return Err(TypeError::TypesDoesNotConform {
                symbol,
                protocol_id: self.protocol_id,
            });
        }

        Ok(true)
    }
}
