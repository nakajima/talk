use crate::{
    name_resolution::symbol::ProtocolId,
    types::{
        constraint_solver::{DeferralReason, SolveResult},
        constraints::store::ConstraintId,
        infer_ty::{InferTy, Meta},
        solve_context::SolveContext,
        type_catalog::ConformanceKey,
        type_error::TypeError,
        type_session::TypeSession,
    },
};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Conforms {
    pub id: ConstraintId,
    pub ty: InferTy,
    pub protocol_id: ProtocolId,
}

impl Conforms {
    pub fn solve(
        &self,
        context: &mut SolveContext,
        session: &mut TypeSession,
        last_try: bool,
    ) -> SolveResult {
        let symbol = match &self.ty {
            InferTy::Var { id, .. } => {
                return SolveResult::Defer(DeferralReason::WaitingOnMeta(Meta::Ty(*id)));
            }
            InferTy::Primitive(symbol) => *symbol,
            InferTy::Nominal { symbol, .. } => *symbol,
            _ => {
                return SolveResult::Err(TypeError::TypesCannotConform {
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
            return SolveResult::Err(TypeError::TypesDoesNotConform {
                symbol,
                protocol_id: self.protocol_id,
            });
        }

        SolveResult::Solved(Default::default())
    }
}
