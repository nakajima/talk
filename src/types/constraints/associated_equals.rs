use crate::{
    name_resolution::symbol::{AssociatedTypeId, TypeId},
    span::Span,
    types::{
        constraints::constraint::ConstraintCause,
        passes::dependencies_pass::SCCResolved,
        ty::{Level, Ty},
        type_error::TypeError,
        type_operations::UnificationSubstitutions,
        type_session::TypeSession,
        wants::Wants,
    },
};

#[derive(Debug, Clone)]
pub struct AssociatedEquals {
    pub subject: Ty,
    pub protocol_id: TypeId,
    pub associated_type_id: AssociatedTypeId,
    pub output: Ty,
    pub cause: ConstraintCause,
    pub span: Span,
}

impl AssociatedEquals {
    pub fn solve(
        &self,
        _session: &mut TypeSession<SCCResolved>,
        _level: Level,
        _next_wants: &mut Wants,
        _substitutions: &mut UnificationSubstitutions,
    ) -> Result<bool, TypeError> {
        todo!()
    }
}
