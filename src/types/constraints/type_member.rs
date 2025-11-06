use crate::{
    label::Label,
    span::Span,
    types::{
        constraints::constraint::ConstraintCause,
        infer_ty::{InferTy, Level},
        type_error::TypeError,
        type_operations::{UnificationSubstitutions, apply},
        type_session::TypeSession,
        wants::Wants,
    },
};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct TypeMember {
    pub base: InferTy,
    pub name: Label,
    pub generics: Vec<InferTy>,
    pub result: InferTy,
    pub cause: ConstraintCause,
    pub span: Span,
}

impl TypeMember {
    pub fn solve(
        &self,
        _session: &mut TypeSession,
        _level: Level,
        _next_wants: &mut Wants,
        substitutions: &mut UnificationSubstitutions,
    ) -> Result<bool, TypeError> {
        let _base = apply(self.base.clone(), substitutions);
        Ok(false)
    }
}
