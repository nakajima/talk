use crate::{
    label::Label,
    span::Span,
    types::{
        constraints::constraint::ConstraintCause,
        passes::dependencies_pass::SCCResolved,
        ty::{Level, Ty},
        type_error::TypeError,
        type_operations::{UnificationSubstitutions, apply},
        type_session::TypeSession,
        wants::Wants,
    },
};

#[derive(Debug, Clone)]
pub struct TypeMember {
    pub base: Ty,
    pub name: Label,
    pub generics: Vec<Ty>,
    pub result: Ty,
    pub cause: ConstraintCause,
    pub span: Span,
}

impl TypeMember {
    pub fn solve(
        &self,
        _session: &mut TypeSession<SCCResolved>,
        _level: Level,
        _next_wants: &mut Wants,
        substitutions: &mut UnificationSubstitutions,
    ) -> Result<bool, TypeError> {
        let base = apply(self.base.clone(), substitutions);
        println!("BASE: {base:?}");
        Ok(false)
    }
}
