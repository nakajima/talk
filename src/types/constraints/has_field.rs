use crate::{
    label::Label,
    span::Span,
    types::{
        constraint::ConstraintCause,
        passes::dependencies_pass::SCCResolved,
        row::Row,
        ty::{Level, Ty},
        type_error::TypeError,
        type_operations::{UnificationSubstitutions, apply_row},
        type_session::TypeSession,
        wants::Wants,
    },
};

#[derive(Debug, Clone)]
pub struct HasField {
    pub row: Row,
    pub label: Label,
    pub ty: Ty,
    pub cause: ConstraintCause,
    pub span: Span,
}

impl HasField {
    pub fn solve(
        &self,
        _session: &mut TypeSession<SCCResolved>,
        _level: Level,
        next_wants: &mut Wants,
        substitutions: &mut UnificationSubstitutions,
    ) -> Result<bool, TypeError> {
        match &self.row {
            Row::Empty(..) => Err(TypeError::MemberNotFound(
                self.ty.clone(),
                self.label.to_string(),
            )),
            Row::Param(..) => Err(TypeError::MemberNotFound(
                Ty::Record(Box::new(self.row.clone())),
                self.label.to_string(),
            )),
            Row::Var(..) => {
                // Keep the constraint for the next iteration with the applied row
                next_wants._has_field(
                    apply_row(self.row.clone(), substitutions),
                    self.label.clone(),
                    self.ty.clone(),
                    ConstraintCause::Internal,
                    self.span,
                );
                Ok(false)
            }
            Row::Extend { row, label, ty } => {
                if self.label == *label {
                    next_wants.equals(
                        self.ty.clone(),
                        ty.clone(),
                        ConstraintCause::Internal,
                        self.span,
                    );
                    tracing::trace!("found match for {label:?}");
                    Ok(true)
                } else {
                    next_wants._has_field(
                        *row.clone(),
                        self.label.clone(),
                        self.ty.clone(),
                        ConstraintCause::Internal,
                        self.span,
                    );

                    Ok(true)
                }
            }
        }
    }
}
