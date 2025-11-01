use crate::{
    label::Label,
    span::Span,
    types::{
        constraints::constraint::ConstraintCause,
        infer_row::InferRow,
        infer_ty::{InferTy, Level},
        type_error::TypeError,
        type_operations::UnificationSubstitutions,
        type_session::TypeSession,
        wants::Wants,
    },
};

#[derive(Debug, Clone, PartialEq)]
pub struct HasField {
    pub row: InferRow,
    pub label: Label,
    pub ty: InferTy,
    pub cause: ConstraintCause,
    pub span: Span,
}

impl HasField {
    pub fn solve(
        &self,
        _session: &mut TypeSession,
        _level: Level,
        next_wants: &mut Wants,
        _substitutions: &mut UnificationSubstitutions,
    ) -> Result<bool, TypeError> {
        match &self.row {
            InferRow::Empty(..) => Err(TypeError::MemberNotFound(
                self.ty.clone(),
                self.label.to_string(),
            )),
            InferRow::Param(..) => Err(TypeError::MemberNotFound(
                InferTy::Record(Box::new(self.row.clone())),
                self.label.to_string(),
            )),
            InferRow::Var(..) => {
                // Keep the constraint for the next iteration with the applied row
                next_wants._has_field(
                    self.row.clone(),
                    self.label.clone(),
                    self.ty.clone(),
                    ConstraintCause::Internal,
                    self.span,
                );
                Ok(false)
            }
            InferRow::Extend { row, label, ty } => {
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
