use crate::{
    label::Label,
    span::Span,
    types::{
        constraints::constraint::ConstraintCause, infer_row::InferRow, infer_ty::InferTy,
        solve_context::SolveContext, type_error::TypeError,
    },
};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct HasField {
    pub row: InferRow,
    pub label: Label,
    pub ty: InferTy,
    pub cause: ConstraintCause,
    pub span: Span,
}

impl HasField {
    pub fn solve(&self, context: &mut SolveContext) -> Result<bool, TypeError> {
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
                context.wants._has_field(
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
                    context.wants.equals(
                        self.ty.clone(),
                        ty.clone(),
                        ConstraintCause::Internal,
                        self.span,
                    );
                    tracing::trace!("found match for {label:?}");
                    Ok(true)
                } else {
                    context.wants._has_field(
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
