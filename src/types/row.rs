use crate::{
    compiling::module::ModuleId,
    types::{
        infer_row::{ClosedRow, InferRow, InnerRow},
        scheme::ForAll,
        ty::{Specializations, Ty, Typed},
        type_error::TypeError,
    },
};

pub type Row = InnerRow<Typed>;

impl Row {
    pub fn collect_specializations(&self, concrete: &Row) -> Result<Specializations, TypeError> {
        let mut result = Specializations::default();
        match (self, concrete) {
            (Row::Empty, Row::Empty) => (),
            (Row::Param(id), other) => {
                if !matches!(other, Row::Param(..)) {
                    result.row.insert(*id, other.clone());
                }
            }
            (
                Row::Extend {
                    row: lhs_row,
                    ty: lhs_ty,
                    ..
                },
                Row::Extend {
                    row: rhs_row,
                    ty: rhs_ty,
                    ..
                },
            ) => {
                result.ty.extend(lhs_ty.collect_specializations(rhs_ty)?.ty);
                result
                    .row
                    .extend(lhs_row.collect_specializations(rhs_row)?.row);
            }
            _ => return Err(TypeError::SpecializationMismatch),
        }
        Ok(result)
    }
}

fn close(row: &Row, mut closed_row: ClosedRow<Ty>) -> ClosedRow<Ty> {
    #[allow(clippy::panic)]
    match row {
        Row::Empty => closed_row,
        Row::Param(_) => panic!("Cannot close param: {row:?}"),
        Row::Extend { row, label, ty } => {
            closed_row.insert(label.clone(), ty.clone());
            close(row, closed_row)
        }
    }
}
