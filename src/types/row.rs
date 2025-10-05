use crate::{
    label::Label,
    types::{
        infer_row::{ClosedRow, RowParamId},
        ty::Ty,
    },
};

#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub enum Row {
    Empty,
    Param(RowParamId),
    Extend { row: Box<Row>, label: Label, ty: Ty },
}

impl Row {
    pub fn close(&self) -> ClosedRow<Ty> {
        close(self, ClosedRow::default())
    }
}

fn close(row: &Row, mut closed_row: ClosedRow<Ty>) -> ClosedRow<Ty> {
    match row {
        Row::Empty => closed_row,
        Row::Param(_) => panic!("Cannot close param"),
        Row::Extend { row, label, ty } => {
            closed_row.insert(label.clone(), ty.clone());
            close(row, closed_row)
        }
    }
}
