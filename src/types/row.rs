use crate::{label::Label, types::ty::Ty};

#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy, PartialOrd, Ord)]
pub struct RowMetaId(u32);
impl From<u32> for RowMetaId {
    fn from(value: u32) -> Self {
        RowMetaId(value)
    }
}

#[derive(Default, Debug, PartialEq)]
pub struct ClosedRow {
    pub labels: Vec<Label>,
    pub values: Vec<Ty>,
}

// TODO: Add Level to Var
#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub enum Row {
    Empty,
    Extend { row: Box<Row>, label: Label, ty: Ty },
    Var(RowMetaId),
}

impl Row {
    pub fn close(&self) -> ClosedRow {
        close(self, ClosedRow::default())
    }
}

fn close(row: &Row, mut closed_row: ClosedRow) -> ClosedRow {
    match row {
        Row::Empty => closed_row,
        Row::Var(_) => panic!("Cannot close var"),
        Row::Extend { row, label, ty } => {
            closed_row.labels.push(label.clone());
            closed_row.values.push(ty.clone());
            close(row, closed_row)
        }
    }
}
