use crate::{label::Label, types::ty::Ty};

#[derive(PartialEq, Eq, Hash, Clone, Copy, PartialOrd, Ord)]
pub struct RowMetaId(pub u32);
impl From<u32> for RowMetaId {
    fn from(value: u32) -> Self {
        RowMetaId(value)
    }
}

impl std::fmt::Debug for RowMetaId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "π{}", self.0)
    }
}

#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy, PartialOrd, Ord)]
pub struct RowParamId(pub u32);
impl From<u32> for RowParamId {
    fn from(value: u32) -> Self {
        RowParamId(value)
    }
}

#[derive(Default, Debug, PartialEq)]
pub struct ClosedRow {
    pub labels: Vec<Label>,
    pub values: Vec<Ty>,
}

// TODO: Add Level to Var once we support open rows
#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub enum Row {
    Empty,
    Extend { row: Box<Row>, label: Label, ty: Ty },
    Param(RowParamId),
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
        Row::Param(_) => panic!("Cannot close param"),
        Row::Extend { row, label, ty } => {
            closed_row.labels.push(label.clone());
            closed_row.values.push(ty.clone());
            close(row, closed_row)
        }
    }
}
