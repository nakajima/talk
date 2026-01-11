use derive_visitor::{Drive, DriveMut};

use crate::{
    compiling::module::ModuleId,
    label::Label,
    types::{
        infer_row::{ClosedRow, RowMetaId, RowParamId},
        scheme::ForAll,
        ty::{BaseRow, RowType, SomeType, Ty},
    },
};

#[derive(Debug, PartialEq, Eq, Hash, Clone, Drive, DriveMut)]
pub enum Row {
    Empty,
    Param(#[drive(skip)] RowParamId),
    Extend {
        row: Box<Row>,
        #[drive(skip)]
        label: Label,
        ty: Ty,
    },
}

impl RowType for Row {
    type T = Ty;

    fn base(&self) -> BaseRow<Ty> {
        match self.clone() {
            Self::Empty => BaseRow::Empty,
            Self::Param(id) => BaseRow::Param(id),
            Self::Extend { row, label, ty } => BaseRow::Extend {
                row: row.base().into(),
                label,
                ty,
            },
        }
    }

    fn empty() -> Self {
        Self::Empty
    }

    fn param(id: RowParamId) -> Self {
        Self::Param(id)
    }

    fn var(_id: RowMetaId) -> Self {
        unreachable!("cannot convert row meta");
    }

    fn extend(row: Self, label: Label, ty: Ty) -> Self {
        Self::Extend {
            row: row.into(),
            label,
            ty,
        }
    }
}

impl Row {
    pub fn close(&self) -> ClosedRow<Ty> {
        close(self, ClosedRow::default())
    }

    pub fn collect_foralls(&self) -> Vec<ForAll> {
        let mut result = vec![];
        match self {
            Row::Empty => (),
            Row::Param(id) => {
                result.push(ForAll::Row(*id));
            }
            Row::Extend { row, ty, .. } => {
                result.extend(ty.collect_foralls());
                result.extend(row.collect_foralls());
            }
        }
        result
    }

    pub fn import(self, module_id: ModuleId) -> Self {
        match self {
            Row::Empty => Row::Empty,
            Row::Param(v) => Row::Param(v),
            Row::Extend { box row, label, ty } => Row::Extend {
                row: row.import(module_id).into(),
                label,
                ty: ty.import(module_id),
            },
        }
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
