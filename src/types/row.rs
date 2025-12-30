use derive_visitor::{Drive, DriveMut};

use crate::{
    compiling::module::ModuleId,
    label::Label,
    types::{
        infer_row::{ClosedRow, RowParamId},
        scheme::ForAll,
        ty::{SomeType, Ty},
        type_session::TypeDefKind,
    },
};

#[derive(Debug, PartialEq, Eq, Hash, Clone, Drive, DriveMut)]
pub enum Row {
    Empty(#[drive(skip)] TypeDefKind),
    Param(#[drive(skip)] RowParamId),
    Extend {
        row: Box<Row>,
        #[drive(skip)]
        label: Label,
        ty: Ty,
    },
}

impl Row {
    pub fn close(&self) -> ClosedRow<Ty> {
        close(self, ClosedRow::default())
    }

    pub fn collect_foralls(&self) -> Vec<ForAll> {
        let mut result = vec![];
        match self {
            Row::Empty(..) => (),
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
            Row::Empty(v) => Row::Empty(v),
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
        Row::Empty(..) => closed_row,
        Row::Param(_) => panic!("Cannot close param: {row:?}"),
        Row::Extend { row, label, ty } => {
            closed_row.insert(label.clone(), ty.clone());
            close(row, closed_row)
        }
    }
}
