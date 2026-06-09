use indexmap::IndexMap;

use crate::{
    compiling::module::ModuleId,
    name_resolution::symbol::Symbol,
    types::{
        infer_row::{Row, RowParamId},
        infer_ty::Ty,
    },
};

#[derive(Default, Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct TypeArgs {
    pub ty: IndexMap<Symbol, Ty>,
    pub row: IndexMap<RowParamId, Row>,
}

impl TypeArgs {
    pub fn is_empty(&self) -> bool {
        self.ty.is_empty() && self.row.is_empty()
    }

    pub fn extend(&mut self, other: TypeArgs) {
        self.ty.extend(other.ty);
        self.row.extend(other.row);
    }

    pub fn apply(&self, ty: Ty) -> Ty {
        ty.mapping(
            &mut |t| {
                if let Ty::Param(id, _) = t
                    && let Some(replacement) = self.ty.get(&id)
                {
                    replacement.clone()
                } else {
                    t
                }
            },
            &mut |r| self.apply_row(r),
        )
    }

    pub fn apply_row(&self, row: Row) -> Row {
        match row {
            Row::Empty => Row::Empty,
            Row::Extend { row, label, ty } => Row::Extend {
                row: self.apply_row(*row).into(),
                label,
                ty: self.apply(ty),
            },
            Row::Param(id) => self.row.get(&id).cloned().unwrap_or(Row::Param(id)),
            Row::Var(id) => Row::Var(id),
        }
    }

    pub fn import(self, module_id: ModuleId) -> Self {
        Self {
            ty: self
                .ty
                .into_iter()
                .map(|(param, ty)| (param.import(module_id), ty.import(module_id)))
                .collect(),
            row: self
                .row
                .into_iter()
                .map(|(param, row)| (param, row.import(module_id)))
                .collect(),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Instantiated<T> {
    pub value: T,
    pub type_args: TypeArgs,
}

impl<T> Instantiated<T> {
    pub fn new(value: T, type_args: TypeArgs) -> Self {
        Self { value, type_args }
    }
}
