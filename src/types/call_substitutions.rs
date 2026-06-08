use std::collections::BTreeMap;

use rustc_hash::FxHashMap;

use crate::{
    compiling::module::ModuleId,
    name_resolution::symbol::Symbol,
    node_id::NodeID,
    types::{
        infer_row::{Row, RowParamId},
        infer_ty::Ty,
    },
};

#[derive(Debug, PartialEq, Clone, serde::Serialize, serde::Deserialize, Default)]
pub struct TrackedInstantiations {
    pub ty: FxHashMap<NodeID, FxHashMap<Symbol, Ty>>,
    pub row: FxHashMap<NodeID, FxHashMap<RowParamId, Row>>,
}

impl TrackedInstantiations {
    pub fn insert_ty(&mut self, id: NodeID, param: Symbol, ty: Ty) {
        self.ty.entry(id).or_default().insert(param, ty);
    }

    pub fn insert_row(&mut self, id: NodeID, param: RowParamId, row: Row) {
        self.row.entry(id).or_default().insert(param, row);
    }
}

#[derive(Default, Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct CallSubstitutions {
    pub ty: BTreeMap<Symbol, Ty>,
    pub row: BTreeMap<RowParamId, Row>,
}

impl CallSubstitutions {
    pub fn is_empty(&self) -> bool {
        self.ty.is_empty() && self.row.is_empty()
    }

    pub fn extend(&mut self, other: CallSubstitutions) {
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
            &mut |r| {
                if let Row::Param(id) = r
                    && let Some(replacement) = self.row.get(&id)
                {
                    replacement.clone()
                } else {
                    r
                }
            },
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
