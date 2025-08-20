use std::{collections::BTreeMap, fmt::Display};

use derive_visitor::DriveMut;

use crate::{
    type_checker::TypeError,
    types::{
        ty::{Ty, TypeParameter},
        type_var::TypeVar,
        type_var_context::{RowVar, TypeVarContext},
        visitors::inference_visitor::Substitutions,
    },
};

#[derive(Debug)]
pub enum Direction {
    Left,
    Right,
}

#[derive(Debug, Hash, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum Label {
    String(String),
    Int(u32),
}

impl<T: Into<String>> From<T> for Label {
    fn from(value: T) -> Self {
        Label::String(value.into())
    }
}

impl Display for Label {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Label::String(string) => write!(f, "{string}"),
            Label::Int(i) => write!(f, "{i}"),
        }
    }
}

#[derive(Debug, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct RowCombination {
    pub left: Row,
    pub right: Row,
    pub goal: Row,
}

#[derive(Debug, Hash, Clone, PartialEq, Eq, DriveMut, PartialOrd, Ord)]
pub enum Row {
    Open(#[drive(skip)] RowVar),
    Closed(ClosedRow),
}

#[derive(Debug, Default, Hash, Clone, PartialEq, Eq, DriveMut, PartialOrd, Ord)]
pub struct ClosedRow {
    // Sorted lexographically
    #[drive(skip)]
    pub fields: Vec<Label>,
    // One type for each field in fields
    pub values: Vec<Ty>,
}

impl Row {
    pub fn instantiate_row(
        &self,
        _context: &mut TypeVarContext,
        substitutions: &mut BTreeMap<TypeParameter, TypeVar>,
    ) -> Row {
        match self {
            Row::Closed(ClosedRow { fields, values }) => Row::Closed(ClosedRow {
                fields: fields.clone(),
                values: values
                    .iter()
                    .map(|v| v.instantiate(_context, substitutions))
                    .collect(),
            }),
            Row::Open(var) => {
                // For open rows, keep the same row variable
                // The fields are already defined for this row variable, and instantiation
                // only affects the types of those fields (via substitutions), not the structure
                Row::Open(*var)
            }
        }
    }

    pub(crate) fn substituting(self, substitutions: &Substitutions) -> Result<Row, TypeError> {
        let row = match self {
            Row::Open(var) => {
                if let Some(new_var) = substitutions.get_row(&var) {
                    Row::Open(*new_var)
                } else {
                    self
                }
            }
            Row::Closed(ClosedRow { fields, values }) => {
                let mut new_values = vec![];
                for value in values {
                    new_values.push(value.substituting(substitutions)?);
                }
                Row::Closed(ClosedRow {
                    fields,
                    values: new_values,
                })
            }
        };

        Ok(row)
    }

    pub fn canonical_type_vars(&self) -> Vec<TypeVar> {
        match self {
            Row::Open(_) => vec![],
            Row::Closed(ClosedRow { values, .. }) => {
                let mut result = vec![];
                for value in values {
                    result.extend(value.canonical_type_vars())
                }
                result
            }
        }
    }
}
