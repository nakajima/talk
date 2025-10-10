use std::str::FromStr;

use indexmap::IndexMap;

use crate::{
    ir::ir_error::IRError,
    label::Label,
    types::{row::Row, ty::Ty, type_session::TypeDefKind},
};

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum IrTy {
    Int,
    Float,
    Bool,
    // (123, true) -> false
    Func(Vec<IrTy>, Box<IrTy>),
    // { 123, 4.56, true }
    Record(IndexMap<Label, IrTy>),
    // { 1 ; 123, true }
    Enum { tag: u16, values: Vec<IrTy> },
    Void,
}

impl FromStr for IrTy {
    type Err = IRError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        if s == "int" {
            return Ok(IrTy::Int);
        }

        if s == "float" {
            return Ok(IrTy::Float);
        }

        if s == "bool" {
            return Ok(IrTy::Bool);
        }

        if s == "void" {
            return Ok(IrTy::Void);
        }

        // function: (a, b, c) -> r
        if let Some((lhs, rhs)) = s.split_once("->") {
            let args_str = lhs.trim().trim_start_matches('(').trim_end_matches(')');
            let args = split_simple(args_str, ',')
                .into_iter()
                .map(|t| {
                    t.parse()
                        .map_err(|e| IRError::CouldNotParse(format!("{e:?}")))
                })
                .collect::<Result<Vec<_>, IRError>>()?;
            let ret = Box::new(rhs.trim().parse()?);
            return Ok(IrTy::Func(args, ret));
        }

        // record or enum: {...}
        if s.starts_with('{') && s.ends_with('}') {
            let inner = &s[1..s.len() - 1].trim();

            // enum: "{ <tag> ; a, b, c }"
            if let Some((tag_part, vals_part)) = inner.split_once(';') {
                let tag: u16 = tag_part
                    .trim()
                    .parse()
                    .map_err(|e| IRError::CouldNotParse(format!("{e:?}")))?;
                let values = split_simple(vals_part, ',')
                    .into_iter()
                    .map(|t| {
                        t.parse()
                            .map_err(|e| IRError::CouldNotParse(format!("{e:?}")))
                    })
                    .collect::<Result<Vec<_>, IRError>>()?;
                return Ok(IrTy::Enum { tag, values });
            }

            // record: "{ a, b, c }"  (labels ignored at IR; use positional)
            let mut map: IndexMap<Label, IrTy> = IndexMap::new();
            for (i, part) in split_simple(inner, ',').into_iter().enumerate() {
                // adjust this line if your Label has a different constructor
                map.insert(Label::from(i.to_string()), part.parse()?);
            }
            return Ok(IrTy::Record(map));
        }

        Err(IRError::CouldNotParse(format!("no IrTy for {s:?}")))
    }
}

fn split_simple(s: &str, sep: char) -> Vec<&str> {
    s.split(sep)
        .map(|t| t.trim())
        .filter(|t| !t.is_empty())
        .collect()
}

impl From<IrTy> for Ty {
    fn from(value: IrTy) -> Self {
        match value {
            IrTy::Int => Ty::Int,
            IrTy::Float => Ty::Float,
            IrTy::Bool => Ty::Bool,
            IrTy::Func(params, box ret) => params
                .into_iter()
                .collect::<Vec<_>>()
                .into_iter()
                .rfold(ret.into(), |acc, p| {
                    Ty::Func(Box::new(p.into()), Box::new(acc))
                }),
            IrTy::Record(tys) => {
                let mut row = Row::Empty(TypeDefKind::Struct);
                for (label, ty) in tys {
                    row = Row::Extend {
                        row: row.into(),
                        label,
                        ty: ty.into(),
                    }
                }

                Ty::Record(row.into())
            }
            IrTy::Enum { .. } => {
                unimplemented!()
            }
            IrTy::Void => Ty::Void,
        }
    }
}
