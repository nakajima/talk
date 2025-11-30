use std::str::FromStr;

use crate::{
    ir::ir_error::IRError,
    label::Label,
    name_resolution::symbol::Symbol,
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
    Record(Option<Symbol>, Vec<IrTy>),
    RawPtr,
    Byte,
    Void,
    Buffer(u32),
}

impl IrTy {
    pub fn bytes_len(&self) -> usize {
        match self {
            IrTy::Int => 8,
            IrTy::Float => 8,
            IrTy::Bool => 1,
            IrTy::Func(args, ret) => {
                ret.bytes_len() + args.iter().map(|a| a.bytes_len()).sum::<usize>()
            }
            IrTy::Record(_sym, fields) => fields.iter().map(|a| a.bytes_len()).sum::<usize>(), // Including space for a symbol
            IrTy::RawPtr => 8,
            IrTy::Byte => 1,
            IrTy::Void => 0,
            IrTy::Buffer(len) => *len as usize,
        }
    }
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

        // record: {...}
        if s.starts_with('{') && s.ends_with('}') {
            let inner = &s[1..s.len() - 1].trim();

            // record: "{ a, b, c }"
            let mut map: Vec<IrTy> = Vec::new();
            for part in split_simple(inner, ',').into_iter() {
                // adjust this line if your Label has a different constructor
                map.push(part.parse()?);
            }
            return Ok(IrTy::Record(None, map));
        }

        Err(IRError::CouldNotParse(format!("no IrTy for {s:?}")))
    }
}

impl std::fmt::Display for IrTy {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            IrTy::Int => write!(f, "int"),
            IrTy::Float => write!(f, "float"),
            IrTy::Bool => write!(f, "bool"),
            IrTy::Byte => write!(f, "byte"),
            IrTy::RawPtr => write!(f, "rawptr"),
            IrTy::Func(items, ir_ty) => write!(
                f,
                "({}) -> {}",
                items
                    .iter()
                    .map(|i| format!("{i}"))
                    .collect::<Vec<_>>()
                    .join(", "),
                ir_ty
            ),
            IrTy::Record(sym, fields) => {
                let mut items = vec![];
                for item in fields {
                    items.push(format!("{item}"));
                }
                write!(
                    f,
                    "{{ {}{} }}",
                    if let Some(sym) = sym {
                        format!("{sym}")
                    } else {
                        "".to_string()
                    },
                    items.join(", ")
                )
            }
            IrTy::Buffer(len) => write!(f, "buf({len})"),
            IrTy::Void => write!(f, "void"),
        }
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
            IrTy::RawPtr => Ty::RawPtr,
            IrTy::Byte => Ty::Byte,
            IrTy::Buffer(..) => Ty::RawPtr,
            IrTy::Func(params, box ret) => params
                .into_iter()
                .collect::<Vec<_>>()
                .into_iter()
                .rfold(ret.into(), |acc, p| {
                    Ty::Func(Box::new(p.into()), Box::new(acc))
                }),
            IrTy::Record(sym, tys) => {
                let mut row = Row::Empty(TypeDefKind::Struct);
                for (i, ty) in tys.iter().enumerate() {
                    row = Row::Extend {
                        row: row.into(),
                        label: Label::Positional(i),
                        ty: ty.clone().into(),
                    }
                }

                Ty::Record(sym, row.into())
            }
            IrTy::Void => Ty::Void,
        }
    }
}
