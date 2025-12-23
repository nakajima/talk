use std::hash::Hash;

use derive_visitor::{Drive, DriveMut};
use indexmap::IndexSet;

use crate::{
    compiling::module::ModuleId,
    name::Name,
    name_resolution::symbol::Symbol,
    types::{
        infer_ty::{InferTy, TypeParamId},
        row::Row,
        scheme::ForAll,
    },
};

pub trait SomeType: std::fmt::Debug + PartialEq + Clone + Eq + Hash + Drive + DriveMut {
    type RowType: PartialEq + Clone + std::fmt::Debug;
    fn void() -> Self;
    fn contains_var(&self) -> bool;
}

impl SomeType for Ty {
    type RowType = Row;

    fn void() -> Self {
        Ty::Void
    }

    fn contains_var(&self) -> bool {
        false
    }
}

#[derive(Debug, PartialEq, Eq, Hash, Clone, Drive, DriveMut)]
pub enum Ty {
    Primitive(#[drive(skip)] Symbol),
    Param(#[drive(skip)] TypeParamId),
    Constructor {
        #[drive(skip)]
        name: Name,
        params: Vec<Ty>,
        ret: Box<Ty>,
    },

    Func(Box<Ty>, Box<Ty>),
    Tuple(Vec<Ty>),
    Record(#[drive(skip)] Option<Symbol>, Box<Row>),

    // Nominal types (we look up their information from the TypeCatalog)
    Nominal {
        #[drive(skip)]
        symbol: Symbol,
        type_args: Vec<Ty>,
    },
}

impl std::fmt::Display for Ty {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Ty::Primitive(symbol) => match *symbol {
                Symbol::Int => write!(f, "Int"),
                Symbol::Float => write!(f, "Float"),
                Symbol::Bool => write!(f, "Bool"),
                Symbol::Void => write!(f, "Void"),
                Symbol::RawPtr => write!(f, "RawPtr"),
                _ => write!(f, "{symbol}"),
            },
            Ty::Param(type_param_id) => write!(f, "{:?}", type_param_id),
            Ty::Constructor { name, .. } => {
                write!(f, "{}", name.name_str())
            }
            Ty::Func(param, ret) => {
                write!(
                    f,
                    "({}) -> {ret}",
                    param
                        .clone()
                        .uncurry_params()
                        .iter()
                        .map(|p| format!("{p}"))
                        .collect::<Vec<_>>()
                        .join(", "),
                )
            }
            Ty::Tuple(items) => {
                write!(
                    f,
                    "({})",
                    items
                        .iter()
                        .map(|p| format!("{p}"))
                        .collect::<Vec<_>>()
                        .join(", ")
                )
            }
            Ty::Record(.., row) => write!(
                f,
                "{{ {} }}",
                row.close()
                    .iter()
                    .map(|(k, v)| format!("{k}: {v}"))
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
            Ty::Nominal { symbol, .. } => {
                write!(f, "Nominal({symbol})")
            }
        }
    }
}

#[allow(non_upper_case_globals)]
#[allow(non_snake_case)]
impl Ty {
    pub const Int: Ty = Ty::Primitive(Symbol::Int);
    pub const Float: Ty = Ty::Primitive(Symbol::Float);
    pub const Bool: Ty = Ty::Primitive(Symbol::Bool);
    pub const Void: Ty = Ty::Primitive(Symbol::Void);
    pub const Byte: Ty = Ty::Primitive(Symbol::Byte);
    pub const RawPtr: Ty = Ty::Primitive(Symbol::RawPtr);
    pub fn String() -> Ty {
        Ty::Nominal {
            symbol: Symbol::String,
            type_args: Default::default(),
        }
    }
    pub fn Array(t: Ty) -> Ty {
        InferTy::Array(t.into()).into()
    }

    pub fn collect_foralls(&self) -> IndexSet<ForAll> {
        let mut result: IndexSet<ForAll> = Default::default();
        match self {
            Ty::Primitive(..) => (),
            Ty::Param(id) => {
                result.insert(ForAll::Ty(*id));
            }
            Ty::Constructor { params, ret, .. } => {
                for param in params {
                    result.extend(param.collect_foralls());
                }
                result.extend(ret.collect_foralls());
            }
            Ty::Func(param, ret) => {
                result.extend(param.collect_foralls());
                result.extend(ret.collect_foralls());
            }
            Ty::Tuple(items) => {
                for item in items {
                    result.extend(item.collect_foralls());
                }
            }
            Ty::Record(.., row) => {
                result.extend(row.collect_foralls());
            }
            Ty::Nominal { type_args, .. } => {
                for arg in type_args {
                    result.extend(arg.collect_foralls());
                }
            }
        }
        result
    }

    pub fn import(self, module_id: ModuleId) -> Self {
        match self {
            Ty::Primitive(symbol) => Ty::Primitive(symbol),
            Ty::Param(type_param_id) => Ty::Param(type_param_id),
            Ty::Constructor {
                name: Name::Resolved(sym, name),
                params,
                ret,
            } => Ty::Constructor {
                name: Name::Resolved(sym.import(module_id), name),
                params: params.into_iter().map(|p| p.import(module_id)).collect(),
                ret: ret.import(module_id).into(),
            },
            Ty::Func(param, ret) => {
                Ty::Func(param.import(module_id).into(), ret.import(module_id).into())
            }
            Ty::Tuple(items) => Ty::Tuple(items.into_iter().map(|t| t.import(module_id)).collect()),
            Ty::Record(symbol, box row) => Ty::Record(
                symbol.map(|s| s.import(module_id)),
                row.import(module_id).into(),
            ),
            Ty::Nominal { symbol, type_args } => Ty::Nominal {
                symbol: symbol.import(module_id),
                type_args: type_args.into_iter().map(|t| t.import(module_id)).collect(),
            },
            other => other,
        }
    }

    pub(crate) fn uncurry_params(self) -> Vec<Ty> {
        let mut result = vec![];

        match self {
            Ty::Void => (),
            Ty::Primitive(..) => result.push(self),
            Ty::Param(..) => result.push(self),
            Ty::Constructor { .. } => result.push(self),
            Ty::Func(param, ..) => result.extend(param.uncurry_params()),
            Ty::Tuple(..) => result.push(self),
            Ty::Record(..) => result.push(self),
            Ty::Nominal { .. } => result.push(self),
        }

        result
    }
}
