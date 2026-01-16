use std::hash::Hash;

use crate::{
    compiling::module::ModuleId,
    ir::lowerer::curry_ty,
    label::Label,
    name::Name,
    name_resolution::symbol::Symbol,
    types::{
        infer_row::{RowMetaId, RowParamId},
        infer_ty::{InferTy, TypeParamId},
        mappable::Mappable,
        row::Row,
        scheme::ForAll,
        type_error::TypeError,
        types::TypeEntry,
    },
};
use derive_visitor::{Drive, DriveMut};
use indexmap::{IndexMap, IndexSet};

pub enum BaseRow<T: SomeType> {
    Empty,
    Param(RowParamId),
    Var(RowMetaId),
    Extend { row: Box<Self>, label: Label, ty: T },
}

pub trait RowType: PartialEq + Clone + std::fmt::Debug + Drive + DriveMut {
    type T: SomeType<RowType = Self>;
    fn base(&self) -> BaseRow<Self::T>;
    fn empty() -> Self;
    fn param(id: RowParamId) -> Self;
    fn var(id: RowMetaId) -> Self;
    fn extend(row: Self, label: Label, ty: Self::T) -> Self;
}

pub trait SomeType:
    std::fmt::Debug
    + PartialEq
    + Clone
    + Eq
    + Hash
    + Drive
    + DriveMut
    + Mappable<Self, Self, Output = Self>
{
    type RowType: RowType<T = Self>;
    type Entry: Drive + DriveMut + PartialEq + Clone + std::fmt::Debug;

    fn void() -> Self;
    fn contains_var(&self) -> bool;
    fn import(self, module_id: ModuleId) -> Self;
}

impl SomeType for Ty {
    type RowType = Row;
    type Entry = TypeEntry;

    fn void() -> Self {
        Ty::Void
    }

    fn contains_var(&self) -> bool {
        false
    }

    fn import(self, module_id: ModuleId) -> Self {
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
            Ty::Func(param, ret, effects) => Ty::Func(
                param.import(module_id).into(),
                ret.import(module_id).into(),
                effects.import(module_id).into(),
            ),
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

    Func(Box<Ty>, Box<Ty>, Box<Row>),
    Tuple(Vec<Ty>),
    Record(#[drive(skip)] Option<Symbol>, Box<Row>),

    // Nominal types (we look up their information from the TypeCatalog)
    Nominal {
        #[drive(skip)]
        symbol: Symbol,
        type_args: Vec<Ty>,
    },
}

impl Mappable<Ty, Ty> for Ty {
    type Output = Ty;
    fn mapping(
        self,
        ty_map: &mut impl FnMut(Ty) -> Ty,
        row_map: &mut impl FnMut(<Ty as SomeType>::RowType) -> <Ty as SomeType>::RowType,
    ) -> Self::Output {
        match self {
            Ty::Constructor { name, params, ret } => Ty::Constructor {
                name,
                params: params
                    .into_iter()
                    .map(|p| p.mapping(ty_map, row_map))
                    .collect(),
                ret: ret.mapping(ty_map, row_map).into(),
            },
            Ty::Func(param, ret, effects) => Ty::Func(
                param.mapping(ty_map, row_map).into(),
                ret.mapping(ty_map, row_map).into(),
                effects.mapping(ty_map, row_map).into(),
            ),
            Ty::Tuple(items) => Ty::Tuple(
                items
                    .into_iter()
                    .map(|i| i.mapping(ty_map, row_map))
                    .collect(),
            ),
            Ty::Record(symbol, row) => Ty::Record(symbol, row.mapping(ty_map, row_map).into()),
            Ty::Nominal { symbol, type_args } => Ty::Nominal {
                symbol,
                type_args: type_args
                    .into_iter()
                    .map(|t| t.mapping(ty_map, row_map))
                    .collect(),
            },
            other => ty_map(other),
        }
    }
}

impl std::fmt::Display for Ty {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Ty::Primitive(symbol) => match *symbol {
                Symbol::Int => write!(f, "Int"),
                Symbol::Float => write!(f, "Float"),
                Symbol::Bool => write!(f, "Bool"),
                Symbol::Void => write!(f, "Void"),
                Symbol::Never => write!(f, "Never"),
                Symbol::RawPtr => write!(f, "RawPtr"),
                _ => write!(f, "{symbol}"),
            },
            Ty::Param(type_param_id) => write!(f, "{:?}", type_param_id),
            Ty::Constructor { name, .. } => {
                write!(f, "{}", name.name_str())
            }
            Ty::Func(param, ret, effects) => {
                write!(
                    f,
                    "({}) {effects:?} -> {ret}",
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

#[derive(Default, Debug, Clone, PartialEq)]
pub struct Specializations {
    pub ty: IndexMap<TypeParamId, Ty>,
    pub row: IndexMap<RowParamId, Row>,
}
impl Specializations {
    pub fn is_empty(&self) -> bool {
        self.ty.is_empty() && self.row.is_empty()
    }

    pub fn extend(&mut self, other: Specializations) {
        self.ty.extend(
            other
                .ty
                .into_iter()
                .filter(|(_, v)| !matches!(v, Ty::Param(..))),
        );
        self.row.extend(
            other
                .row
                .into_iter()
                .filter(|(_, v)| !matches!(v, Row::Param(..))),
        );
    }

    pub fn apply(&self, ty: Ty) -> Ty {
        ty.mapping(
            &mut |t| {
                if let Ty::Param(id) = t
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
}

#[allow(non_upper_case_globals)]
#[allow(non_snake_case)]
impl Ty {
    pub const Int: Ty = Ty::Primitive(Symbol::Int);
    pub const Float: Ty = Ty::Primitive(Symbol::Float);
    pub const Bool: Ty = Ty::Primitive(Symbol::Bool);
    pub const Void: Ty = Ty::Primitive(Symbol::Void);
    pub const Never: Ty = Ty::Primitive(Symbol::Never);
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

    pub fn collect_specializations(&self, concrete: &Ty) -> Result<Specializations, TypeError> {
        let mut result = Specializations::default();
        match (self, concrete) {
            (Ty::Primitive(..), Ty::Primitive(..)) => (),
            (Ty::Param(id), other) => {
                if !matches!(other, Ty::Param(..)) {
                    result.ty.insert(*id, other.clone());
                }
            }
            (
                Ty::Constructor {
                    params: lhs_params,
                    ret: lhs_ret,
                    ..
                },
                Ty::Constructor {
                    params: rhs_params,
                    ret: rhs_ret,
                    ..
                },
            ) => {
                for (lhs, rhs) in lhs_params.iter().zip(rhs_params) {
                    result.ty.extend(lhs.collect_specializations(rhs)?.ty);
                }

                result
                    .ty
                    .extend(lhs_ret.collect_specializations(rhs_ret)?.ty);
            }
            (
                Ty::Constructor {
                    params: constructor_params,
                    ret: box constructor_ret,
                    ..
                },
                Ty::Func(func_params, func_ret, _),
            )
            | (
                Ty::Func(func_params, func_ret, _),
                Ty::Constructor {
                    params: constructor_params,
                    ret: box constructor_ret,
                    ..
                },
            ) => (),
            (
                Ty::Func(lhs_param, lhs_ret, lhs_effects),
                Ty::Func(rhs_param, rhs_ret, rhs_effects),
            ) => {
                result
                    .ty
                    .extend(lhs_param.collect_specializations(rhs_param)?.ty);
                result
                    .ty
                    .extend(lhs_ret.collect_specializations(rhs_ret)?.ty);
                result
                    .row
                    .extend(lhs_effects.collect_specializations(rhs_effects)?.row)
            }
            (Ty::Tuple(lhs_items), Ty::Tuple(rhs_items)) => {
                for (lhs, rhs) in lhs_items.iter().zip(rhs_items) {
                    result.ty.extend(lhs.collect_specializations(rhs)?.ty);
                }
            }
            (Ty::Record(.., lhs_row), Ty::Record(.., rhs_row)) => {
                result
                    .row
                    .extend(lhs_row.collect_specializations(rhs_row)?.row);
            }
            (
                Ty::Nominal {
                    type_args: lhs_args,
                    ..
                },
                Ty::Nominal {
                    type_args: rhs_args,
                    ..
                },
            ) => {
                for (lhs, rhs) in lhs_args.iter().zip(rhs_args) {
                    result.ty.extend(lhs.collect_specializations(rhs)?.ty);
                }
            }
            tup => {
                tracing::error!("{tup:?}");
                return Err(TypeError::SpecializationMismatch);
            }
        }
        Ok(result)
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
            Ty::Func(param, ret, effects) => {
                result.extend(param.collect_foralls());
                result.extend(ret.collect_foralls());
                result.extend(effects.collect_foralls());
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
