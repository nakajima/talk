use std::hash::Hash;

use crate::{
    name_resolution::symbol::Symbol,
    types::{
        infer_row::RowParamId,
        infer_ty::{InferTy, InnerTy, TypePhase},
        mappable::Mappable,
        row::Row,
        scheme::ForAll,
        type_error::TypeError,
    },
};
use futures::never::Never;
use indexmap::{IndexMap, IndexSet};

#[derive(PartialEq, Eq, Clone, Hash, Copy, Debug)]
pub struct Typed {}
impl TypePhase for Typed {
    type RigidVar = Never;
    type TypeVar = Never;
    type RowVar = Never;
}

pub type Ty = InnerTy<Typed>;

// #[derive(Debug, PartialEq, Eq, Hash, Clone, Drive, DriveMut)]
// pub enum Ty {
//     Primitive(#[drive(skip)] Symbol),
//     Param(#[drive(skip)] Symbol, #[drive(skip)] Vec<ProtocolId>),
//     Constructor {
//         #[drive(skip)]
//         name: Name,
//         params: Vec<Ty>,
//         ret: Box<Ty>,
//     },

//     Func(Box<Ty>, Box<Ty>, Box<Row>),
//     Tuple(Vec<Ty>),
//     Record(#[drive(skip)] Option<Symbol>, Box<Row>),

//     // Nominal types (we look up their information from the TypeCatalog)
//     Nominal {
//         #[drive(skip)]
//         symbol: Symbol,
//         type_args: Vec<Ty>,
//     },
// }

#[derive(Default, Debug, Clone, PartialEq)]
pub struct Specializations {
    pub ty: IndexMap<Symbol, Ty>,
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
}

#[allow(non_upper_case_globals)]
#[allow(non_snake_case)]
impl Ty {
    pub fn collect_specializations(&self, concrete: &Self) -> Result<Specializations, TypeError> {
        let mut result = Specializations::default();
        match (self, concrete) {
            (Self::Primitive(..), Self::Primitive(..)) => (),
            (Self::Param(id, _), other) => {
                if !matches!(other, Self::Param(..)) {
                    result.ty.insert(*id, other.clone());
                }
            }
            (
                Self::Constructor {
                    params: lhs_params,
                    ret: lhs_ret,
                    ..
                },
                Self::Constructor {
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
                Self::Constructor {
                    params: _constructor_params,
                    ret: box _constructor_ret,
                    ..
                },
                Self::Func(_func_params, _func_ret, _),
            )
            | (
                Self::Func(_func_params, _func_ret, _),
                Self::Constructor {
                    params: _constructor_params,
                    ret: box _constructor_ret,
                    ..
                },
            ) => (),
            (
                Self::Func(lhs_param, lhs_ret, lhs_effects),
                Self::Func(rhs_param, rhs_ret, rhs_effects),
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
            (Self::Tuple(lhs_items), Self::Tuple(rhs_items)) => {
                for (lhs, rhs) in lhs_items.iter().zip(rhs_items) {
                    result.ty.extend(lhs.collect_specializations(rhs)?.ty);
                }
            }
            (Self::Record(.., lhs_row), Self::Record(.., rhs_row)) => {
                result
                    .row
                    .extend(lhs_row.collect_specializations(rhs_row)?.row);
            }
            (
                Self::Nominal {
                    type_args: lhs_args,
                    ..
                },
                Self::Nominal {
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
