use ena::unify::{UnifyKey, UnifyValue};
use indexmap::IndexSet;
use itertools::Itertools;
use std::hash::Hash;

use crate::{
    compiling::module::ModuleId,
    label::Label,
    name::Name,
    name_resolution::symbol::{ProtocolId, StructId, Symbol},
    types::{
        infer_row::{InferRow, RowMetaId},
        scheme::{ForAll, Scheme},
        term_environment::EnvEntry,
        ty::{SomeType, Ty},
        type_error::TypeError,
    },
};

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Meta {
    Ty(MetaVarId),
    Row(RowMetaId),
}

#[derive(PartialEq, Eq, Hash, Clone, Copy, PartialOrd, Ord)]
pub struct MetaVarId(u32);
impl From<u32> for MetaVarId {
    fn from(value: u32) -> Self {
        MetaVarId(value)
    }
}

impl UnifyKey for MetaVarId {
    type Value = Level;

    fn index(&self) -> u32 {
        self.0
    }

    fn from_index(u: u32) -> Self {
        Self(u)
    }

    fn tag() -> &'static str {
        "meta"
    }
}

impl std::fmt::Debug for MetaVarId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "meta({})", self.0)
    }
}

#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy, PartialOrd, Ord)]
pub struct TypeParamId(u32);
impl TypeParamId {
    pub const IR_TYPE_PARAM: TypeParamId = TypeParamId(u32::MAX - 1);
}
impl From<u32> for TypeParamId {
    fn from(value: u32) -> Self {
        TypeParamId(value)
    }
}

#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy, PartialOrd, Ord)]
pub struct SkolemId(u32);
impl From<u32> for SkolemId {
    fn from(value: u32) -> Self {
        SkolemId(value)
    }
}

#[derive(Default, PartialEq, PartialOrd, Clone, Copy, Debug, Eq, Hash)]
pub struct Level(pub u32);
impl Level {
    pub fn next(&self) -> Level {
        Level(self.0 + 1)
    }

    pub fn prev(&self) -> Level {
        Level(self.0.saturating_sub(1))
    }
}

impl UnifyValue for Level {
    type Error = TypeError;

    fn unify_values(lhs: &Self, rhs: &Self) -> Result<Self, Self::Error> {
        Ok(if lhs.0 > rhs.0 { *rhs } else { *lhs })
    }
}

#[derive(PartialEq, Eq, Clone, Hash)]
pub enum InferTy {
    Primitive(Symbol),

    Param(TypeParamId),
    Rigid(SkolemId),
    Var {
        id: MetaVarId,
        level: Level,
    },

    Projection {
        base: Box<InferTy>,
        protocol_id: ProtocolId,
        associated: Label,
    },

    Constructor {
        name: Name,
        params: Vec<InferTy>,
        ret: Box<InferTy>,
    },

    Func(Box<InferTy>, Box<InferTy>),
    Tuple(Vec<InferTy>),
    Record(Box<InferRow>),

    // Nominal types (we look up their information from the TypeCatalog)
    Nominal {
        symbol: Symbol,
        type_args: Vec<InferTy>,
    },

    Error(Box<TypeError>),
}

impl From<InferTy> for Ty {
    #[allow(clippy::panic)]
    fn from(value: InferTy) -> Self {
        match value {
            InferTy::Primitive(primitive) => Ty::Primitive(primitive),
            InferTy::Param(type_param_id) => Ty::Param(type_param_id),
            InferTy::Constructor {
                name,
                params,
                box ret,
            } => Ty::Constructor {
                name,
                params: params.into_iter().map(|p| p.into()).collect(),
                ret: Box::new(ret.into()),
            },
            InferTy::Func(box param, box ret) => {
                Ty::Func(Box::new(param.into()), Box::new(ret.into()))
            }
            InferTy::Tuple(items) => Ty::Tuple(items.into_iter().map(|t| t.into()).collect()),
            InferTy::Record(box infer_row) => Ty::Record(None, Box::new(infer_row.into())),
            InferTy::Nominal { symbol, type_args } => Ty::Nominal {
                symbol,
                type_args: type_args.into_iter().map(|p| p.into()).collect(),
            },
            InferTy::Projection { .. } => Ty::Param(420420.into()), // FIXME
            _ => Ty::Param(420420.into()),
        }
    }
}

impl From<Ty> for InferTy {
    fn from(value: Ty) -> Self {
        match value {
            Ty::Primitive(primitive) => InferTy::Primitive(primitive),
            Ty::Param(type_param_id) => InferTy::Param(type_param_id),
            Ty::Constructor {
                name,
                params,
                box ret,
            } => InferTy::Constructor {
                name,
                params: params.into_iter().map(|p| p.into()).collect(),
                ret: Box::new(ret.into()),
            },
            Ty::Func(box param, box ret) => {
                InferTy::Func(Box::new(param.into()), Box::new(ret.into()))
            }
            Ty::Tuple(items) => InferTy::Tuple(items.into_iter().map(|t| t.into()).collect()),
            Ty::Record(.., box infer_row) => InferTy::Record(Box::new(infer_row.into())),
            Ty::Nominal { symbol, type_args } => InferTy::Nominal {
                symbol,
                type_args: type_args.into_iter().map(|t| t.into()).collect(),
            },
        }
    }
}

impl SomeType for InferTy {
    type RowType = InferRow;

    fn void() -> Self {
        InferTy::Void
    }

    fn contains_var(&self) -> bool {
        match self {
            InferTy::Param(..) => false,
            InferTy::Rigid(..) => false,
            InferTy::Var { .. } => true,
            InferTy::Primitive(..) => false,
            InferTy::Error(..) => false,
            InferTy::Projection { base, .. } => base.contains_var(),
            InferTy::Constructor { params, .. } => params.iter().any(|p| p.contains_var()),
            InferTy::Func(ty, ty1) => ty.contains_var() || ty1.contains_var(),
            InferTy::Tuple(items) => items.iter().any(|i| i.contains_var()),
            InferTy::Record(box row) => match row {
                InferRow::Extend { row, ty, .. } => {
                    InferTy::Record(row.clone()).contains_var() || ty.contains_var()
                }
                InferRow::Var(_) => true,
                _ => false,
            },
            InferTy::Nominal { type_args, .. } => type_args.contains(self),
        }
    }
}

#[allow(non_upper_case_globals)]
#[allow(non_snake_case)]
impl InferTy {
    pub const Int: InferTy = InferTy::Primitive(Symbol::Int);
    pub const Float: InferTy = InferTy::Primitive(Symbol::Float);
    pub const Bool: InferTy = InferTy::Primitive(Symbol::Bool);
    pub const RawPtr: InferTy = InferTy::Primitive(Symbol::RawPtr);
    pub const Void: InferTy = InferTy::Primitive(Symbol::Void);
    pub const Byte: InferTy = InferTy::Primitive(Symbol::Byte);
    pub fn String() -> InferTy {
        InferTy::Nominal {
            symbol: Symbol::String,
            type_args: Default::default(),
        }
    }
    pub fn Array(t: InferTy) -> InferTy {
        InferTy::Nominal {
            symbol: Symbol::Struct(StructId {
                module_id: ModuleId::Core,
                local_id: 3,
            }),
            type_args: vec![t],
        }
    }

    pub fn collect_metas(&self) -> IndexSet<InferTy> {
        let mut out = IndexSet::default();
        match self {
            InferTy::Error(..) => {}
            InferTy::Param(_) => {}
            InferTy::Var { .. } => {
                out.insert(self.clone());
            }
            InferTy::Projection { base, .. } => {
                out.extend(base.collect_metas());
            }
            InferTy::Func(dom, codom) => {
                out.extend(dom.collect_metas());
                out.extend(codom.collect_metas());
            }
            InferTy::Tuple(items) => {
                for item in items {
                    out.extend(item.collect_metas());
                }
            }
            InferTy::Record(box row) => match row {
                InferRow::Empty(..) => (),
                InferRow::Var(..) => {
                    out.insert(self.clone());
                }
                InferRow::Param(..) => (),
                InferRow::Extend { row, ty, .. } => {
                    out.extend(ty.collect_metas());
                    out.extend(InferTy::Record(row.clone()).collect_metas());
                }
            },
            InferTy::Nominal { type_args, .. } => {
                for arg in type_args {
                    out.extend(arg.collect_metas());
                }
            }
            InferTy::Constructor { params, .. } => {
                for param in params {
                    out.extend(param.collect_metas());
                }
            }
            InferTy::Primitive(_) | InferTy::Rigid(_) => {}
        }

        out
    }

    pub fn to_entry(&self) -> EnvEntry<InferTy> {
        let foralls: IndexSet<ForAll> = self.collect_foralls().into_iter().collect();
        if foralls.is_empty() {
            EnvEntry::Mono(self.clone())
        } else {
            EnvEntry::Scheme(Scheme {
                ty: self.clone(),
                foralls,
                predicates: vec![],
            })
        }
    }

    pub fn collect_foralls(&self) -> IndexSet<ForAll> {
        let mut result: IndexSet<ForAll> = Default::default();
        match self {
            InferTy::Param(id) => {
                result.insert(ForAll::Ty(*id));
            }
            InferTy::Error(..) => (),
            InferTy::Rigid(..) => (),
            InferTy::Var { .. } => (),
            InferTy::Primitive(..) => (),
            InferTy::Nominal { type_args, .. } => {
                for arg in type_args {
                    result.extend(arg.collect_foralls());
                }
            }
            InferTy::Projection { base, .. } => {
                result.extend(base.collect_foralls());
            }
            InferTy::Constructor { params, .. } => {
                for item in params {
                    result.extend(item.collect_foralls());
                }
            }
            InferTy::Func(ty, ty1) => {
                result.extend(ty.collect_foralls());
                result.extend(ty1.collect_foralls());
            }
            InferTy::Tuple(items) => {
                for item in items {
                    result.extend(item.collect_foralls());
                }
            }
            InferTy::Record(box row) => {
                result.extend(row.collect_foralls());
            }
        }
        result
    }

    pub fn import(self, module_id: ModuleId) -> InferTy {
        match self {
            InferTy::Error(..) => self,
            InferTy::Primitive(..) => self,
            InferTy::Param(..) => self,
            InferTy::Rigid(..) => self,
            InferTy::Var { .. } => self,
            InferTy::Projection {
                base,
                associated,
                protocol_id,
            } => InferTy::Projection {
                base: base.import(module_id).into(),
                associated,
                protocol_id,
            },
            InferTy::Constructor {
                name: name @ Name::Resolved(..),
                params,
                ret,
            } => InferTy::Constructor {
                name: Name::Resolved(
                    name.symbol()
                        .unwrap_or_else(|_| unreachable!())
                        .import(module_id),
                    name.name_str(),
                ),
                params,
                ret,
            },
            InferTy::Func(ty, ty1) => {
                InferTy::Func(ty.import(module_id).into(), ty1.import(module_id).into())
            }
            InferTy::Tuple(items) => {
                InferTy::Tuple(items.into_iter().map(|i| i.import(module_id)).collect())
            }
            InferTy::Record(row) => InferTy::Record(row.import(module_id).into()),
            InferTy::Nominal { symbol, type_args } => InferTy::Nominal {
                symbol: symbol.import(module_id),
                type_args: type_args.into_iter().map(|f| f.import(module_id)).collect(),
            },
            _ => self,
        }
    }
}

impl std::fmt::Debug for InferTy {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            InferTy::Error(err) => write!(f, "Error Ty: {err}"),
            InferTy::Param(id) => write!(f, "typeparam(α{})", id.0),
            InferTy::Rigid(id) => write!(f, "rigid(α{})", id.0),
            InferTy::Var { id, level } => write!(f, "meta(α{}, {})", id.0, level.0),
            InferTy::Primitive(primitive) => write!(f, "{primitive:?}"),
            InferTy::Constructor { name, params, .. } => {
                write!(f, "Constructor({name:?},{params:?})")
            }
            InferTy::Projection {
                base,
                associated,
                protocol_id,
            } => write!(f, "{base:?}.{associated:?}[{protocol_id:?}"),
            InferTy::Func(param, ret) => write!(f, "func({param:?}) -> {ret:?}"),
            InferTy::Tuple(items) => {
                write!(f, "({})", items.iter().map(|i| format!("{i:?}")).join(", "))
            }
            InferTy::Nominal { symbol, type_args } => {
                write!(f, "Nominal({symbol:?}, {type_args:?})")
            }
            InferTy::Record(box row) => {
                let row_debug = match row {
                    InferRow::Empty(kind) => format!("emptyrow({kind:?})"),
                    InferRow::Param(id) => format!("rowparam(π{})", id.0),
                    InferRow::Extend { .. } => {
                        let closed = row.close();
                        let mut parts = vec![];
                        for (field, value) in closed {
                            parts.push(format!("{field}: {value:?}"));
                        }
                        parts.join(", ")
                    }
                    InferRow::Var(row_meta_id) => format!("rowmeta(π{})", row_meta_id.0),
                };

                write!(f, "{{{row_debug}}}",)
            }
        }
    }
}
