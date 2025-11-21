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
        type_session::TypeDefKind,
    },
};

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
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

#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy)]
pub enum Primitive {
    Int(Symbol),
    Float(Symbol),
    Bool(Symbol),
    Void(Symbol),
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
        row: Box<InferRow>,
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
            InferTy::Record(box infer_row) => Ty::Record(Box::new(infer_row.into())),
            InferTy::Nominal { symbol, box row } => Ty::Nominal {
                symbol,
                row: Box::new(row.into()),
            },
            InferTy::Projection { .. } => Ty::Param(420420.into()), // FIXME
            ty => panic!("Ty cannot contain variables: {ty:?}"),
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
            Ty::Record(box infer_row) => InferTy::Record(Box::new(infer_row.into())),
            Ty::Nominal { symbol, box row } => InferTy::Nominal {
                symbol,
                row: Box::new(row.into()),
            },
        }
    }
}

impl SomeType for InferTy {
    type RowType = InferRow;
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
            InferTy::Nominal { box row, .. } => {
                let row_contains = match row {
                    InferRow::Extend { row, ty, .. } => {
                        InferTy::Record(row.clone()).contains_var() || ty.contains_var()
                    }
                    InferRow::Var(_) => true,
                    _ => false,
                };

                if row_contains {
                    return true;
                }

                false
            }
        }
    }
}

#[allow(non_upper_case_globals)]
#[allow(non_snake_case)]
impl InferTy {
    pub const Int: InferTy = InferTy::Primitive(Symbol::Int);
    pub const Float: InferTy = InferTy::Primitive(Symbol::Float);
    pub const Bool: InferTy = InferTy::Primitive(Symbol::Bool);
    pub const Void: InferTy = InferTy::Primitive(Symbol::Void);
    pub fn String() -> InferTy {
        InferTy::Nominal {
            symbol: Symbol::Struct(StructId {
                module_id: ModuleId::Core,
                local_id: 2,
            }),
            row: Box::new(InferRow::Empty(TypeDefKind::Struct)),
        }
    }
    pub fn Array(_t: InferTy) -> InferTy {
        let row = InferRow::Extend {
            row: InferRow::Extend {
                row: InferRow::Extend {
                    row: InferRow::Empty(TypeDefKind::Struct).into(),
                    label: "count".into(),
                    ty: InferTy::Int,
                }
                .into(),
                label: "capacity".into(),
                ty: InferTy::Int,
            }
            .into(),
            label: "storage".into(),
            ty: InferTy::Int,
        };

        InferTy::Nominal {
            symbol: Symbol::Struct(StructId {
                module_id: ModuleId::Core,
                local_id: 3,
            }),
            row: row.into(),
        }
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
            InferTy::Nominal { box row, .. } | InferTy::Record(box row) => {
                result.extend(row.collect_foralls());
            }
        }
        result
    }

    pub fn fold<T, F: FnMut(&InferTy) -> T>(&self, f: &mut F) -> T {
        match self {
            InferTy::Primitive(..) => f(self),
            InferTy::Param(..) => f(self),
            InferTy::Rigid(..) => f(self),
            InferTy::Var { .. } => f(self),
            InferTy::Error(..) => f(self),
            InferTy::Constructor { params, ret, .. } => {
                _ = params.iter().map(&mut *f);
                _ = f(ret);
                f(self)
            }
            InferTy::Projection { base, .. } => {
                _ = f(base);
                f(self)
            }
            InferTy::Func(ty, ty1) => {
                f(ty);
                f(ty1);
                f(self)
            }
            InferTy::Tuple(items) => {
                _ = items.iter().map(&mut *f);
                f(self)
            }
            InferTy::Record(box row) => match row {
                InferRow::Extend { ty, .. } => {
                    f(ty);
                    f(self)
                }
                _ => f(self),
            },
            InferTy::Nominal { box row, .. } => match row {
                InferRow::Extend { ty, .. } => {
                    f(ty);
                    f(self)
                }
                _ => f(self),
            },
        }
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
            InferTy::Constructor { name, params, ret } => InferTy::Constructor {
                name: Name::Resolved(name.symbol().import(module_id), name.name_str()),
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
            InferTy::Nominal { symbol, row } => InferTy::Nominal {
                symbol: symbol.import(module_id),
                row: row.import(module_id).into(),
            },
        }
    }
}

impl std::fmt::Debug for InferTy {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            InferTy::Error(err) => write!(f, "Err: {err}"),
            InferTy::Param(id) => write!(f, "typeparam(α{})", id.0),
            InferTy::Rigid(id) => write!(f, "rigid(α{})", id.0),
            InferTy::Var { id, level } => write!(f, "meta(α{}, {})", id.0, level.0),
            InferTy::Primitive(primitive) => write!(f, "{primitive:?}"),
            InferTy::Constructor { params, .. } => {
                write!(f, "Constructor({params:?})")
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
            InferTy::Nominal { symbol, row } => {
                write!(f, "Type({symbol:?}, {row:?})")
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
