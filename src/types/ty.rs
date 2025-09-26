use itertools::Itertools;

use crate::{
    name_resolution::symbol::TypeId,
    node_id::NodeID,
    types::{row::Row, scheme::ForAll},
};

#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy, PartialOrd, Ord)]
pub struct UnificationVarId(u32);
impl From<u32> for UnificationVarId {
    fn from(value: u32) -> Self {
        UnificationVarId(value)
    }
}

#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy, PartialOrd, Ord)]
pub struct TypeParamId(u32);
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

#[derive(PartialEq, PartialOrd, Clone, Copy, Debug, Eq, Hash)]
pub struct Level(pub u32);
impl Level {
    pub fn next(&self) -> Level {
        Level(self.0 + 1)
    }
}

#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy)]
pub enum Primitive {
    Int,
    Float,
    Bool,
    Void,
}

#[derive(PartialEq, Eq, Hash, Clone)]
pub enum Ty {
    Hole(NodeID),
    Primitive(Primitive),

    Param(TypeParamId),
    Rigid(SkolemId),
    UnificationVar {
        id: UnificationVarId,
        level: Level,
    },

    Constructor {
        type_id: TypeId,
        params: Vec<Ty>,
        ret: Box<Ty>,
    },

    Func(Box<Ty>, Box<Ty>),

    Tuple(Vec<Ty>),

    Record(Box<Row>),

    // Nominal types (we look up their information from the TypeCatalog)
    Nominal {
        id: TypeId,
        row: Box<Row>,
    },
}

#[allow(non_upper_case_globals)]
impl Ty {
    pub const Int: Ty = Ty::Primitive(Primitive::Int);
    pub const Float: Ty = Ty::Primitive(Primitive::Float);
    pub const Bool: Ty = Ty::Primitive(Primitive::Bool);
    pub const Void: Ty = Ty::Primitive(Primitive::Void);

    pub fn collect_foralls(&self) -> Vec<ForAll> {
        let mut result = vec![];
        match self {
            Ty::Hole(..) => (),
            Ty::Param(id) => result.push(ForAll::Ty(*id)),
            Ty::Rigid(..) => (),
            Ty::UnificationVar { .. } => (),
            Ty::Primitive(..) => (),
            Ty::Constructor { params, .. } => {
                for item in params {
                    result.extend(item.collect_foralls());
                }
            }
            Ty::Func(ty, ty1) => {
                result.extend(ty.collect_foralls());
                result.extend(ty1.collect_foralls());
            }
            Ty::Tuple(items) => {
                for item in items {
                    result.extend(item.collect_foralls());
                }
            }
            Ty::Nominal { box row, .. } | Ty::Record(box row) => match row {
                Row::Empty(..) => (),
                Row::Extend { row, ty, .. } => {
                    result.extend(Ty::Record(row.clone()).collect_foralls());
                    result.extend(ty.collect_foralls());
                }
                Row::Param(id) => {
                    result.push(ForAll::Row(*id));
                }
                Row::Var(_) => (),
            },
        }
        result
    }

    pub fn contains_var(&self) -> bool {
        match self {
            Ty::Hole(..) => false,
            Ty::Param(..) => false,
            Ty::Rigid(..) => false,
            Ty::UnificationVar { .. } => true,
            Ty::Primitive(..) => false,
            Ty::Constructor { params, .. } => params.iter().any(|p| p.contains_var()),
            Ty::Func(ty, ty1) => ty.contains_var() || ty1.contains_var(),
            Ty::Tuple(items) => items.iter().any(|i| i.contains_var()),
            Ty::Record(box row) => match row {
                Row::Extend { row, ty, .. } => {
                    Ty::Record(row.clone()).contains_var() || ty.contains_var()
                }
                Row::Var(_) => true,
                _ => false,
            },
            Ty::Nominal { .. } => false,
        }
    }

    pub fn fold<T, F: FnMut(&Ty) -> T>(&self, f: &mut F) -> T {
        match self {
            Ty::Hole(..) => f(self),
            Ty::Primitive(..) => f(self),
            Ty::Param(..) => f(self),
            Ty::Rigid(..) => f(self),
            Ty::UnificationVar { .. } => f(self),
            Ty::Constructor { params, ret, .. } => {
                _ = params.iter().map(&mut *f);
                _ = f(ret);
                f(self)
            }
            Ty::Func(ty, ty1) => {
                f(ty);
                f(ty1);
                f(self)
            }
            Ty::Tuple(items) => {
                _ = items.iter().map(&mut *f);
                f(self)
            }
            Ty::Record(box row) => match row {
                Row::Extend { ty, .. } => {
                    f(ty);
                    f(self)
                }
                _ => f(self),
            },
            Ty::Nominal { box row, .. } => match row {
                Row::Extend { ty, .. } => {
                    f(ty);
                    f(self)
                }
                _ => f(self),
            },
        }
    }
}

impl std::fmt::Debug for Ty {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Ty::Hole(..) => write!(f, "Hole"),
            Ty::Param(id) => write!(f, "typeparam(α{})", id.0),
            Ty::Rigid(id) => write!(f, "rigid(α{})", id.0),
            Ty::UnificationVar { id, level } => write!(f, "meta(α{}, {})", id.0, level.0),
            Ty::Primitive(primitive) => write!(f, "{primitive:?}"),
            Ty::Constructor { params, .. } => {
                write!(f, "Constructor({params:?})")
            }
            Ty::Func(param, ret) => write!(f, "func({param:?}) -> {ret:?}"),
            Ty::Tuple(items) => {
                write!(f, "({})", items.iter().map(|i| format!("{i:?}")).join(", "))
            }
            Ty::Nominal { id, row } => write!(f, "Type({id:?}, {row:?})"),
            Ty::Record(box row) => {
                let row_debug = match row {
                    Row::Empty(..) => "".to_string(),
                    Row::Param(id) => format!("rowparam(π{})", id.0),
                    Row::Extend { .. } => {
                        let closed = row.close();
                        let mut parts = vec![];
                        for (field, value) in closed {
                            parts.push(format!("{field}: {value:?}"));
                        }
                        parts.join(", ")
                    }
                    Row::Var(row_meta_id) => format!("rowmeta(π{})", row_meta_id.0),
                };

                write!(f, "{{{row_debug}}}",)
            }
        }
    }
}
