use itertools::Itertools;

use crate::{
    name::Name,
    node_id::NodeID,
    types::{row::Row, type_session::TypeDefKind},
};

#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy, PartialOrd, Ord)]
pub struct TyMetaId(u32);
impl From<u32> for TyMetaId {
    fn from(value: u32) -> Self {
        TyMetaId(value)
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
    Param(TypeParamId),
    Rigid(SkolemId),
    MetaVar { id: TyMetaId, level: Level },
    Primitive(Primitive),
    TypeConstructor { name: Name, kind: TypeDefKind },
    TypeApplication(Box<Ty>, Box<Ty>),
    Func(Box<Ty>, Box<Ty>),
    Tuple(Vec<Ty>),
    Record(Box<Row>),
    Struct(Name, Box<Row>),
}

#[allow(non_upper_case_globals)]
impl Ty {
    pub const Int: Ty = Ty::Primitive(Primitive::Int);
    pub const Float: Ty = Ty::Primitive(Primitive::Float);
    pub const Bool: Ty = Ty::Primitive(Primitive::Bool);
    pub const Void: Ty = Ty::Primitive(Primitive::Void);

    pub fn contains_var(&self) -> bool {
        match self {
            Ty::Hole(..) => false,
            Ty::Param(..) => false,
            Ty::Rigid(..) => false,
            Ty::MetaVar { .. } => true,
            Ty::Primitive(..) => false,
            Ty::TypeConstructor { .. } => false,
            Ty::TypeApplication(ty, ty1) => ty.contains_var() || ty1.contains_var(),
            Ty::Func(ty, ty1) => ty.contains_var() || ty1.contains_var(),
            Ty::Tuple(items) => items.iter().any(|i| i.contains_var()),
            Ty::Struct(_, box row) | Ty::Record(box row) => match row {
                Row::Empty => false,
                Row::Extend { row, ty, .. } => {
                    Ty::Record(row.clone()).contains_var() || ty.contains_var()
                }
                Row::Param(..) => false,
                Row::Var(_) => true,
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
            Ty::MetaVar { id, level } => write!(f, "meta(α{}, {})", id.0, level.0),
            Ty::Primitive(primitive) => write!(f, "{primitive:?}"),
            Ty::TypeConstructor { name, kind: _ } => {
                write!(f, "K({:?})", name.name_str())
            }
            Ty::TypeApplication(ty, ty1) => write!(f, "{ty:?} → {ty1:?}"),
            Ty::Func(param, ret) => write!(f, "func({param:?}) -> {ret:?}"),
            Ty::Tuple(items) => {
                write!(f, "({})", items.iter().map(|i| format!("{i:?}")).join(", "))
            }
            Ty::Record(box row) => match row {
                Row::Empty => write!(f, "{{}}"),
                Row::Param(id) => write!(f, "rowparam(π{})", id.0),
                Row::Extend { .. } => {
                    let closed = row.close();
                    let mut parts = vec![];
                    for (field, value) in closed {
                        parts.push(format!("{field}: {value:?}"));
                    }
                    write!(f, "{{ {} }}", parts.join(", "))
                }
                Row::Var(row_meta_id) => write!(f, "π{}", row_meta_id.0),
            },
            Ty::Struct(name, box row) => {
                write!(f, "struct {} {:?}", name.name_str(), row.close())
            }
        }
    }
}
