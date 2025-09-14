use itertools::Itertools;

use crate::{
    label::Label, name::Name, name_resolution::symbol::TypeId, node_id::NodeID, types::row::Row,
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
        param: Box<Ty>,
        ret: Box<Ty>,
    },

    Func(Box<Ty>, Box<Ty>),

    Tuple(Vec<Ty>),

    // Nominal types
    Struct(Option<Name>, Box<Row>),
    Sum(Option<Name>, Box<Row>), // Row for variants
    Variant(Label, Box<Ty>),     // Attached value can be either Record or Tuple
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
            Ty::UnificationVar { .. } => true,
            Ty::Primitive(..) => false,
            Ty::Constructor { param, ret, .. } => param.contains_var() || ret.contains_var(),
            Ty::Func(ty, ty1) => ty.contains_var() || ty1.contains_var(),
            Ty::Tuple(items) => items.iter().any(|i| i.contains_var()),
            Ty::Sum(name, box variants) => match variants {
                Row::Empty(..) => false,
                Row::Extend { row, ty, .. } => {
                    Ty::Struct(name.clone(), row.clone()).contains_var() || ty.contains_var()
                }
                Row::Param(..) => false,
                Row::Var(_) => true,
            },
            Ty::Variant(_, ty) => ty.contains_var(),
            Ty::Struct(name, box row) => match row {
                Row::Empty(..) => false,
                Row::Extend { row, ty, .. } => {
                    Ty::Struct(name.clone(), row.clone()).contains_var() || ty.contains_var()
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
            Ty::UnificationVar { id, level } => write!(f, "meta(α{}, {})", id.0, level.0),
            Ty::Primitive(primitive) => write!(f, "{primitive:?}"),
            Ty::Constructor { param, ret, .. } => {
                write!(f, "Constructor({param:?}) -> {ret:?}")
            }
            Ty::Func(param, ret) => write!(f, "func({param:?}) -> {ret:?}"),
            Ty::Tuple(items) => {
                write!(f, "({})", items.iter().map(|i| format!("{i:?}")).join(", "))
            }
            Ty::Variant(name, ty) => {
                write!(f, "enum {name:?}({ty:?})")
            }
            Ty::Struct(name, box row) | Ty::Sum(name, box row) => {
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

                write!(
                    f,
                    "{}{}{{{row_debug}}}",
                    if matches!(self, Ty::Struct(..)) {
                        "struct"
                    } else {
                        "enum"
                    },
                    if let Some(name) = name {
                        format!(" {} ", name.name_str())
                    } else {
                        "".into()
                    }
                )
            }
        }
    }
}
