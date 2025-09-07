use crate::{name::Name, node_id::NodeID, types::type_session::TypeDefKind};

#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy, PartialOrd, Ord)]
pub struct MetaId(u32);
impl From<u32> for MetaId {
    fn from(value: u32) -> Self {
        MetaId(value)
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

#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub enum Ty {
    Hole(NodeID),
    Param(TypeParamId),
    Rigid(SkolemId),
    MetaVar { id: MetaId, level: Level },
    Primitive(Primitive),
    TypeConstructor { name: Name, kind: TypeDefKind },
    TypeApplication(Box<Ty>, Box<Ty>),
    Func(Box<Ty>, Box<Ty>),
    Tuple(Vec<Ty>),
}

#[allow(non_upper_case_globals)]
impl Ty {
    pub const Int: Ty = Ty::Primitive(Primitive::Int);
    pub const Float: Ty = Ty::Primitive(Primitive::Float);
    pub const Bool: Ty = Ty::Primitive(Primitive::Bool);
    pub const Void: Ty = Ty::Primitive(Primitive::Void);
}
