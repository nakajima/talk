use crate::{
    name::Name, name_resolution::symbol::DeclId, node_id::NodeID, types::type_session::TypeDefKind,
};

#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy)]
pub struct MetaId(u32);
impl From<u32> for MetaId {
    fn from(value: u32) -> Self {
        MetaId(value)
    }
}

#[derive(Debug, Copy, PartialEq, Eq, Clone)]
pub struct Level(pub u32);
impl Level {
    pub fn next(&self) -> Level {
        Level(self.0 + 1)
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum Primitive {
    Int,
    Float,
    Bool,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Ty {
    Hole(NodeID),
    Rigid(DeclId),
    MetaVar { id: MetaId, level: Level },
    Primitive(Primitive),
    TypeConstructor { name: Name, kind: TypeDefKind },
    TypeApplication(Box<Ty>, Box<Ty>),
}

#[allow(non_upper_case_globals)]
impl Ty {
    pub const Int: Ty = Ty::Primitive(Primitive::Int);
    pub const Float: Ty = Ty::Primitive(Primitive::Float);
    pub const Bool: Ty = Ty::Primitive(Primitive::Bool);
}
