use crate::{
    name::Name, name_resolution::symbol::DeclId, node_id::NodeID, types::type_session::TypeDefKind,
};

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Primitive {
    Int,
    Float,
    Bool,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Ty {
    Hole(NodeID),
    Rigid(DeclId),
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
