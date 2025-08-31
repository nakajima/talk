use crate::{name::Name, node_id::NodeID, types::type_session::TypeDefKind};

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Primitive {
    Int,
    Float,
    Bool,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Ty {
    Hole(NodeID),
    Primitive(Primitive),
    Nominal { name: Name, kind: TypeDefKind },
}

#[allow(non_upper_case_globals)]
impl Ty {
    pub const Int: Ty = Ty::Primitive(Primitive::Int);
    pub const Float: Ty = Ty::Primitive(Primitive::Float);
    pub const Bool: Ty = Ty::Primitive(Primitive::Bool);
}
