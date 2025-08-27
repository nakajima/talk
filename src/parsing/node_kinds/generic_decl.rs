use crate::{parsing::span::Span, impl_into_node, name::Name, node::Node, node_id::NodeID};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GenericDecl {
    pub id: NodeID,
    pub name: Name,
    pub generics: Vec<GenericDecl>,
    pub conformances: Vec<GenericDecl>,
    pub span: Span,
}

impl_into_node!(GenericDecl);
