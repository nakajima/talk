use derive_visitor::{Drive, DriveMut};

use crate::{impl_into_node, name::Name, node_id::NodeID, parsing::span::Span};

#[derive(Debug, Clone, PartialEq, Eq, Drive, DriveMut)]
pub struct GenericDecl {
    #[drive(skip)]
    pub id: NodeID,
    #[drive(skip)]
    pub name: Name,
    pub generics: Vec<GenericDecl>,
    pub conformances: Vec<GenericDecl>,
    #[drive(skip)]
    pub span: Span,
}

impl_into_node!(GenericDecl);
