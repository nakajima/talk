use derive_visitor::{Drive, DriveMut};

use crate::{impl_into_node, node_id::NodeID, node_kinds::decl::Decl, span::Span};

#[derive(Debug, Clone, PartialEq, Eq, Drive, DriveMut)]
pub struct Body {
    #[drive(skip)]
    pub id: NodeID,
    pub decls: Vec<Decl>,
    #[drive(skip)]
    pub span: Span,
}

impl_into_node!(Body);
