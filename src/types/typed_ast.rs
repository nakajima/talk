use derive_visitor::{Drive, DriveMut};

use crate::{node_id::NodeID, span::Span, types::ty::Ty};

pub struct TypedAST {
    pub roots: Vec<TypedNode>,
}

#[derive(Clone, PartialEq, Eq, Drive, DriveMut)]
pub enum NodeKind {}

#[derive(Clone, PartialEq, Eq, Drive, DriveMut)]
pub struct TypedNode {
    #[drive(skip)]
    pub id: NodeID,
    pub kind: NodeKind,
    #[drive(skip)]
    pub ty: Ty,
    #[drive(skip)]
    pub span: Span,
}
