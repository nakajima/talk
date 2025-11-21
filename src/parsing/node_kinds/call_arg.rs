use derive_visitor::{Drive, DriveMut};

use crate::{
    impl_into_node, label::Label, node_id::NodeID, node_kinds::expr::Expr, parsing::span::Span,
};

#[derive(Debug, Clone, PartialEq, Eq, Drive, DriveMut)]
pub struct CallArg {
    #[drive(skip)]
    pub id: NodeID,
    #[drive(skip)]
    pub label: Label,
    #[drive(skip)]
    pub label_span: Span,
    pub value: Expr,
    #[drive(skip)]
    pub span: Span,
}

impl_into_node!(CallArg);
