use derive_visitor::{Drive, DriveMut};

use crate::{
    impl_into_node,
    name::Name,
    node_id::NodeID,
    node_kinds::{expr::Expr, type_annotation::TypeAnnotation},
    parsing::span::Span,
};

#[derive(Clone, Debug, PartialEq, Eq, Drive, DriveMut)]
pub struct RecordFieldTypeAnnotation {
    #[drive(skip)]
    pub id: NodeID,
    #[drive(skip)]
    pub label: Name,
    #[drive(skip)]
    pub label_span: Span,
    pub value: TypeAnnotation,
    #[drive(skip)]
    pub span: Span,
}

// Single field in a record literal
#[derive(Clone, Debug, PartialEq, Eq, Drive, DriveMut)]
pub struct RecordField {
    #[drive(skip)]
    pub id: NodeID,
    #[drive(skip)]
    pub label: Name,
    #[drive(skip)]
    pub label_span: Span,
    pub value: Expr,
    #[drive(skip)]
    pub span: Span,
}

impl_into_node!(RecordField);
