use derive_visitor::{Drive, DriveMut};

use crate::{impl_into_node, name::Name, node_id::NodeID, parsing::span::Span};

#[derive(Debug, Clone, PartialEq, Eq, Drive, DriveMut)]
pub enum TypeAnnotationKind {
    Func {
        params: Vec<TypeAnnotation>,
        returns: Box<TypeAnnotation>,
    },
    Nominal {
        #[drive(skip)]
        name: Name,
        generics: Vec<TypeAnnotation>,
    },
    Tuple(Vec<TypeAnnotation>),
}

#[derive(Debug, Clone, PartialEq, Eq, Drive, DriveMut)]
pub struct TypeAnnotation {
    #[drive(skip)]
    pub id: NodeID,
    pub kind: TypeAnnotationKind,
    #[drive(skip)]
    pub span: Span,
}

impl_into_node!(TypeAnnotation);
