use crate::{name::Name, node_id::NodeID};
use derive_visitor::{Drive, DriveMut};

#[derive(Debug, Clone, PartialEq, Eq, DriveMut, Drive)]
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

#[derive(Debug, Clone, PartialEq, Eq, DriveMut, Drive)]
pub struct TypeAnnotation {
    #[drive(skip)]
    pub id: NodeID,
    pub kind: TypeAnnotationKind,
}
