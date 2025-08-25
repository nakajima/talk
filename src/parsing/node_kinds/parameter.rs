use derive_visitor::{Drive, DriveMut};

use crate::{name::Name, node_id::NodeID, node_kinds::type_annotation::TypeAnnotation};

#[derive(Debug, Clone, PartialEq, Eq, DriveMut, Drive)]
pub struct Parameter {
    #[drive(skip)]
    pub id: NodeID,
    #[drive(skip)]
    pub name: Name,
    pub type_annotation: Option<TypeAnnotation>,
}

impl Parameter {
    pub fn new(id: NodeID, name: Name, type_annotation: Option<TypeAnnotation>) -> Self {
        Self {
            id,
            name,
            type_annotation,
        }
    }
}
