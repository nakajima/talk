use crate::{name::Name, node_id::NodeID, node_kinds::type_annotation::TypeAnnotation};
use derive_visitor::{Drive, DriveMut};

// Single field in a record literal
#[derive(Clone, Debug, PartialEq, Eq, DriveMut, Drive)]
pub struct RecordField {
    #[drive(skip)]
    pub id: NodeID,
    #[drive(skip)]
    pub label: Name,
    pub value: TypeAnnotation,
}
