use derive_visitor::{Drive, DriveMut};

use crate::{name::Name, node_id::NodeID};

#[derive(Debug, Clone, PartialEq, Eq, DriveMut, Drive)]
pub struct GenericDecl {
    #[drive(skip)]
    pub id: NodeID,
    #[drive(skip)]
    pub name: Name,
    pub generics: Vec<GenericDecl>,
    pub conformances: Vec<GenericDecl>,
}
