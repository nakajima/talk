use crate::{SymbolID, ty::Ty2};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Conformance {
    pub protocol_id: SymbolID,
    pub associated_types: Vec<Ty2>,
}

impl Conformance {
    pub fn new(protocol_id: SymbolID, associated_types: Vec<Ty2>) -> Self {
        Self {
            protocol_id,
            associated_types,
        }
    }
}
