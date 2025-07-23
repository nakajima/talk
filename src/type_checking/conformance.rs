use crate::{SymbolID, ty::Ty};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Conformance {
    pub protocol_id: SymbolID,
    pub associated_types: Vec<Ty>,
}

impl Conformance {
    pub fn new(protocol_id: SymbolID, associated_types: Vec<Ty>) -> Self {
        Self {
            protocol_id,
            associated_types,
        }
    }
}
