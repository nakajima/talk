use crate::{SymbolID, ty::Ty};

#[derive(Debug, Clone, PartialEq)]
pub struct TypeConstraint {
    pub protocol_id: SymbolID,
    pub associated_types: Vec<Ty>,
}
