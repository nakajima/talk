use crate::{SymbolID, ty::Ty};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TypeConstraint {
    Conforms {
        protocol_id: SymbolID,
        associated_types: Vec<Ty>,
    },
    InstanceOf {
        symbol_id: SymbolID,
        associated_types: Vec<Ty>,
    },
    Equals {
        ty: Ty,
    },
}
