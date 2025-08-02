use crate::{SymbolID, ty::Ty2};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TypeConstraint {
    Conforms {
        protocol_id: SymbolID,
        associated_types: Vec<Ty2>,
    },
    InstanceOf {
        symbol_id: SymbolID,
        associated_types: Vec<Ty2>,
    },
    Equals {
        ty: Ty2,
    },
}
