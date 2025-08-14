use crate::types::ty::{Primitive, Ty, TypeParameter};

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq, PartialOrd, std::cmp::Ord)]
pub struct TypeVar {
    pub id: u32,
    pub kind: TypeVarKind,
}

impl TypeVar {
    pub fn to_type_parameter(&self) -> TypeParameter {
        TypeParameter(self.id)
    }
}

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq, PartialOrd, std::cmp::Ord)]
pub enum TypeVarKind {
    Row,
    IntLiteral,
    FloatLiteral,
    // Canonical,
    Instantiated,
    None,
    Void,
}

impl TypeVarKind {
    /// Returns true if this kind is more specific than the other
    pub fn is_more_specific_than(&self, other: &TypeVarKind) -> bool {
        use TypeVarKind::*;
        match (self, other) {
            // Literal kinds are most specific
            (IntLiteral | FloatLiteral, _) => true,
            // Canonical/Instantiated are more specific than None
            (Instantiated, None) => true,
            // Everything else is not more specific
            _ => false,
        }
    }
}

impl TypeVar {
    pub fn new(id: u32, kind: TypeVarKind) -> Self {
        Self { id, kind }
    }

    pub fn accepts(&self, ty: &Ty) -> bool {
        match self.kind {
            TypeVarKind::IntLiteral => matches!(
                ty,
                Ty::Primitive(Primitive::Int) | Ty::Primitive(Primitive::Byte)
            ),
            TypeVarKind::FloatLiteral => matches!(ty, Ty::Primitive(Primitive::Float)),
            _ => true,
        }
    }
}
