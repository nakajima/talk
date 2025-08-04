use crate::types::ty::{Primitive, Ty};

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq, PartialOrd, std::cmp::Ord)]
pub struct TypeVar {
    pub id: u32,
    pub kind: TypeVarKind,
}

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq, PartialOrd, std::cmp::Ord)]
pub enum TypeVarKind {
    IntLiteral,
    FloatLiteral,
    Canonical,
    Instantiated,
    None,
}

impl TypeVar {
    pub fn new(id: u32, kind: TypeVarKind) -> Self {
        Self { id, kind }
    }

    pub fn accepts(&self, ty: &Ty) -> bool {
        if matches!(self.kind, TypeVarKind::IntLiteral) {
            return matches!(
                ty,
                Ty::Primitive(Primitive::Int) | Ty::Primitive(Primitive::Byte)
            );
        }

        true
    }
}
