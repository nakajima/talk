use crate::types::ty::{Primitive, Ty};

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq, PartialOrd, std::cmp::Ord)]
pub struct TypeVar(pub u32, pub TypeVarDefault);

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq, PartialOrd, std::cmp::Ord)]
pub enum TypeVarDefault {
    Int,
    Float,
    None,
}

impl TypeVar {
    pub fn new(id: u32, default: TypeVarDefault) -> Self {
        Self(id, default)
    }

    pub fn accepts(&self, ty: &Ty) -> bool {
        if matches!(self.1, TypeVarDefault::Int) {
            return matches!(
                ty,
                Ty::Primitive(Primitive::Int) | Ty::Primitive(Primitive::Byte)
            );
        }

        true
    }
}
