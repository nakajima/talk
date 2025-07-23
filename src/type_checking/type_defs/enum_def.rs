use crate::ty::Ty;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EnumVariant {
    pub tag: usize,
    pub name: String,
    pub ty: Ty,
}
