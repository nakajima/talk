use crate::{parsing::expr_id::ExprID, ty::Ty};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Property {
    pub index: usize,
    pub name: String,
    pub expr_id: ExprID,
    pub ty: Ty,
    pub has_default: bool,
}

impl Property {
    pub fn new(index: usize, name: String, expr_id: ExprID, ty: Ty, has_default: bool) -> Self {
        Self {
            index,
            name,
            expr_id,
            ty,
            has_default,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Initializer {
    pub name: String,
    pub expr_id: ExprID,
    pub ty: Ty,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Method {
    pub name: String,
    pub expr_id: ExprID,
    pub ty: Ty,
}

impl Method {
    pub fn new(name: String, expr_id: ExprID, ty: Ty) -> Self {
        Self { name, expr_id, ty }
    }
}
