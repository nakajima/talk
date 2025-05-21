use crate::parser::ExprID;

use super::type_checker::{Ty, TypeDesc};

#[derive(Debug, Clone, PartialEq)]
pub struct TypedExpr {
    pub expr: ExprID,
    pub ty: TypeDesc,
}

impl TypedExpr {
    pub fn new(expr: ExprID, ty: TypeDesc) -> Self {
        Self { expr, ty }
    }
}
