use crate::parser::ExprID;

use super::type_checker::Ty;

#[derive(Debug, Clone, PartialEq)]
pub struct TypedExpr {
    pub expr: ExprID,
    pub ty: Ty,
}

impl TypedExpr {
    pub fn new(expr: ExprID, ty: Ty) -> Self {
        Self { expr, ty }
    }
}
