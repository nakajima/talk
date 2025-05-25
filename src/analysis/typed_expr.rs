use crate::expr::Expr;

use super::type_checker::Ty;

#[derive(Debug, Clone, PartialEq)]
pub struct TypedExpr {
    pub expr: Expr,
    pub ty: Ty,
}

impl TypedExpr {
    pub fn new(expr: Expr, ty: Ty) -> Self {
        Self { expr, ty }
    }
}
