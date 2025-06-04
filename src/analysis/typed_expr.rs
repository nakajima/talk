use crate::{expr::Expr, parser::ExprID};

use super::type_checker::Ty;

#[derive(Debug, Clone, PartialEq)]
pub struct TypedExpr {
    pub id: ExprID,
    pub expr: Expr,
    pub ty: Ty,
}

impl TypedExpr {
    pub fn new(id: ExprID, expr: Expr, ty: Ty) -> Self {
        Self { id, expr, ty }
    }
}
