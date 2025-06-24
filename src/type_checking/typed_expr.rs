use crate::{expr::Expr, parser::ExprID, ty::Ty};

#[derive(Debug, Clone, PartialEq, Eq)]
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
