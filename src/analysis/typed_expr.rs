use crate::{expr::Expr, parser::ExprID};

use super::type_checker::Ty;

#[derive(Debug, Clone, PartialEq)]
pub struct TypedExpr {
    pub id: ExprID,
    pub ty: Ty,
}

impl TypedExpr {
    pub fn new(expr: Expr, ty: Ty) -> Self {
        Self { expr, ty }
    }
}
