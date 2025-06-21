use crate::{
    expr::Expr,
    parser::{ExprID, ExprIDWithPath},
};

use super::type_checker::Ty;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TypedExpr {
    pub id: ExprIDWithPath,
    pub expr: Expr,
    pub ty: Ty,
}

impl TypedExpr {
    pub fn new(id: ExprIDWithPath, expr: Expr, ty: Ty) -> Self {
        Self { id, expr, ty }
    }
}
