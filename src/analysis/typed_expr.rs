use crate::{FileID, expr::Expr, parser::ExprID};

use super::type_checker::Ty;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TypedExpr {
    pub id: ExprID,
    pub file_id: FileID,
    pub expr: Expr,
    pub ty: Ty,
}

impl TypedExpr {
    pub fn new(id: ExprID, file_id: FileID, expr: Expr, ty: Ty) -> Self {
        Self {
            id,
            file_id,
            expr,
            ty,
        }
    }
}
