use crate::token_kind::TokenKind;

use super::expr::Expr;

pub trait Visitor<Result, Context> {
    fn visit_literal_int(&self, literal: &'static str, context: Context) -> Result;
    fn visit_literal_float(&self, literal: &'static str, context: Context) -> Result;
    fn visit_binary_expr(&self, lhs: &Expr, rhs: &Expr, op: TokenKind, context: Context) -> Result;
}
