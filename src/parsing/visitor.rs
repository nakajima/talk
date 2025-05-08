use crate::token_kind::TokenKind;

use super::{expr::Expr, func_expr::FuncExpr, parse_tree::ParseTree};

pub trait Visitor<Returning, Context> {
    fn visit_literal_int(
        &self,
        literal: &'static str,
        context: &Context,
        parse_tree: &ParseTree,
    ) -> Returning;

    fn visit_literal_float(
        &self,
        literal: &'static str,
        context: &Context,
        parse_tree: &ParseTree,
    ) -> Returning;

    fn visit_binary_expr(
        &self,
        lhs: &Expr,
        rhs: &Expr,
        op: TokenKind,
        context: &Context,
        parse_tree: &ParseTree,
    ) -> Returning;

    fn visit_unary_expr(
        &self,
        rhs: &Expr,
        op: TokenKind,
        context: &Context,
        parse_tree: &ParseTree,
    ) -> Returning;

    fn visit_variable(
        &self,
        name: &'static str,
        context: &Context,
        parse_tree: &ParseTree,
    ) -> Returning;

    fn visit_tuple(
        &self,
        items: Vec<usize>,
        context: &Context,
        parse_tree: &ParseTree,
    ) -> Returning;

    fn visit_func(&self, func: FuncExpr, context: &Context, parse_tree: &ParseTree) -> Returning;
}
