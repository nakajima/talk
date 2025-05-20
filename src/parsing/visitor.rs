use crate::{token::Token, token_kind::TokenKind};

use super::{expr::Expr, parse_tree::ParseTree, parser::ExprID};

pub trait Visitor<Returning, Context> {
    fn visit_literal_int<'a>(
        &self,
        literal: &'a str,
        context: &Context,
        parse_tree: &ParseTree,
    ) -> Returning;

    fn visit_literal_float<'a>(
        &self,
        literal: &'a str,
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

    fn visit_variable<'a>(
        &self,
        name: &'a str,
        context: &Context,
        parse_tree: &ParseTree,
    ) -> Returning;

    fn visit_tuple(
        &self,
        items: Vec<ExprID>,
        context: &Context,
        parse_tree: &ParseTree,
    ) -> Returning;

    fn visit_func(
        &self,
        name: &Option<Token>,
        params: &[ExprID],
        body: ExprID,
        context: &Context,
        parse_tree: &ParseTree,
    ) -> Returning;
}
