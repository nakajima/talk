use crate::{token::Token, token_kind::TokenKind};

use super::{expr::Expr, parse_tree::ParseTree, parser::NodeID};

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
        items: Vec<NodeID>,
        context: &Context,
        parse_tree: &ParseTree,
    ) -> Returning;

    fn visit_func(
        &self,
        name: &Option<Token>,
        params: &Vec<NodeID>,
        body: NodeID,
        context: &Context,
        parse_tree: &ParseTree,
    ) -> Returning;
}
