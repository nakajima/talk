use crate::{
    node_kinds::{
        attribute::Attribute, block::Block, call_arg::CallArg, decl::Decl, expr::Expr,
        generic_decl::GenericDecl, incomplete_expr::IncompleteExpr, match_arm::MatchArm,
        parameter::Parameter, pattern::Pattern, record_field::RecordField, stmt::Stmt,
        type_annotation::TypeAnnotation,
    },
    span::Span,
};

use derive_visitor::{Drive, DriveMut};

pub trait NodeType: Into<Node> + From<Node> {}

#[derive(Debug, Clone, PartialEq, Eq, Drive, DriveMut)]
pub enum Node {
    Attribute(Attribute),
    Decl(Decl),
    GenericDecl(GenericDecl),
    Parameter(Parameter),
    Stmt(Stmt),
    Expr(Expr),
    Pattern(Pattern),
    MatchArm(MatchArm),
    Block(Block),
    TypeAnnotation(TypeAnnotation),
    RecordField(RecordField),
    IncompleteExpr(IncompleteExpr),
    CallArg(CallArg),
}

impl Node {
    pub fn span(&self) -> Span {
        match self {
            Node::Attribute(attribute) => attribute.span,
            Node::Decl(decl) => decl.span,
            Node::GenericDecl(generic_decl) => generic_decl.span,
            Node::Parameter(parameter) => parameter.span,
            Node::Stmt(stmt) => stmt.span,
            Node::Expr(expr) => expr.span,
            Node::Pattern(pattern) => pattern.span,
            Node::MatchArm(match_arm) => match_arm.span,
            Node::Block(block) => block.span,
            Node::TypeAnnotation(type_annotation) => type_annotation.span,
            Node::RecordField(record_field) => record_field.span,
            Node::IncompleteExpr(..) => Span { start: 0, end: 0 },
            Node::CallArg(call_arg) => call_arg.span,
        }
    }

    pub fn as_expr(self) -> Expr {
        let Node::Expr(expr) = self else {
            panic!("Node.as_expr() failed for {self:?}")
        };

        expr
    }

    pub fn as_stmt(&self) -> &Stmt {
        let Node::Stmt(stmt) = &self else {
            panic!("Node.as_stmt() failed for {self:?}")
        };

        stmt
    }

    pub fn as_decl(&self) -> &Decl {
        let Node::Decl(decl) = &self else {
            panic!("Node.as_stmt() failed for {self:?}")
        };

        decl
    }
}
