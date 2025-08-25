use derive_visitor::{Drive, DriveMut};

use crate::node_kinds::{
    attribute::Attribute, block::Block, decl::Decl, expr::Expr, generic_decl::GenericDecl,
    incomplete_expr::IncompleteExpr, match_arm::MatchArm, parameter::Parameter, pattern::Pattern,
    stmt::Stmt, type_annotation::TypeAnnotation,
};

#[derive(Debug, Clone, PartialEq, Eq, DriveMut, Drive)]
pub enum Node {
    #[drive(skip)]
    Attribute(Attribute),
    Decl(Decl),
    GenericDecl(GenericDecl),
    Incomplete(IncompleteExpr),
    Parameter(Parameter),
    Stmt(Stmt),
    Expr(Expr),
    Pattern(Pattern),
    MatchArm(MatchArm),
    Block(Block),
    TypeAnnotation(TypeAnnotation),
}

impl Node {
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
