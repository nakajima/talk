use crate::{
    node_id::{FileID, NodeID},
    node_kinds::{
        attribute::Attribute,
        block::Block,
        body::Body,
        call_arg::CallArg,
        decl::Decl,
        expr::{Expr, ExprKind},
        func::Func,
        func_signature::FuncSignature,
        generic_decl::GenericDecl,
        incomplete_expr::IncompleteExpr,
        inline_ir_instruction::InlineIRInstruction,
        match_arm::MatchArm,
        parameter::Parameter,
        pattern::Pattern,
        record_field::RecordField,
        stmt::Stmt,
        type_annotation::TypeAnnotation,
    },
    span::Span,
};

use derive_visitor::{Drive, DriveMut};

pub trait NodeType: Into<Node> + TryFrom<Node> {}

#[derive(Debug, Clone, PartialEq, Eq, Drive, DriveMut)]
pub enum Node {
    Attribute(Attribute),
    Decl(Decl),
    Func(Func),
    GenericDecl(GenericDecl),
    Parameter(Parameter),
    Stmt(Stmt),
    Expr(Expr),
    Pattern(Pattern),
    MatchArm(MatchArm),
    Block(Block),
    Body(Body),
    TypeAnnotation(TypeAnnotation),
    RecordField(RecordField),
    IncompleteExpr(IncompleteExpr),
    CallArg(CallArg),
    FuncSignature(FuncSignature),
    #[drive(skip)]
    InlineIRInstruction(InlineIRInstruction),
}

impl Node {
    pub fn span(&self) -> Span {
        match self {
            Node::Attribute(attribute) => attribute.span,
            Node::Decl(decl) => decl.span,
            Node::Func(func) => func.body.span,
            Node::GenericDecl(generic_decl) => generic_decl.span,
            Node::Parameter(parameter) => parameter.span,
            Node::Stmt(stmt) => stmt.span,
            Node::Expr(expr) => expr.span,
            Node::Pattern(pattern) => pattern.span,
            Node::MatchArm(match_arm) => match_arm.span,
            Node::Block(block) => block.span,
            Node::Body(body) => body.span,
            Node::TypeAnnotation(type_annotation) => type_annotation.span,
            Node::RecordField(record_field) => record_field.span,
            Node::IncompleteExpr(..) => Span {
                file_id: FileID(0),
                start: 0,
                end: 0,
            },
            Node::CallArg(call_arg) => call_arg.span,
            Node::FuncSignature(sig) => sig.span,
            Node::InlineIRInstruction(ir) => ir.span,
        }
    }

    pub fn node_id(&self) -> NodeID {
        match self {
            Node::Attribute(attribute) => attribute.id,
            Node::Decl(decl) => decl.id,
            Node::Func(func) => func.id,
            Node::GenericDecl(generic_decl) => generic_decl.id,
            Node::Parameter(parameter) => parameter.id,
            Node::Stmt(stmt) => stmt.id,
            Node::Expr(expr) => expr.id,
            Node::Pattern(pattern) => pattern.id,
            Node::MatchArm(match_arm) => match_arm.id,
            Node::Block(block) => block.id,
            Node::Body(body) => body.id,
            Node::TypeAnnotation(type_annotation) => type_annotation.id,
            Node::RecordField(record_field) => record_field.id,
            Node::IncompleteExpr(..) => NodeID(FileID(0), 0),
            Node::CallArg(call_arg) => call_arg.id,
            Node::FuncSignature(sig) => sig.id,
            Node::InlineIRInstruction(ir) => ir.id,
        }
    }

    #[allow(clippy::panic)]
    pub fn as_expr(self) -> Expr {
        if let Node::InlineIRInstruction(ref instr) = self {
            // This feels janky
            return Expr {
                id: self.node_id(),
                span: self.span(),
                kind: ExprKind::InlineIR(instr.to_owned()),
            };
        }

        let Node::Expr(expr) = self else {
            panic!("Node.as_expr() failed for {self:?}")
        };

        expr
    }

    #[allow(clippy::panic)]
    pub fn as_stmt(&self) -> &Stmt {
        let Node::Stmt(stmt) = &self else {
            panic!("Node.as_stmt() failed for {self:?}")
        };

        stmt
    }

    #[allow(clippy::panic)]
    pub fn as_decl(&self) -> &Decl {
        let Node::Decl(decl) = &self else {
            panic!("Node.as_stmt() failed for {self:?}")
        };

        decl
    }
}

impl From<&Node> for Node {
    fn from(val: &Node) -> Self {
        val.clone()
    }
}

// impl std::fmt::Debug for Node {
//     fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
//         let meta = Default::default();
//         let formatter = formatter::Formatter::new(&meta);
//         write!(f, "{}", formatter.format(std::slice::from_ref(self), 80))
//     }
// }
