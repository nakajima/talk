use derive_visitor::{Drive, DriveMut};

use crate::{
    impl_into_node,
    label::Label,
    name::Name,
    node_id::NodeID,
    node_kinds::{
        block::Block, call_arg::CallArg, func::Func, incomplete_expr::IncompleteExpr,
        match_arm::MatchArm, record_field::RecordField, type_annotation::TypeAnnotation,
    },
    parsing::span::Span,
    token_kind::TokenKind,
};

#[derive(Debug, Clone, PartialEq, Eq, Drive, DriveMut)]
pub enum ExprKind {
    // These first expressions only exist to assist with LSP operations
    #[drive(skip)]
    Incomplete(IncompleteExpr),

    // Start of the real expressions
    LiteralArray(Vec<Expr>),

    LiteralInt(#[drive(skip)] String),
    LiteralFloat(#[drive(skip)] String),
    LiteralTrue,
    LiteralFalse,
    LiteralString(#[drive(skip)] String),

    Unary(#[drive(skip)] TokenKind, Box<Expr>),
    Binary(Box<Expr>, #[drive(skip)] TokenKind, Box<Expr>),
    Tuple(Vec<Expr>),
    Block(Block),
    Call {
        callee: Box<Expr>,
        type_args: Vec<TypeAnnotation>,
        args: Vec<CallArg>,
    },

    // A dot thing
    Member(Option<Box<Expr>> /* receiver */, #[drive(skip)] Label),

    // Function stuff
    Func(Func),

    Variable(#[drive(skip)] Name),

    // These don't get parsed, they get rewritten from Variables by the name resolver
    Constructor(#[drive(skip)] Name),

    // Control flow
    If(
        Box<Expr>, /* condition */
        Block,     /* condition block */
        Block,     /* else block */
    ),

    // Match expression
    Match(
        Box<Expr>,     // scrutinee: the value being matched
        Vec<MatchArm>, // arms: [MatchArm(pattern, body)]
    ),

    // Record literal: {x: 1, y: 2}
    RecordLiteral {
        fields: Vec<RecordField>,
        spread: Option<Box<Expr>>,
    }, // List of RecordField expressions

    // Row variable in type context: ..R
    RowVariable(#[drive(skip)] Name),
}

impl ExprKind {
    pub fn is_syntactic_value(&self) -> bool {
        match self {
            // These perform computations, they're not just like, values. Which
            // matters when it comes to generalization.
            ExprKind::If(..)
            | ExprKind::Block(..)
            | ExprKind::Match(..)
            | ExprKind::Call { .. }
            | ExprKind::Unary(..)
            | ExprKind::Binary(..)
            | ExprKind::Member(..)
            | ExprKind::RowVariable(..) => false,

            ExprKind::Func(..) => true,
            ExprKind::LiteralArray(items) => items.iter().all(|e| e.kind.is_syntactic_value()),
            ExprKind::Tuple(items) => items.iter().all(|e| e.kind.is_syntactic_value()),
            ExprKind::RecordLiteral { fields, spread } => {
                spread.is_none()
                    && fields
                        .iter()
                        .all(|field| field.value.kind.is_syntactic_value())
            }

            ExprKind::Incomplete(..) => true,
            ExprKind::LiteralInt(..) => true,
            ExprKind::LiteralFloat(..) => true,
            ExprKind::LiteralTrue => true,
            ExprKind::LiteralFalse => true,
            ExprKind::LiteralString(..) => true,
            ExprKind::Variable(..) => true,
            ExprKind::Constructor(..) => true,
        }
    }
}

#[derive(Clone, PartialEq, Eq, Drive, DriveMut)]
pub struct Expr {
    #[drive(skip)]
    pub id: NodeID,
    pub kind: ExprKind,
    #[drive(skip)]
    pub span: Span,
}

impl std::fmt::Debug for Expr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Expr(id: {:?}, kind: {:?})", self.id, self.kind)
    }
}

impl_into_node!(Expr);
