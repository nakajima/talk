use derive_visitor::{Drive, DriveMut};

use crate::{
    impl_into_node,
    label::Label,
    name::Name,
    node_id::NodeID,
    node_kinds::{
        block::Block, call_arg::CallArg, func::Func, incomplete_expr::IncompleteExpr,
        inline_ir_instruction::InlineIRInstruction, match_arm::MatchArm, record_field::RecordField,
        type_annotation::TypeAnnotation,
    },
    parsing::span::Span,
    token_kind::TokenKind,
};

#[derive(Debug, Clone, PartialEq, Eq, Drive, DriveMut, serde::Serialize, serde::Deserialize)]
pub enum ExprKind {
    // These first expressions only exist to assist with LSP operations
    Incomplete(IncompleteExpr),

    InlineIR(InlineIRInstruction),

    As(Box<Expr>, TypeAnnotation),

    MacroCall {
        #[drive(skip)]
        name: String,
        #[drive(skip)]
        name_span: Span,
        args: Vec<Expr>,
    },

    CallEffect {
        #[drive(skip)]
        effect_name: Name,
        #[drive(skip)]
        effect_name_span: Span,
        type_args: Vec<crate::node_kinds::generic_arg::GenericArg>,
        args: Vec<CallArg>,
    },

    // Start of the real expressions
    LiteralArray(Vec<Expr>),

    LiteralInt(#[drive(skip)] String),
    LiteralFloat(#[drive(skip)] String),
    LiteralTrue,
    LiteralFalse,
    LiteralString(#[drive(skip)] String),
    LiteralCharacter(#[drive(skip)] String),
    Unreachable,

    Unary(#[drive(skip)] TokenKind, Box<Expr>),
    /// Postfix early propagation. Typing elaborates this into a two-arm
    /// enum match: the first variant continues and the second returns.
    Propagate(Box<Expr>),
    /// Postfix force unwrap. The hidden failure expression starts as
    /// `unreachable`, then follows its ordinary desugaring to `'panic`.
    /// Typing uses it as the second arm of the same two-variant elaboration.
    ForceUnwrap(Box<Expr>, Box<Expr>),
    Binary(Box<Expr>, #[drive(skip)] TokenKind, Box<Expr>),
    Subscript(Box<Expr>, Box<Expr>),
    Tuple(Vec<Expr>),
    Block(Block),
    /// A lexical acknowledgement of the compiler-known `'unsafe` effect.
    /// Unlike `@handle`, this installs no runtime handler.
    Unsafe(Block),
    Call {
        callee: Box<Expr>,
        type_args: Vec<crate::node_kinds::generic_arg::GenericArg>,
        args: Vec<CallArg>,
        trailing_block: Option<Block>,
        /// The surface operator lowered into this call, if any. Keeping this
        /// provenance lets later phases report operator-specific diagnostics
        /// without mistaking an explicit protocol-static call for an operator.
        #[drive(skip)]
        desugared_operator: Option<TokenKind>,
    },

    // A dot thing
    Member(
        Option<Box<Expr>>, /* receiver */
        #[drive(skip)] Label,
        #[drive(skip)] Span,
    ),

    // Function stuff
    Func(Func),

    Variable(#[drive(skip)] Name),

    // A type name used as an expression: rewritten from Variables by the
    // name resolver, or parsed directly for a specialized reference
    // (`Opt<Int>.some`, `Res<Int>.A<Bool>`). The name may be a dotted
    // nested-type path; the outer Vec holds one arg list per path
    // segment, so each segment's explicit args pin that segment's own
    // param slots.
    Constructor(
        #[drive(skip)] Name,
        Vec<Vec<crate::node_kinds::generic_arg::GenericArg>>,
    ),

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
}

impl ExprKind {
    pub fn is_syntactic_value(&self) -> bool {
        match self {
            // These perform computations, they're not just like, values. Which
            // matters when it comes to generalization.
            ExprKind::If(..)
            | ExprKind::MacroCall { .. }
            | ExprKind::Block(..)
            | ExprKind::Unsafe(..)
            | ExprKind::Match(..)
            | ExprKind::Call { .. }
            | ExprKind::Unary(..)
            | ExprKind::Propagate(..)
            | ExprKind::ForceUnwrap(..)
            | ExprKind::Binary(..)
            | ExprKind::Subscript(..)
            | ExprKind::Member(..)
            | ExprKind::As(..)
            | ExprKind::InlineIR(..)
            | ExprKind::CallEffect { .. }
            | ExprKind::Unreachable => false,

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
            ExprKind::LiteralCharacter(..) => true,
            ExprKind::Variable(..) => true,
            ExprKind::Constructor(..) => true,
        }
    }
}

#[derive(Clone, PartialEq, Eq, Drive, DriveMut, serde::Serialize, serde::Deserialize)]
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
