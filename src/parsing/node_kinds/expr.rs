use crate::{
    impl_into_node,
    label::Label,
    name::Name,
    node::Node,
    node_id::NodeID,
    node_kinds::{
        attribute::Attribute, block::Block, call_arg::CallArg, generic_decl::GenericDecl,
        incomplete_expr::IncompleteExpr, match_arm::MatchArm, parameter::Parameter,
        pattern::Pattern, record_field::RecordField, type_annotation::TypeAnnotation,
    },
    parsing::span::Span,
    token_kind::TokenKind,
};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ExprKind {
    // These first expressions only exist to assist with LSP operations
    Incomplete(IncompleteExpr),

    // Start of the real expressions
    LiteralArray(Vec<Expr>),

    LiteralInt(String),

    LiteralFloat(String),
    LiteralTrue,
    LiteralFalse,

    LiteralString(String),
    Unary(TokenKind, Box<Expr>),
    Binary(Box<Expr>, TokenKind, Box<Expr>),
    Tuple(Vec<Expr>),
    Block(Block),
    Call {
        callee: Box<Expr>,
        type_args: Vec<TypeAnnotation>,
        args: Vec<CallArg>,
    },

    // A dot thing
    Member(Option<Box<Expr>> /* receiver */, Label),

    // Function stuff
    Func {
        generics: Vec<GenericDecl>,
        params: Vec<Parameter>,      /* params tuple */
        body: Block,                 /* body */
        ret: Option<TypeAnnotation>, /* return type */

        attributes: Vec<Attribute>,
    },

    Variable(Name),

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

    // Patterns (for match arms)
    PatternVariant(
        Option<Name>, // enum name (None for unqualified .some)
        Name,         // variant name: "some"
        Vec<Pattern>, // bindings: ["wrapped"]
    ),

    // Record literal: {x: 1, y: 2}
    RecordLiteral(Vec<RecordField>), // List of RecordField expressions

    // Row variable in type context: ..R
    RowVariable(Name),

    // Spread in record literal: ...obj
    Spread(Box<Node>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Expr {
    pub id: NodeID,
    pub kind: ExprKind,
    pub span: Span,
}

impl_into_node!(Expr);
