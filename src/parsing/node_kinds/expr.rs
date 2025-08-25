use derive_visitor::{Drive, DriveMut};

use crate::{
    label::Label,
    name::Name,
    node::Node,
    node_id::NodeID,
    node_kinds::{
        attribute::Attribute, block::Block, generic_decl::GenericDecl,
        incomplete_expr::IncompleteExpr, match_arm::MatchArm, parameter::Parameter,
        record_field::RecordField, type_annotation::TypeAnnotation,
    },
    token_kind::TokenKind,
};

#[derive(Debug, Clone, PartialEq, Eq, DriveMut, Drive)]
pub struct CallArg {
    #[drive(skip)]
    pub id: NodeID,
    #[drive(skip)]
    pub label: Label,
    pub value: Expr,
}

#[derive(Debug, Clone, PartialEq, Eq, DriveMut, Drive)]
pub enum ExprKind {
    // These first expressions only exist to assist with LSP operations
    Incomplete(IncompleteExpr),

    // Start of the real expressions
    LiteralArray(Vec<Expr>),
    #[drive(skip)]
    LiteralInt(String),
    #[drive(skip)]
    LiteralFloat(String),
    LiteralTrue,
    LiteralFalse,
    #[drive(skip)]
    LiteralString(String),
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
    Func {
        generics: Vec<GenericDecl>,
        params: Vec<Parameter>,      /* params tuple */
        body: Block,                 /* body */
        ret: Option<TypeAnnotation>, /* return type */
        #[drive(skip)]
        attributes: Vec<Attribute>,
    },

    Variable(#[drive(skip)] Name),

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
        #[drive(skip)] Option<Name>, // enum name (None for unqualified .some)
        #[drive(skip)] Name,         // variant name: "some"
        Vec<Node>,                   // bindings: ["wrapped"]
    ),

    // Record literal: {x: 1, y: 2}
    RecordLiteral(Vec<RecordField>), // List of RecordField expressions

    // Row variable in type context: ..R
    RowVariable(#[drive(skip)] Name),

    // Spread in record literal: ...obj
    Spread(Box<Node>),

    FuncSignature {
        #[drive(skip)]
        name: Name,
        params: Vec<Node>,
        generics: Vec<Node>,
        ret: Box<Node>,
    },
}

#[derive(Debug, Clone, PartialEq, Eq, DriveMut, Drive)]
pub struct Expr {
    #[drive(skip)]
    pub id: NodeID,
    pub kind: ExprKind,
}

impl From<Expr> for Node {
    fn from(val: Expr) -> Self {
        Node::Expr(val)
    }
}
