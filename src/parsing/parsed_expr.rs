use crate::{SymbolID, name::Name, parser::ExprID, token_kind::TokenKind};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum IncompleteExpr {
    Member(Option<Box<ParsedExpr>>), // Receiver
    Func {
        name: Option<Name>,
        params: Option<Vec<ParsedExpr>>,
        generics: Option<Vec<ParsedExpr>>,
        ret: Option<Box<ParsedExpr>>,
        body: Option<Box<ParsedExpr>>,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Pattern {
    // Literals that must match exactly
    LiteralInt(String),
    LiteralFloat(String),
    LiteralTrue,
    LiteralFalse,

    // Variable binding (always succeeds, binds value)
    Bind(Name),

    // Wildcard (always succeeds, ignores value)
    Wildcard,

    // Enum variant destructuring
    Variant {
        enum_name: Option<Name>, // None for .some, Some for Option.some
        variant_name: String,
        fields: Vec<ParsedExpr>, // Recursive patterns for fields
    },
    // // Tuple destructuring
    // PatternTuple(Vec<Pattern>),

    // // Reference patterns (for Rust-style matching)
    // PatternRef(Box<Pattern>),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Expr {
    // These first expressions only exist to assist with LSP operations
    Incomplete(IncompleteExpr),

    // Start of the real expressions
    LiteralArray(Vec<ParsedExpr>),
    LiteralInt(String),
    LiteralFloat(String),
    LiteralTrue,
    LiteralFalse,
    LiteralString(String),
    Unary(TokenKind, Box<ParsedExpr>),
    Binary(Box<ParsedExpr>, TokenKind, Box<ParsedExpr>),
    Tuple(Vec<ParsedExpr>),
    Block(Vec<ParsedExpr>),
    Call {
        callee: Box<ParsedExpr>,
        type_args: Vec<ParsedExpr>,
        args: Vec<ParsedExpr>,
    },
    ParsedPattern(Pattern),
    Return(Option<Box<ParsedExpr>>),
    Break,
    Extend {
        name: Name,                /* name */
        generics: Vec<ParsedExpr>, /* generics */
        conformances: Vec<ParsedExpr>,
        body: Box<ParsedExpr>, /* body */
    },
    Struct {
        name: Name,                /* name */
        generics: Vec<ParsedExpr>, /* generics */
        conformances: Vec<ParsedExpr>,
        body: Box<ParsedExpr>, /* body */
    },

    Property {
        name: Name,
        type_repr: Option<Box<ParsedExpr>>,
        default_value: Option<Box<ParsedExpr>>,
    },

    // A type annotation
    TypeRepr {
        name: Name,
        generics: Vec<ParsedExpr>, /* generics */
        conformances: Vec<ParsedExpr>,
        introduces_type: bool, /* is this a generic type parameter (if so we need to declare it in a scope) */
    },

    FuncTypeRepr(
        Vec<ParsedExpr>, /* [TypeRepr] args */
        Box<ParsedExpr>, /* return TypeRepr */
        bool, /* is this a generic type parameter (if so we need to declare it in a scope) */
    ),

    TupleTypeRepr(
        Vec<ParsedExpr>, /* (T1, T2) */
        bool, /* is this a generic type parameter (if so we need to declare it in a scope) */
    ),

    // A dot thing
    Member(Option<Box<ParsedExpr>> /* receiver */, String),

    Init(Option<SymbolID>, Box<ParsedExpr> /* func */),

    // Function stuff
    Func {
        name: Option<Name>,
        generics: Vec<ParsedExpr>,
        params: Vec<ParsedExpr>,      /* params tuple */
        body: Box<ParsedExpr>,        /* body */
        ret: Option<Box<ParsedExpr>>, /* return type */
        captures: Vec<SymbolID>,
    },

    Parameter(
        Name,                    /* name */
        Option<Box<ParsedExpr>>, /* TypeRepr */
    ),
    CallArg {
        label: Option<Name>,
        value: Box<ParsedExpr>,
    },

    // Variables
    Let(
        Name,                    /* name */
        Option<Box<ParsedExpr>>, /* type annotation */
    ),
    Assignment(
        Box<ParsedExpr>, /* LHS */
        Box<ParsedExpr>, /* RHS */
    ),
    Variable(Name),

    // For name resolution
    // ResolvedVariable(SymbolID, Option<ParsedExpr>),
    // ResolvedLet(SymbolID, Option<ParsedExpr> /* RHS */),

    // Control flow
    If(
        Box<ParsedExpr>,         /* condition */
        Box<ParsedExpr>,         /* condition block */
        Option<Box<ParsedExpr>>, /* else block */
    ),

    Loop(
        Option<Box<ParsedExpr>>, /* condition */
        Box<ParsedExpr>,         /* body */
    ),

    // Enum declaration
    EnumDecl {
        name: Name, // TypeRepr name: Option
        conformances: Vec<ParsedExpr>,
        generics: Vec<ParsedExpr>, // Generics TypeParams <T>
        body: Box<ParsedExpr>,     // Body
    },

    // Individual enum variant in declaration
    EnumVariant(
        Name,            // name: "some"
        Vec<ParsedExpr>, // associated types: [TypeRepr("T")]
    ),

    // Match expression
    Match(
        Box<ParsedExpr>, // scrutinee: the value being matched
        Vec<ParsedExpr>, // arms: [MatchArm(pattern, body)]
    ),

    // Individual match arm
    MatchArm(
        Box<ParsedExpr>, // pattern
        Box<ParsedExpr>, // body (after ->)
    ),

    // Patterns (for match arms)
    PatternVariant(
        Option<Name>,    // enum name (None for unqualified .some)
        Name,            // variant name: "some"
        Vec<ParsedExpr>, // bindings: ["wrapped"]
    ),

    ProtocolDecl {
        name: Name,
        associated_types: Vec<ParsedExpr>,
        body: Box<ParsedExpr>,
        conformances: Vec<ParsedExpr>,
    },

    FuncSignature {
        name: Name,
        params: Vec<ParsedExpr>,
        generics: Vec<ParsedExpr>,
        ret: Box<ParsedExpr>,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ParsedExpr {
    pub id: ExprID,
    pub expr: Expr,
}
