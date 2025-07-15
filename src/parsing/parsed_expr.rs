use derive_visitor::DriveMut;

use crate::{SymbolID, name::Name, parsing::expr_id::ExprID, token_kind::TokenKind};

#[derive(Clone, Debug, PartialEq, Eq, DriveMut)]
pub enum IncompleteExpr {
    Member(Option<Box<ParsedExpr>>), // Receiver
    Func {
        #[drive(skip)]
        name: Option<Name>,
        params: Option<Vec<ParsedExpr>>,
        generics: Option<Vec<ParsedExpr>>,
        ret: Option<Box<ParsedExpr>>,
        body: Option<Box<ParsedExpr>>,
    },
}

#[derive(Clone, Debug, PartialEq, Eq, DriveMut)]
pub enum Pattern {
    // Literals that must match exactly
    #[drive(skip)]
    LiteralInt(String),
    #[drive(skip)]
    LiteralFloat(String),
    LiteralTrue,
    LiteralFalse,

    // Variable binding (always succeeds, binds value)
    #[drive(skip)]
    Bind(Name),

    // Wildcard (always succeeds, ignores value)
    Wildcard,

    // Enum variant destructuring
    Variant {
        #[drive(skip)]
        enum_name: Option<Name>, // None for .some, Some for Option.some
        #[drive(skip)]
        variant_name: String,
        fields: Vec<ParsedExpr>, // Recursive patterns for fields
    },
    // // Tuple destructuring
    // PatternTuple(Vec<Pattern>),

    // // Reference patterns (for Rust-style matching)
    // PatternRef(Box<Pattern>),
}

#[derive(Clone, Debug, PartialEq, Eq, DriveMut)]
pub enum Expr {
    // These first expressions only exist to assist with LSP operations
    Incomplete(IncompleteExpr),

    // Start of the real expressions
    LiteralArray(Vec<ParsedExpr>),
    #[drive(skip)]
    LiteralInt(String),
    #[drive(skip)]
    LiteralFloat(String),
    LiteralTrue,
    LiteralFalse,
    #[drive(skip)]
    LiteralString(String),
    Unary(#[drive(skip)] TokenKind, Box<ParsedExpr>),
    Binary(Box<ParsedExpr>, #[drive(skip)] TokenKind, Box<ParsedExpr>),
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
        #[drive(skip)]
        name: Name, /* name */
        generics: Vec<ParsedExpr>, /* generics */
        conformances: Vec<ParsedExpr>,
        body: Box<ParsedExpr>, /* body */
    },
    Struct {
        #[drive(skip)]
        name: Name, /* name */
        generics: Vec<ParsedExpr>, /* generics */
        conformances: Vec<ParsedExpr>,
        body: Box<ParsedExpr>, /* body */
    },

    Property {
        #[drive(skip)]
        name: Name,
        type_repr: Option<Box<ParsedExpr>>,
        default_value: Option<Box<ParsedExpr>>,
    },

    // A type annotation
    TypeRepr {
        #[drive(skip)]
        name: Name,
        generics: Vec<ParsedExpr>, /* generics */
        conformances: Vec<ParsedExpr>,
        #[drive(skip)]
        introduces_type: bool, /* is this a generic type parameter (if so we need to declare it in a scope) */
    },

    FuncTypeRepr(
        Vec<ParsedExpr>,     /* [TypeRepr] args */
        Box<ParsedExpr>,     /* return TypeRepr */
        #[drive(skip)] bool, /* is this a generic type parameter (if so we need to declare it in a scope) */
    ),

    TupleTypeRepr(
        Vec<ParsedExpr>,     /* (T1, T2) */
        #[drive(skip)] bool, /* is this a generic type parameter (if so we need to declare it in a scope) */
    ),

    // A dot thing
    Member(
        Option<Box<ParsedExpr>>, /* receiver */
        #[drive(skip)] String,
    ),

    Init(
        #[drive(skip)] Option<SymbolID>,
        Box<ParsedExpr>, /* func */
    ),

    // Function stuff
    Func {
        #[drive(skip)]
        name: Option<Name>,
        generics: Vec<ParsedExpr>,
        params: Vec<ParsedExpr>,      /* params tuple */
        body: Box<ParsedExpr>,        /* body */
        ret: Option<Box<ParsedExpr>>, /* return type */
        #[drive(skip)]
        captures: Vec<SymbolID>,
    },

    Parameter(
        #[drive(skip)] Name,     /* name */
        Option<Box<ParsedExpr>>, /* TypeRepr */
    ),
    CallArg {
        #[drive(skip)]
        label: Option<Name>,
        value: Box<ParsedExpr>,
    },

    // Variables
    Let(
        #[drive(skip)] Name,     /* name */
        Option<Box<ParsedExpr>>, /* type annotation */
    ),
    Assignment(
        Box<ParsedExpr>, /* LHS */
        Box<ParsedExpr>, /* RHS */
    ),
    Variable(#[drive(skip)] Name),

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
        #[drive(skip)]
        name: Name, // TypeRepr name: Option
        conformances: Vec<ParsedExpr>,
        generics: Vec<ParsedExpr>, // Generics TypeParams <T>
        body: Box<ParsedExpr>,     // Body
    },

    // Individual enum variant in declaration
    EnumVariant(
        #[drive(skip)] Name, // name: "some"
        Vec<ParsedExpr>,     // associated types: [TypeRepr("T")]
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
        #[drive(skip)] Option<Name>, // enum name (None for unqualified .some)
        #[drive(skip)] Name,         // variant name: "some"
        Vec<ParsedExpr>,             // bindings: ["wrapped"]
    ),

    ProtocolDecl {
        #[drive(skip)]
        name: Name,
        associated_types: Vec<ParsedExpr>,
        body: Box<ParsedExpr>,
        conformances: Vec<ParsedExpr>,
    },

    FuncSignature {
        #[drive(skip)]
        name: Name,
        params: Vec<ParsedExpr>,
        generics: Vec<ParsedExpr>,
        ret: Box<ParsedExpr>,
    },
}

#[derive(Clone, Debug, PartialEq, Eq, DriveMut)]
pub struct ParsedExpr {
    #[drive(skip)]
    pub id: ExprID,
    pub expr: Expr,
}
