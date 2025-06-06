use crate::{token::Token, token_kind::TokenKind};

use super::{name::Name, parser::ExprID};

pub type VarDepth = u32;

#[derive(Clone, Debug, PartialEq)]
pub struct ExprMeta {
    pub start: Token,
    pub end: Token,
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
        variant_name: Name,
        fields: Vec<ExprID>, // Recursive patterns for fields
    },
    // // Tuple destructuring
    // PatternTuple(Vec<Pattern>),

    // // Reference patterns (for Rust-style matching)
    // PatternRef(Box<Pattern>),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Expr {
    LiteralInt(String),
    LiteralFloat(String),
    LiteralTrue,
    LiteralFalse,
    Unary(TokenKind, ExprID),
    Binary(ExprID, TokenKind, ExprID),
    Tuple(Vec<ExprID>),
    Block(Vec<ExprID>),
    Call(ExprID, Vec<ExprID>),
    Pattern(Pattern),
    Return(Option<ExprID>),

    // A type annotation
    TypeRepr(
        Name,
        Vec<ExprID>, /* generics */
        bool,        /* is this a generic type parameter (if so we need to declare it in a scope) */
    ),

    FuncTypeRepr(
        Vec<ExprID>, /* [TypeRepr] args */
        ExprID,      /* return TypeRepr */
        bool,        /* is this a generic type parameter (if so we need to declare it in a scope) */
    ),

    TupleTypeRepr(
        Vec<ExprID>, /* (T1, T2) */
        bool,        /* is this a generic type parameter (if so we need to declare it in a scope) */
    ),

    // A dot thing
    Member(Option<ExprID> /* receiver */, String),

    // Function stuff
    Func {
        name: Option<Name>,
        generics: Vec<ExprID>,
        params: Vec<ExprID>, /* params tuple */
        body: ExprID,        /* body */
        ret: Option<ExprID>, /* return type */
    },
    Parameter(Name /* name */, Option<ExprID> /* TypeRepr */),

    // Variables
    Let(
        Name,           /* name */
        Option<ExprID>, /* type annotation */
    ),
    Assignment(ExprID /* LHS */, ExprID /* RHS */),
    Variable(Name, Option<ExprID>),

    // For name resolution
    // ResolvedVariable(SymbolID, Option<ExprID>),
    // ResolvedLet(SymbolID, Option<ExprID> /* RHS */),

    // Control flow
    If(
        ExprID,         /* condition */
        ExprID,         /* condition block */
        Option<ExprID>, /* else block */
    ),

    Loop(Option<ExprID> /* condition */, ExprID /* body */),

    // Enum declaration
    EnumDecl(
        Name,        // TypeRepr name: Option
        Vec<ExprID>, // Generics TypeParams <T>
        ExprID,      // Body
    ),

    // Individual enum variant in declaration
    EnumVariant(
        Name,        // name: "some"
        Vec<ExprID>, // associated types: [TypeRepr("T")]
    ),

    // Match expression
    Match(
        ExprID,      // scrutinee: the value being matched
        Vec<ExprID>, // arms: [MatchArm(pattern, body)]
    ),

    // Individual match arm
    MatchArm(
        ExprID, // pattern
        ExprID, // body (after ->)
    ),

    // Patterns (for match arms)
    PatternVariant(
        Option<Name>, // enum name (None for unqualified .some)
        Name,         // variant name: "some"
        Vec<ExprID>,  // bindings: ["wrapped"]
    ),
}
