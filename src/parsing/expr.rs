use crate::{symbol_table::SymbolID, token::Token, token_kind::TokenKind};

use super::parser::ExprID;

pub type VarDepth = u32;

#[derive(Clone, Debug, PartialEq)]
pub struct ExprMeta {
    pub start: Token,
    pub end: Token,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FuncName {
    Main,
    Token(String),
    Resolved(SymbolID),
}

impl FuncName {
    pub fn replace(&mut self, func_name: FuncName) {
        *self = func_name
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Name {
    Raw(String),
    Resolved(SymbolID),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Expr {
    LiteralInt(&'static str),
    LiteralFloat(&'static str),
    LiteralTrue,
    LiteralFalse,
    Unary(TokenKind, ExprID),
    Binary(ExprID, TokenKind, ExprID),
    Tuple(Vec<ExprID>),
    Block(Vec<ExprID>),
    Call(ExprID, Vec<ExprID>),

    // A type annotation
    TypeRepr(String, Vec<ExprID> /* generics */),

    // A dot thing
    Member(Option<ExprID> /* receiver */, String),

    // Function stuff
    Func(
        Option<FuncName>,
        Vec<ExprID>,    /* params tuple */
        ExprID,         /* body */
        Option<ExprID>, /* return type */
    ),
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
        ExprID, // TypeRepr name: "Option<T>"
        ExprID, // Body
    ),

    // Individual enum variant in declaration
    EnumVariant(
        Name,        // name: "some"
        Vec<ExprID>, // associated types: [TypeRepr("T")]
    ),

    // Match expression
    Match(
        ExprID, // scrutinee: the value being matched
        ExprID, // body
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

    // Member access for construction: Option.some(123)
    MemberAccess(
        ExprID, // base: Variable("Option")
        Name,   // member: "some"
    ),
}
