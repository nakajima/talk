use crate::{SymbolID, name::ResolvedName, parser::ExprID, token_kind::TokenKind, ty::Ty};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Pattern {
    LiteralInt(String),
    LiteralFloat(String),
    LiteralTrue,
    LiteralFalse,

    Bind(ResolvedName),

    Wildcard,

    Variant {
        enum_name: Option<ResolvedName>,
        variant_name: String,
        fields: Vec<TypedExpr>,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Expr {
    LiteralArray(Vec<TypedExpr>),
    LiteralInt(String),
    LiteralFloat(String),
    LiteralTrue,
    LiteralFalse,
    LiteralString(String),
    Unary(TokenKind, Box<TypedExpr>),
    Binary(Box<TypedExpr>, TokenKind, Box<TypedExpr>),
    Tuple(Vec<TypedExpr>),
    Block(Vec<TypedExpr>),
    Call {
        callee: Box<TypedExpr>,
        type_args: Vec<TypedExpr>,
        args: Vec<TypedExpr>,
    },
    ParsedPattern(Pattern),
    Return(Option<Box<TypedExpr>>),
    Break,
    Extend {
        name: ResolvedName,
        generics: Vec<TypedExpr>,
        conformances: Vec<TypedExpr>,
        body: Box<TypedExpr>,
    },
    Struct {
        name: ResolvedName,
        generics: Vec<TypedExpr>,
        conformances: Vec<TypedExpr>,
        body: Box<TypedExpr>,
    },

    Property {
        name: ResolvedName,
        type_repr: Option<Box<TypedExpr>>,
        default_value: Option<Box<TypedExpr>>,
    },

    // A type annotation
    TypeRepr {
        name: ResolvedName,
        generics: Vec<TypedExpr>,
        conformances: Vec<TypedExpr>,
        introduces_type: bool,
    },

    FuncTypeRepr(Vec<TypedExpr>, Box<TypedExpr>, bool),

    TupleTypeRepr(Vec<TypedExpr>, bool),

    // A dot thing
    Member(Option<Box<TypedExpr>> /* receiver */, String),

    Init(SymbolID, Box<TypedExpr> /* func */),

    // Function stuff
    Func {
        name: Option<ResolvedName>,
        generics: Vec<TypedExpr>,
        params: Vec<TypedExpr>,
        body: Box<TypedExpr>,
        ret: Option<Box<TypedExpr>>,
        captures: Vec<SymbolID>,
    },

    Parameter(ResolvedName, Option<Box<TypedExpr>>),
    CallArg {
        label: Option<ResolvedName>,
        value: Box<TypedExpr>,
    },

    // Variables
    Let(ResolvedName, Option<Box<TypedExpr>>),
    Assignment(Box<TypedExpr>, Box<TypedExpr>),
    Variable(ResolvedName),

    If(Box<TypedExpr>, Box<TypedExpr>, Option<Box<TypedExpr>>),

    Loop(Option<Box<TypedExpr>>, Box<TypedExpr> /* body */),

    // Enum declaration
    EnumDecl {
        name: ResolvedName,
        conformances: Vec<TypedExpr>,
        generics: Vec<TypedExpr>,
        body: Box<TypedExpr>,
    },

    // Individual enum variant in declaration
    EnumVariant(ResolvedName, Vec<TypedExpr>),

    // Match expression
    Match(Box<TypedExpr>, Vec<TypedExpr>),

    // Individual match arm
    MatchArm(Box<TypedExpr>, Box<TypedExpr>),

    // Patterns (for match arms)
    PatternVariant(Option<ResolvedName>, ResolvedName, Vec<TypedExpr>),

    ProtocolDecl {
        name: ResolvedName,
        associated_types: Vec<TypedExpr>,
        body: Box<TypedExpr>,
        conformances: Vec<TypedExpr>,
    },

    FuncSignature {
        name: ResolvedName,
        params: Vec<TypedExpr>,
        generics: Vec<TypedExpr>,
        ret: Box<TypedExpr>,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TypedExpr {
    pub id: ExprID,
    pub expr: Expr,
    pub ty: Ty,
}

impl TypedExpr {
    pub fn new(id: ExprID, expr: Expr, ty: Ty) -> Self {
        Self { id, expr, ty }
    }
}
