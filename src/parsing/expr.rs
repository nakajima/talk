use crate::token::Token;
use std::ops::Range;
pub type VarDepth = u32;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct ExprMeta {
    pub start: Token,
    pub end: Token,
    pub identifiers: Vec<Token>,
}

impl ExprMeta {
    pub fn generated() -> Self {
        Self {
            start: Token::GENERATED,
            end: Token::GENERATED,
            identifiers: vec![],
        }
    }

    pub fn source_range(&self) -> Range<u32> {
        self.start.start..self.end.end
    }
}

// pub type SharedExpr = Rc<RefCell<Expr>>;

// #[derive(Clone, Debug, PartialEq, Eq)]
// pub enum Expr {
//     // These first expressions only exist to assist with LSP operations
//     Incomplete(IncompleteExpr),

//     // Start of the real expressions
//     LiteralArray(Vec<SharedExpr>),
//     LiteralInt(String),
//     LiteralFloat(String),
//     LiteralTrue,
//     LiteralFalse,
//     LiteralString(String),
//     Unary(TokenKind, SharedExpr),
//     Binary(SharedExpr, TokenKind, SharedExpr),
//     Tuple(Vec<SharedExpr>),
//     Block(Vec<SharedExpr>),
//     Call {
//         callee: SharedExpr,
//         type_args: Vec<SharedExpr>,
//         args: Vec<SharedExpr>,
//     },
//     Pattern(Pattern),
//     Return(Option<SharedExpr>),
//     Break,
//     Extend {
//         name: Name,                /* name */
//         generics: Vec<SharedExpr>, /* generics */
//         conformances: Vec<SharedExpr>,
//         body: SharedExpr, /* body */
//     },
//     Struct {
//         name: Name,                /* name */
//         generics: Vec<SharedExpr>, /* generics */
//         conformances: Vec<SharedExpr>,
//         body: SharedExpr, /* body */
//     },

//     Property {
//         name: Name,
//         type_repr: Option<SharedExpr>,
//         default_value: Option<SharedExpr>,
//     },

//     // A type annotation
//     TypeRepr {
//         name: Name,
//         generics: Vec<SharedExpr>, /* generics */
//         conformances: Vec<SharedExpr>,
//         introduces_type: bool, /* is this a generic type parameter (if so we need to declare it in a scope) */
//     },

//     FuncTypeRepr(
//         Vec<SharedExpr>, /* [TypeRepr] args */
//         SharedExpr,      /* return TypeRepr */
//         bool, /* is this a generic type parameter (if so we need to declare it in a scope) */
//     ),

//     TupleTypeRepr(
//         Vec<SharedExpr>, /* (T1, T2) */
//         bool, /* is this a generic type parameter (if so we need to declare it in a scope) */
//     ),

//     // A dot thing
//     Member(Option<SharedExpr> /* receiver */, String),

//     Init(Option<SymbolID>, SharedExpr /* func */),

//     // Function stuff
//     Func {
//         name: Option<Name>,
//         generics: Vec<SharedExpr>,
//         params: Vec<SharedExpr>, /* params tuple */
//         body: SharedExpr,        /* body */
//         ret: Option<SharedExpr>, /* return type */
//         captures: Vec<SymbolID>,
//     },

//     Parameter(Name /* name */, Option<SharedExpr> /* TypeRepr */),
//     CallArg {
//         label: Option<Name>,
//         value: SharedExpr,
//     },

//     // Variables
//     Let(
//         Name,               /* name */
//         Option<SharedExpr>, /* type annotation */
//     ),
//     Assignment(SharedExpr /* LHS */, SharedExpr /* RHS */),
//     Variable(Name, Option<SharedExpr>),

//     // For name resolution
//     // ResolvedVariable(SymbolID, Option<SharedExpr>),
//     // ResolvedLet(SymbolID, Option<SharedExpr> /* RHS */),

//     // Control flow
//     If(
//         SharedExpr,         /* condition */
//         SharedExpr,         /* condition block */
//         Option<SharedExpr>, /* else block */
//     ),

//     Loop(
//         Option<SharedExpr>, /* condition */
//         SharedExpr,         /* body */
//     ),

//     // Enum declaration
//     EnumDecl {
//         name: Name, // TypeRepr name: Option
//         conformances: Vec<SharedExpr>,
//         generics: Vec<SharedExpr>, // Generics TypeParams <T>
//         body: SharedExpr,          // Body
//     },

//     // Individual enum variant in declaration
//     EnumVariant(
//         Name,            // name: "some"
//         Vec<SharedExpr>, // associated types: [TypeRepr("T")]
//     ),

//     // Match expression
//     Match(
//         SharedExpr,      // scrutinee: the value being matched
//         Vec<SharedExpr>, // arms: [MatchArm(pattern, body)]
//     ),

//     // Individual match arm
//     MatchArm(
//         SharedExpr, // pattern
//         SharedExpr, // body (after ->)
//     ),

//     // Patterns (for match arms)
//     PatternVariant(
//         Option<Name>,    // enum name (None for unqualified .some)
//         Name,            // variant name: "some"
//         Vec<SharedExpr>, // bindings: ["wrapped"]
//     ),

//     ProtocolDecl {
//         name: Name,
//         associated_types: Vec<SharedExpr>, // Associated types
//         body: SharedExpr,                  // Body ID
//         conformances: Vec<SharedExpr>,
//     },

//     FuncSignature {
//         name: Name,
//         params: Vec<SharedExpr>,
//         generics: Vec<SharedExpr>,
//         ret: SharedExpr,
//     },
// }

// impl Expr {
//     pub fn symbol_id(&self) -> Option<SymbolID> {
//         match self {
//             Expr::Struct {
//                 name: Name::Resolved(symbol_id, _),
//                 ..
//             } => Some(*symbol_id),
//             Expr::Property {
//                 name: Name::Resolved(symbol_id, _),
//                 ..
//             } => Some(*symbol_id),
//             Expr::TypeRepr {
//                 name: Name::Resolved(symbol_id, _),
//                 ..
//             } => Some(*symbol_id),
//             Expr::Init(symbol_id, _) => *symbol_id,
//             Expr::Func {
//                 name: Some(Name::Resolved(symbol_id, _)),
//                 ..
//             } => Some(*symbol_id),
//             Expr::Parameter(Name::Resolved(symbol_id, _), _) => Some(*symbol_id),
//             Expr::CallArg {
//                 label: Some(Name::Resolved(symbol_id, _)),
//                 ..
//             } => Some(*symbol_id),
//             Expr::Let(Name::Resolved(symbol_id, _), _) => Some(*symbol_id),
//             Expr::Variable(Name::Resolved(symbol_id, _), _) => Some(*symbol_id),
//             Expr::EnumDecl {
//                 name: Name::Resolved(symbol_id, _),
//                 ..
//             } => Some(*symbol_id),
//             Expr::EnumVariant(Name::Resolved(symbol_id, _), _) => Some(*symbol_id),
//             Expr::ProtocolDecl {
//                 name: Name::Resolved(symbol_id, _),
//                 ..
//             } => Some(*symbol_id),
//             Expr::FuncSignature {
//                 name: Name::Resolved(symbol_id, _),
//                 ..
//             } => Some(*symbol_id),
//             _ => None,
//         }
//     }
// }
