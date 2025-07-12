use crate::{
    Phase, SourceFile, SymbolID,
    expr::{Expr, IncompleteExpr, Pattern},
    name::Name,
    parser::ExprID,
    token::Token,
    token_kind::TokenKind,
};

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum FilledIncomplete {
    Member(Option<Box<FullExpr>>),
    Func {
        name: Option<Name>,
        params: Option<Vec<FullExpr>>,
        generics: Option<Vec<FullExpr>>,
        ret: Option<Box<FullExpr>>,
        body: Option<Box<FullExpr>>,
    },
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum FullExpr {
    Incomplete(FilledIncomplete),

    LiteralArray(Vec<FullExpr>),
    LiteralInt(String),
    LiteralFloat(String),
    LiteralTrue,
    LiteralFalse,
    LiteralString(String),
    Unary(TokenKind, Box<FullExpr>),
    Binary(Box<FullExpr>, TokenKind, Box<FullExpr>),
    Tuple(Vec<FullExpr>),
    Block(Vec<FullExpr>),
    Call {
        callee: Box<FullExpr>,
        type_args: Vec<FullExpr>,
        args: Vec<FullExpr>,
    },
    Pattern(Pattern),
    Return(Box<Option<FullExpr>>),
    Break,
    Struct {
        name: Name,              /* name */
        generics: Vec<FullExpr>, /* generics */
        conformances: Vec<FullExpr>,
        body: Box<FullExpr>, /* body */
    },
    Extend {
        name: Name,
        generics: Vec<FullExpr>,
        conformances: Vec<FullExpr>,
        body: Box<FullExpr>,
    },
    Property {
        name: Name,
        type_repr: Box<Option<FullExpr>>,
        default_value: Box<Option<FullExpr>>,
    },

    // A type annotation
    TypeRepr {
        name: Name,
        generics: Vec<FullExpr>, /* generics */
        conformances: Vec<FullExpr>,
        introduces_type: bool, /* is this a generic type parameter (if so we need to declare it in a scope) */
    },

    FuncTypeRepr(
        Vec<FullExpr>, /* [TypeRepr] args */
        Box<FullExpr>, /* return TypeRepr */
        bool, /* is this a generic type parameter (if so we need to declare it in a scope) */
    ),

    TupleTypeRepr(
        Vec<FullExpr>, /* (T1, T2) */
        bool, /* is this a generic type parameter (if so we need to declare it in a scope) */
    ),

    // A dot thing
    Member(Box<Option<FullExpr>> /* receiver */, String),

    Init(Option<SymbolID>, Box<FullExpr> /* func */),

    // Function stuff
    Func {
        name: Option<Name>,
        generics: Vec<FullExpr>,
        params: Vec<FullExpr>,      /* params tuple */
        body: Box<FullExpr>,        /* body */
        ret: Box<Option<FullExpr>>, /* return type */
        captures: Vec<SymbolID>,
        effects: Vec<Token>,
    },

    Parameter(
        Name,                  /* name */
        Box<Option<FullExpr>>, /* TypeRepr */
    ),
    CallArg {
        label: Option<Name>,
        value: Box<FullExpr>,
    },

    // Variables
    Let(
        Name,                  /* name */
        Box<Option<FullExpr>>, /* type annotation */
    ),
    Assignment(Box<FullExpr> /* LHS */, Box<FullExpr> /* RHS */),
    Variable(Name, Box<Option<FullExpr>>),

    // For name resolution
    // ResolvedVariable(SymbolID, Option< FullExpr>),
    // ResolvedLet(SymbolID, Option< FullExpr> /* RHS */),

    // Control flow
    If(
        Box<FullExpr>,         /* condition */
        Box<FullExpr>,         /* condition block */
        Box<Option<FullExpr>>, /* else block */
    ),

    Loop(
        Box<Option<FullExpr>>, /* condition */
        Box<FullExpr>,         /* body */
    ),

    // Enum declaration
    EnumDecl {
        name: Name,              // TypeRepr name: Option
        generics: Vec<FullExpr>, // Generics TypeParams <T>
        conformances: Vec<FullExpr>,
        body: Box<FullExpr>, // Body
    },

    // Individual enum variant in declaration
    EnumVariant(
        Name,          // name: "some"
        Vec<FullExpr>, // associated types: [TypeRepr("T")]
    ),

    Await(Box<FullExpr>),

    // Match expression
    Match(
        Box<FullExpr>, // scrutinee: the value being matched
        Vec<FullExpr>, // arms: [MatchArm(pattern, body)]
    ),

    // Individual match arm
    MatchArm(
        Box<FullExpr>, // pattern
        Box<FullExpr>, // body (after ->)
    ),

    // Patterns (for match arms)
    PatternVariant(
        Option<Name>,  // enum name (None for unqualified .some)
        Name,          // variant name: "some"
        Vec<FullExpr>, // bindings: ["wrapped"]
    ),

    ProtocolDecl {
        name: Name,
        associated_types: Vec<FullExpr>, // Associated types
        body: Box<FullExpr>,             // Body ID
        conformances: Vec<FullExpr>,
    },

    FuncSignature {
        name: Name,
        params: Vec<FullExpr>,
        generics: Vec<FullExpr>,
        ret: Box<FullExpr>,
    },
}

pub struct Filler<P: Phase> {
    source: SourceFile<P>,
}

impl<P: Phase> Filler<P> {
    pub fn new(source: SourceFile<P>) -> Self {
        Self { source }
    }

    pub fn fill_root(&self) -> Vec<FullExpr> {
        let mut full_exprs = Vec::new();
        for root_id in self.source.root_ids() {
            full_exprs.push(self.fill(root_id));
        }
        full_exprs
    }

    fn fill_mult(&self, expr_ids: &Vec<ExprID>) -> Vec<FullExpr> {
        let mut result = vec![];
        for id in expr_ids {
            result.push(self.fill(*id));
        }
        result
    }

    pub fn fill(&self, expr_id: ExprID) -> FullExpr {
        #[allow(clippy::unwrap_used)]
        let expr = self.source.get(&expr_id).unwrap();

        match expr.clone() {
            Expr::Incomplete(e) => match e {
                IncompleteExpr::Member(rec) => FullExpr::Incomplete(FilledIncomplete::Member(
                    rec.map(|rec| self.fill(rec).into()),
                )),
                IncompleteExpr::Func {
                    name,
                    params,
                    generics,
                    ret,
                    body,
                } => FullExpr::Incomplete(FilledIncomplete::Func {
                    name,
                    params: params.map(|p| self.fill_mult(&p)),
                    generics: generics.map(|p| self.fill_mult(&p)),
                    ret: ret.map(|r| self.fill(r).into()),
                    body: body.map(|b| self.fill(b).into()),
                }),
            },
            Expr::Await(id) => FullExpr::Await(self.fill(id).into()),
            Expr::LiteralInt(s) => FullExpr::LiteralInt(s),
            Expr::LiteralString(s) => FullExpr::LiteralString(s),
            Expr::Unary(op, rhs_id) => {
                let rhs = self.fill(rhs_id);
                FullExpr::Unary(op, rhs.into())
            }
            Expr::Binary(lhs_id, op, rhs_id) => {
                let lhs = self.fill(lhs_id);
                let rhs = self.fill(rhs_id);
                FullExpr::Binary(lhs.into(), op, rhs.into())
            }
            Expr::Block(expr_ids) => {
                let children = expr_ids.iter().map(|id| self.fill(*id)).collect();
                FullExpr::Block(children)
            }
            Expr::Tuple(expr_ids) => {
                let children = expr_ids.iter().map(|id| self.fill(*id)).collect();
                FullExpr::Tuple(children)
            }
            Expr::Let(name, type_repr_id) => {
                let type_repr = type_repr_id.map(|id| self.fill(id));
                FullExpr::Let(name, type_repr.into())
            }
            Expr::If(cond_id, then_id, else_id) => {
                let cond = self.fill(cond_id);
                let then_block = self.fill(then_id);
                let else_block = else_id.map(|id| self.fill(id));
                FullExpr::If(cond.into(), then_block.into(), else_block.into())
            }
            Expr::LiteralArray(items) => FullExpr::LiteralArray(self.fill_mult(&items)),
            Expr::LiteralFloat(val) => FullExpr::LiteralFloat(val),
            Expr::LiteralTrue => FullExpr::LiteralTrue,
            Expr::LiteralFalse => FullExpr::LiteralFalse,
            Expr::Call {
                callee,
                type_args,
                args,
            } => FullExpr::Call {
                callee: self.fill(callee).into(),
                type_args: self.fill_mult(&type_args),
                args: self.fill_mult(&args),
            },
            Expr::Pattern(pattern) => FullExpr::Pattern(pattern),
            Expr::Return(rhs) => FullExpr::Return(rhs.map(|rhs| self.fill(rhs)).into()),
            Expr::Break => FullExpr::Break,
            Expr::Struct {
                name,
                generics,
                conformances,
                body,
            } => FullExpr::Struct {
                name,
                generics: self.fill_mult(&generics),
                conformances: self.fill_mult(&conformances),
                body: self.fill(body).into(),
            },
            Expr::Extend {
                name,
                generics,
                conformances,
                body,
            } => FullExpr::Extend {
                name,
                generics: self.fill_mult(&generics),
                conformances: self.fill_mult(&conformances),
                body: self.fill(body).into(),
            },
            Expr::Property {
                name,
                type_repr,
                default_value,
            } => FullExpr::Property {
                name,
                type_repr: type_repr.map(|type_repr| self.fill(type_repr)).into(),
                default_value: default_value
                    .map(|default_value| self.fill(default_value))
                    .into(),
            },
            Expr::TypeRepr {
                name,
                generics,
                conformances,
                introduces_type,
            } => FullExpr::TypeRepr {
                name,
                generics: self.fill_mult(&generics),
                conformances: self.fill_mult(&conformances),
                introduces_type,
            },
            Expr::FuncTypeRepr(items, ret, introduces_vars) => FullExpr::FuncTypeRepr(
                self.fill_mult(&items),
                self.fill(ret).into(),
                introduces_vars,
            ),
            Expr::TupleTypeRepr(items, introduces_vars) => {
                FullExpr::TupleTypeRepr(self.fill_mult(&items), introduces_vars)
            }
            Expr::Member(receiver, name) => {
                FullExpr::Member(receiver.map(|receiver| self.fill(receiver)).into(), name)
            }
            Expr::Init(symbol_id, func) => FullExpr::Init(symbol_id, self.fill(func).into()),
            Expr::Func {
                name,
                generics,
                params,
                body,
                ret,
                captures,
                effects,
            } => FullExpr::Func {
                name,
                generics: self.fill_mult(&generics),
                params: self.fill_mult(&params),
                body: self.fill(body).into(),
                ret: ret.map(|ret| self.fill(ret)).into(),
                captures,
                effects,
            },
            Expr::Parameter(name, type_repr) => {
                FullExpr::Parameter(name, type_repr.map(|type_repr| self.fill(type_repr)).into())
            }
            Expr::CallArg { label, value } => FullExpr::CallArg {
                label,
                value: self.fill(value).into(),
            },
            Expr::Assignment(lhs, rhs) => {
                FullExpr::Assignment(self.fill(lhs).into(), self.fill(rhs).into())
            }
            Expr::Variable(name, type_repr) => {
                FullExpr::Variable(name, type_repr.map(|type_repr| self.fill(type_repr)).into())
            }
            Expr::Loop(cond, body) => FullExpr::Loop(
                cond.map(|cond| self.fill(cond)).into(),
                self.fill(body).into(),
            ),
            Expr::EnumDecl {
                name,
                generics,
                conformances,
                body,
            } => FullExpr::EnumDecl {
                name,
                generics: self.fill_mult(&generics),
                conformances: self.fill_mult(&conformances),
                body: self.fill(body).into(),
            },
            Expr::EnumVariant(name, items) => FullExpr::EnumVariant(name, self.fill_mult(&items)),
            Expr::Match(scrutinee, items) => {
                FullExpr::Match(self.fill(scrutinee).into(), self.fill_mult(&items))
            }
            Expr::MatchArm(pattern, body) => {
                FullExpr::MatchArm(self.fill(pattern).into(), self.fill(body).into())
            }
            Expr::PatternVariant(name, name1, items) => {
                FullExpr::PatternVariant(name, name1, self.fill_mult(&items))
            }
            Expr::ProtocolDecl {
                name,
                associated_types,
                body,
                conformances,
            } => FullExpr::ProtocolDecl {
                name,
                associated_types: self.fill_mult(&associated_types),
                body: self.fill(body).into(),
                conformances: self.fill_mult(&conformances),
            },
            Expr::FuncSignature {
                name,
                params,
                generics,
                ret,
            } => FullExpr::FuncSignature {
                name,
                params: self.fill_mult(&params),
                generics: self.fill_mult(&generics),
                ret: self.fill(ret).into(),
            },
        }
    }
}
