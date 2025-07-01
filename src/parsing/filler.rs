use typed_arena::Arena;

use crate::{
    Phase, SourceFile, SymbolID,
    expr::{Expr, Pattern},
    name::Name,
    parser::ExprID,
    token_kind::TokenKind,
};

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum FullExpr<'a> {
    LiteralArray(Vec<&'a FullExpr<'a>>),
    LiteralInt(&'a str),
    LiteralFloat(&'a str),
    LiteralTrue,
    LiteralFalse,
    Unary(&'a TokenKind, &'a FullExpr<'a>),
    Binary(&'a FullExpr<'a>, &'a TokenKind, &'a FullExpr<'a>),
    Tuple(Vec<&'a FullExpr<'a>>),
    Block(Vec<&'a FullExpr<'a>>),
    Call {
        callee: &'a FullExpr<'a>,
        type_args: Vec<&'a FullExpr<'a>>,
        args: Vec<&'a FullExpr<'a>>,
    },
    Pattern(&'a Pattern),
    Return(Option<&'a FullExpr<'a>>),
    Break,
    Struct {
        name: &'a Name,                  /* name */
        generics: Vec<&'a FullExpr<'a>>, /* generics */
        conformances: Vec<&'a FullExpr<'a>>,
        body: &'a FullExpr<'a>, /* body */
    },
    Property {
        name: &'a Name,
        type_repr: Option<&'a FullExpr<'a>>,
        default_value: Option<&'a FullExpr<'a>>,
    },

    // A type annotation
    TypeRepr {
        name: &'a Name,
        generics: Vec<&'a FullExpr<'a>>, /* generics */
        conformances: Vec<&'a FullExpr<'a>>,
        introduces_type: bool, /* is this a generic type parameter (if so we need to declare it in a scope) */
    },

    FuncTypeRepr(
        Vec<&'a FullExpr<'a>>, /* [TypeRepr] args */
        &'a FullExpr<'a>,      /* return TypeRepr */
        bool, /* is this a generic type parameter (if so we need to declare it in a scope) */
    ),

    TupleTypeRepr(
        Vec<&'a FullExpr<'a>>, /* (T1, T2) */
        bool, /* is this a generic type parameter (if so we need to declare it in a scope) */
    ),

    // A dot thing
    Member(Option<&'a FullExpr<'a>> /* receiver */, &'a str),

    Init(Option<SymbolID>, &'a FullExpr<'a> /* func */),

    // Function stuff
    Func {
        name: &'a Option<Name>,
        generics: Vec<&'a FullExpr<'a>>,
        params: Vec<&'a FullExpr<'a>>, /* params tuple */
        body: &'a FullExpr<'a>,        /* body */
        ret: Option<&'a FullExpr<'a>>, /* return type */
        captures: &'a Vec<SymbolID>,
    },

    Parameter(
        &'a Name,                 /* name */
        Option<&'a FullExpr<'a>>, /* TypeRepr */
    ),
    CallArg {
        label: &'a Option<Name>,
        value: &'a FullExpr<'a>,
    },

    // Variables
    Let(
        &'a Name,                 /* name */
        Option<&'a FullExpr<'a>>, /* type annotation */
    ),
    Assignment(
        &'a FullExpr<'a>, /* LHS */
        &'a FullExpr<'a>, /* RHS */
    ),
    Variable(&'a Name, Option<&'a FullExpr<'a>>),

    // For name resolution
    // ResolvedVariable(SymbolID, Option<&'a FullExpr<'a>>),
    // ResolvedLet(SymbolID, Option<&'a FullExpr<'a>> /* RHS */),

    // Control flow
    If(
        &'a FullExpr<'a>,         /* condition */
        &'a FullExpr<'a>,         /* condition block */
        Option<&'a FullExpr<'a>>, /* else block */
    ),

    Loop(
        Option<&'a FullExpr<'a>>, /* condition */
        &'a FullExpr<'a>,         /* body */
    ),

    // Enum declaration
    EnumDecl {
        name: &'a Name,                  // TypeRepr name: Option
        generics: Vec<&'a FullExpr<'a>>, // Generics TypeParams <T>
        conformances: Vec<&'a FullExpr<'a>>,
        body: &'a FullExpr<'a>, // Body
    },

    // Individual enum variant in declaration
    EnumVariant(
        &'a Name,              // name: "some"
        Vec<&'a FullExpr<'a>>, // associated types: [TypeRepr("T")]
    ),

    // Match expression
    Match(
        &'a FullExpr<'a>,      // scrutinee: the value being matched
        Vec<&'a FullExpr<'a>>, // arms: [MatchArm(pattern, body)]
    ),

    // Individual match arm
    MatchArm(
        &'a FullExpr<'a>, // pattern
        &'a FullExpr<'a>, // body (after ->)
    ),

    // Patterns (for match arms)
    PatternVariant(
        &'a Option<Name>,      // enum name (None for unqualified .some)
        &'a Name,              // variant name: "some"
        Vec<&'a FullExpr<'a>>, // bindings: ["wrapped"]
    ),

    ProtocolDecl {
        name: &'a Name,
        associated_types: Vec<&'a FullExpr<'a>>, // Associated types
        body: &'a FullExpr<'a>,                  // Body ID
        conformances: Vec<&'a FullExpr<'a>>,
    },

    FuncSignature {
        name: &'a Name,
        params: Vec<&'a FullExpr<'a>>,
        generics: Vec<&'a FullExpr<'a>>,
        ret: &'a FullExpr<'a>,
    },
}

pub struct Filler<'a, P: Phase> {
    source: &'a SourceFile<P>,
    arena: &'a Arena<FullExpr<'a>>,
}

impl<'a, P: Phase> Filler<'a, P> {
    pub fn new(source: &'a SourceFile<P>, arena: &'a Arena<FullExpr<'a>>) -> Self {
        Self { source, arena }
    }

    pub fn fill_root(&self) -> Vec<&'a FullExpr<'a>> {
        let mut full_exprs = Vec::new();
        for root_id in self.source.root_ids() {
            full_exprs.push(self.fill(root_id));
        }
        full_exprs
    }

    fn fill_mult(&self, expr_ids: &Vec<ExprID>) -> Vec<&'a FullExpr<'a>> {
        let mut result = vec![];
        for id in expr_ids {
            result.push(self.fill(*id));
        }
        result
    }

    pub fn fill(&self, expr_id: ExprID) -> &'a FullExpr<'a> {
        #[allow(clippy::unwrap_used)]
        let expr = self.source.get(&expr_id).unwrap();

        let full_expr = match expr {
            Expr::LiteralInt(s) => FullExpr::LiteralInt(s),
            Expr::Unary(op, rhs_id) => {
                let rhs = self.fill(*rhs_id);
                FullExpr::Unary(op, rhs)
            }
            Expr::Binary(lhs_id, op, rhs_id) => {
                let lhs = self.fill(*lhs_id);
                let rhs = self.fill(*rhs_id);
                FullExpr::Binary(lhs, op, rhs)
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
                FullExpr::Let(name, type_repr)
            }
            Expr::If(cond_id, then_id, else_id) => {
                let cond = self.fill(*cond_id);
                let then_block = self.fill(*then_id);
                let else_block = else_id.map(|id| self.fill(id));
                FullExpr::If(cond, then_block, else_block)
            }
            Expr::LiteralArray(items) => FullExpr::LiteralArray(self.fill_mult(items)),
            Expr::LiteralFloat(val) => FullExpr::LiteralFloat(val),
            Expr::LiteralTrue => FullExpr::LiteralTrue,
            Expr::LiteralFalse => FullExpr::LiteralFalse,
            Expr::Call {
                callee,
                type_args,
                args,
            } => FullExpr::Call {
                callee: self.fill(*callee),
                type_args: self.fill_mult(type_args),
                args: self.fill_mult(args),
            },
            Expr::Pattern(pattern) => FullExpr::Pattern(pattern),
            Expr::Return(rhs) => FullExpr::Return(rhs.map(|rhs| self.fill(rhs))),
            Expr::Break => FullExpr::Break,
            Expr::Struct {
                name,
                generics,
                conformances,
                body,
            } => FullExpr::Struct {
                name,
                generics: self.fill_mult(generics),
                conformances: self.fill_mult(conformances),
                body: self.fill(*body),
            },
            Expr::Property {
                name,
                type_repr,
                default_value,
            } => FullExpr::Property {
                name,
                type_repr: type_repr.map(|type_repr| self.fill(type_repr)),
                default_value: default_value.map(|default_value| self.fill(default_value)),
            },
            Expr::TypeRepr {
                name,
                generics,
                conformances,
                introduces_type,
            } => FullExpr::TypeRepr {
                name,
                generics: self.fill_mult(generics),
                conformances: self.fill_mult(conformances),
                introduces_type: *introduces_type,
            },
            Expr::FuncTypeRepr(items, ret, introduces_vars) => {
                FullExpr::FuncTypeRepr(self.fill_mult(items), self.fill(*ret), *introduces_vars)
            }
            Expr::TupleTypeRepr(items, introduces_vars) => {
                FullExpr::TupleTypeRepr(self.fill_mult(items), *introduces_vars)
            }
            Expr::Member(receiver, name) => {
                FullExpr::Member(receiver.map(|receiver| self.fill(receiver)), name)
            }
            Expr::Init(symbol_id, func) => FullExpr::Init(*symbol_id, self.fill(*func)),
            Expr::Func {
                name,
                generics,
                params,
                body,
                ret,
                captures,
            } => FullExpr::Func {
                name,
                generics: self.fill_mult(generics),
                params: self.fill_mult(params),
                body: self.fill(*body),
                ret: ret.map(|ret| self.fill(ret)),
                captures,
            },
            Expr::Parameter(name, type_repr) => {
                FullExpr::Parameter(name, type_repr.map(|type_repr| self.fill(type_repr)))
            }
            Expr::CallArg { label, value } => FullExpr::CallArg {
                label,
                value: self.fill(*value),
            },
            Expr::Assignment(lhs, rhs) => FullExpr::Assignment(self.fill(*lhs), self.fill(*rhs)),
            Expr::Variable(name, type_repr) => {
                FullExpr::Variable(name, type_repr.map(|type_repr| self.fill(type_repr)))
            }
            Expr::Loop(cond, body) => {
                FullExpr::Loop(cond.map(|cond| self.fill(cond)), self.fill(*body))
            }
            Expr::EnumDecl {
                name,
                generics,
                conformances,
                body,
            } => FullExpr::EnumDecl {
                name,
                generics: self.fill_mult(generics),
                conformances: self.fill_mult(conformances),
                body: self.fill(*body),
            },
            Expr::EnumVariant(name, items) => FullExpr::EnumVariant(name, self.fill_mult(items)),
            Expr::Match(scrutinee, items) => {
                FullExpr::Match(self.fill(*scrutinee), self.fill_mult(items))
            }
            Expr::MatchArm(pattern, body) => {
                FullExpr::MatchArm(self.fill(*pattern), self.fill(*body))
            }
            Expr::PatternVariant(name, name1, items) => {
                FullExpr::PatternVariant(name, name1, self.fill_mult(items))
            }
            Expr::ProtocolDecl {
                name,
                associated_types,
                body,
                conformances,
            } => FullExpr::ProtocolDecl {
                name,
                associated_types: self.fill_mult(associated_types),
                body: self.fill(*body),
                conformances: self.fill_mult(conformances),
            },
            Expr::FuncSignature {
                name,
                params,
                generics,
                ret,
            } => FullExpr::FuncSignature {
                name,
                params: self.fill_mult(params),
                generics: self.fill_mult(generics),
                ret: self.fill(*ret),
            },
        };

        self.arena.alloc(full_expr)
    }
}
