use std::{
    cell::RefCell,
    collections::HashMap,
    rc::Rc,
    sync::{Arc, Mutex},
};

use tracing::trace_span;

use crate::{
    SymbolID, environment::Environment, name::ResolvedName, parser::ExprID,
    substitutions::Substitutions, token_kind::TokenKind, ty::Ty,
};

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

#[derive(Debug, Clone, PartialEq, Eq)]
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

    pub fn apply(&mut self, substitutions: &mut Substitutions, env: &mut Environment) {
        let _s = trace_span!(
            "applying",
            self = format!("{self:?}"),
            subs = format!("{:?}", substitutions.apply(&self.ty, 0, &mut env.context))
        )
        .entered();

        self.ty = substitutions.apply(&self.ty, 0, &mut env.context);

        match &mut self.expr {
            Expr::LiteralArray(items) => {
                Self::apply_mult(items, substitutions, env);
            }
            Expr::LiteralInt(_) => (),
            Expr::LiteralFloat(_) => (),
            Expr::LiteralTrue => (),
            Expr::LiteralFalse => (),
            Expr::LiteralString(_) => (),
            Expr::Unary(_, rhs) => rhs.apply(substitutions, env),
            Expr::Binary(lhs, _, rhs) => {
                lhs.apply(substitutions, env);
                rhs.apply(substitutions, env);
            }
            Expr::Tuple(items) => {
                Self::apply_mult(items, substitutions, env);
            }
            Expr::Block(items) => {
                Self::apply_mult(items, substitutions, env);
            }
            Expr::Call {
                callee,
                type_args,
                args,
            } => {
                callee.apply(substitutions, env);
                Self::apply_mult(type_args, substitutions, env);
                Self::apply_mult(args, substitutions, env);
            }
            Expr::ParsedPattern(pattern) => todo!(),
            Expr::Return(ret) => {
                if let Some(ret) = ret {
                    ret.apply(substitutions, env)
                }
            }
            Expr::Break => (),
            Expr::Extend {
                generics,
                conformances,
                body,
                ..
            } => {
                Self::apply_mult(conformances, substitutions, env);
                Self::apply_mult(generics, substitutions, env);
                body.apply(substitutions, env);
            }
            Expr::Struct {
                generics,
                conformances,
                body,
                ..
            } => {
                Self::apply_mult(conformances, substitutions, env);
                Self::apply_mult(generics, substitutions, env);
                body.apply(substitutions, env);
            }
            Expr::Property {
                type_repr,
                default_value,
                ..
            } => {
                type_repr.as_mut().map(|t| t.apply(substitutions, env));
                default_value.as_mut().map(|t| t.apply(substitutions, env));
            }
            Expr::TypeRepr {
                generics,
                conformances,
                ..
            } => {
                Self::apply_mult(conformances, substitutions, env);
                Self::apply_mult(generics, substitutions, env);
            }
            Expr::FuncTypeRepr(params, ret, _) => {
                Self::apply_mult(params, substitutions, env);
                ret.apply(substitutions, env);
            }
            Expr::TupleTypeRepr(typed_exprs, _) => {
                Self::apply_mult(typed_exprs, substitutions, env)
            }
            Expr::Member(typed_expr, _) => {
                typed_expr.as_mut().map(|t| t.apply(substitutions, env));
            }
            Expr::Init(_, typed_expr) => typed_expr.apply(substitutions, env),
            Expr::Func {
                generics,
                params,
                body,
                ret,
                ..
            } => {
                Self::apply_mult(generics, substitutions, env);
                Self::apply_mult(params, substitutions, env);
                body.apply(substitutions, env);
                ret.as_mut().map(|t| t.apply(substitutions, env));
            }
            Expr::Parameter(_, typed_expr) => {
                if let Some(t) = typed_expr.as_mut() {
                    t.apply(substitutions, env)
                }
            }
            Expr::CallArg { value, .. } => value.apply(substitutions, env),
            Expr::Let(_, typed_expr) => {
                if let Some(t) = typed_expr.as_mut() {
                    t.apply(substitutions, env)
                }
            }
            Expr::Assignment(lhs, rhs) => {
                lhs.apply(substitutions, env);
                rhs.apply(substitutions, env);
            }
            Expr::Variable(_) => (),
            Expr::If(cond, conseq, alt) => {
                cond.apply(substitutions, env);
                conseq.apply(substitutions, env);
                if let Some(t) = alt.as_mut() {
                    t.apply(substitutions, env)
                }
            }
            Expr::Loop(cond, body) => {
                if let Some(t) = cond.as_mut() {
                    t.apply(substitutions, env)
                }
                body.apply(substitutions, env);
            }
            Expr::EnumDecl {
                conformances,
                generics,
                body,
                ..
            } => {
                Self::apply_mult(conformances, substitutions, env);
                Self::apply_mult(generics, substitutions, env);
                body.apply(substitutions, env);
            }
            Expr::EnumVariant(_, typed_exprs) => Self::apply_mult(typed_exprs, substitutions, env),
            Expr::Match(pattern, arms) => {
                pattern.apply(substitutions, env);
                Self::apply_mult(arms, substitutions, env);
            }
            Expr::MatchArm(pattern, body) => {
                pattern.apply(substitutions, env);
                body.apply(substitutions, env);
            }
            Expr::PatternVariant(_, _, values) => {
                Self::apply_mult(values, substitutions, env);
            }
            Expr::ProtocolDecl {
                associated_types,
                body,
                conformances,
                ..
            } => {
                Self::apply_mult(associated_types, substitutions, env);
                Self::apply_mult(conformances, substitutions, env);
                body.apply(substitutions, env);
            }
            Expr::FuncSignature {
                params,
                generics,
                ret,
                ..
            } => {
                Self::apply_mult(params, substitutions, env);
                Self::apply_mult(generics, substitutions, env);
                ret.apply(substitutions, env);
            }
        }
    }

    pub fn find(&self, id: ExprID) -> Option<&TypedExpr> {
        let _s = trace_span!("finding",).entered();

        if id == self.id {
            return Some(self);
        }

        match &self.expr {
            Expr::LiteralArray(items) => Self::find_in(items, id),
            Expr::LiteralInt(_) => None,
            Expr::LiteralFloat(_) => None,
            Expr::LiteralTrue => None,
            Expr::LiteralFalse => None,
            Expr::LiteralString(_) => None,
            Expr::Unary(_, rhs) => rhs.find(id),
            Expr::Binary(lhs, _, rhs) => lhs.find(id).or_else(|| rhs.find(id)),
            Expr::Tuple(items) => Self::find_in(items, id),
            Expr::Block(items) => Self::find_in(items, id),
            Expr::Call {
                callee,
                type_args,
                args,
            } => callee
                .find(id)
                .or_else(|| Self::find_in(type_args, id))
                .or_else(|| Self::find_in(args, id)),
            Expr::ParsedPattern(pattern) => None,
            Expr::Return(ret) => ret.as_ref().and_then(|t| t.find(id)),
            Expr::Break => None,
            Expr::Extend {
                generics,
                conformances,
                body,
                ..
            } => Self::find_in(conformances, id)
                .or_else(|| Self::find_in(generics, id))
                .or_else(|| body.find(id)),
            Expr::Struct {
                generics,
                conformances,
                body,
                ..
            } => Self::find_in(conformances, id)
                .or_else(|| Self::find_in(generics, id))
                .or_else(|| body.find(id)),
            Expr::Property {
                type_repr,
                default_value,
                ..
            } => type_repr
                .as_ref()
                .and_then(|t| t.find(id))
                .or_else(|| default_value.as_ref().and_then(|t| t.find(id))),
            Expr::TypeRepr {
                generics,
                conformances,
                ..
            } => Self::find_in(conformances, id).or_else(|| Self::find_in(generics, id)),
            Expr::FuncTypeRepr(params, ret, _) => {
                Self::find_in(params, id).or_else(|| ret.find(id))
            }
            Expr::TupleTypeRepr(typed_exprs, _) => Self::find_in(typed_exprs, id),
            Expr::Member(receiver, _) => receiver.as_ref().and_then(|t| t.find(id)),
            Expr::Init(_, typed_expr) => typed_expr.find(id),
            Expr::Func {
                generics,
                params,
                body,
                ret,
                ..
            } => body
                .find(id)
                .or_else(|| Self::find_in(generics, id))
                .or_else(|| Self::find_in(params, id))
                .or_else(|| ret.as_ref().and_then(|t| t.find(id))),
            Expr::Parameter(_, typed_expr) => typed_expr.as_ref().and_then(|t| t.find(id)),
            Expr::CallArg { value, .. } => value.find(id),
            Expr::Let(_, typed_expr) => typed_expr.as_ref().and_then(|t| t.find(id)),
            Expr::Assignment(lhs, rhs) => lhs.find(id).or_else(|| rhs.find(id)),
            Expr::Variable(_) => None,
            Expr::If(cond, conseq, alt) => cond
                .find(id)
                .or_else(|| conseq.find(id))
                .or_else(|| alt.as_ref().and_then(|t| t.find(id))),
            Expr::Loop(cond, body) => body
                .find(id)
                .or_else(|| cond.as_ref().and_then(|t| t.find(id))),
            Expr::EnumDecl {
                conformances,
                generics,
                body,
                ..
            } => Self::find_in(conformances, id)
                .or_else(|| Self::find_in(generics, id))
                .or_else(|| body.find(id)),
            Expr::EnumVariant(_, typed_exprs) => Self::find_in(typed_exprs, id),
            Expr::Match(pattern, arms) => pattern.find(id).or_else(|| Self::find_in(arms, id)),
            Expr::MatchArm(pattern, body) => pattern.find(id).or_else(|| body.find(id)),
            Expr::PatternVariant(_, _, values) => Self::find_in(values, id),
            Expr::ProtocolDecl {
                associated_types,
                body,
                conformances,
                ..
            } => Self::find_in(associated_types, id)
                .or_else(|| Self::find_in(conformances, id))
                .or_else(|| body.find(id)),
            Expr::FuncSignature {
                params,
                generics,
                ret,
                ..
            } => Self::find_in(params, id)
                .or_else(|| Self::find_in(generics, id))
                .or_else(|| ret.find(id)),
        }
    }

    pub fn apply_mult(
        exprs: &mut [TypedExpr],
        substitutions: &mut Substitutions,
        env: &mut Environment,
    ) {
        for expr in exprs {
            expr.apply(substitutions, env);
        }
    }

    pub fn find_in<'a>(exprs: &'a [TypedExpr], id: ExprID) -> Option<&'a TypedExpr> {
        for expr in exprs {
            if let Some(result) = expr.find(id) {
                return Some(result);
            }
        }

        None
    }
}
