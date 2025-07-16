use std::{cell::RefCell, rc::Rc};

use derive_visitor::DriveMut;
use tracing::trace_span;

use crate::{
    ExprMetaStorage, SymbolID, environment::Environment, name::ResolvedName,
    parsing::expr_id::ExprID, substitutions::Substitutions, token_kind::TokenKind, ty::Ty,
};

#[derive(Clone, Debug, PartialEq, Eq, DriveMut)]
pub enum Pattern {
    LiteralInt(#[drive(skip)] String),
    LiteralFloat(#[drive(skip)] String),
    LiteralTrue,
    LiteralFalse,

    Bind(#[drive(skip)] ResolvedName),

    Wildcard,

    Variant {
        #[drive(skip)]
        enum_name: Option<ResolvedName>,
        #[drive(skip)]
        variant_name: String,
        fields: Vec<TypedExpr>,
    },
}

#[derive(Debug, Clone, PartialEq, Eq, DriveMut)]
pub enum Expr {
    LiteralArray(Vec<TypedExpr>),
    LiteralInt(#[drive(skip)] String),
    LiteralFloat(#[drive(skip)] String),
    LiteralTrue,
    LiteralFalse,
    LiteralString(#[drive(skip)] String),
    Unary(#[drive(skip)] TokenKind, Box<TypedExpr>),
    Binary(Box<TypedExpr>, #[drive(skip)] TokenKind, Box<TypedExpr>),
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
        #[drive(skip)]
        name: ResolvedName,
        generics: Vec<TypedExpr>,
        conformances: Vec<TypedExpr>,
        body: Box<TypedExpr>,
    },
    Struct {
        #[drive(skip)]
        name: ResolvedName,
        generics: Vec<TypedExpr>,
        conformances: Vec<TypedExpr>,
        body: Box<TypedExpr>,
    },

    Property {
        #[drive(skip)]
        name: ResolvedName,
        type_repr: Option<Box<TypedExpr>>,
        default_value: Option<Box<TypedExpr>>,
    },

    // A type annotation
    TypeRepr {
        #[drive(skip)]
        name: ResolvedName,
        generics: Vec<TypedExpr>,
        conformances: Vec<TypedExpr>,
        #[drive(skip)]
        introduces_type: bool,
    },

    FuncTypeRepr(Vec<TypedExpr>, Box<TypedExpr>, #[drive(skip)] bool),

    TupleTypeRepr(Vec<TypedExpr>, #[drive(skip)] bool),

    // A dot thing
    Member(
        Option<Box<TypedExpr>>, /* receiver */
        #[drive(skip)] String,
    ),

    Init(#[drive(skip)] SymbolID, Box<TypedExpr> /* func */),

    // Function stuff
    Func {
        #[drive(skip)]
        name: Option<ResolvedName>,
        generics: Vec<TypedExpr>,
        params: Vec<TypedExpr>,
        body: Box<TypedExpr>,
        ret: Option<Box<TypedExpr>>,
        #[drive(skip)]
        captures: Vec<SymbolID>,
    },

    Parameter(#[drive(skip)] ResolvedName, Option<Box<TypedExpr>>),
    CallArg {
        #[drive(skip)]
        label: Option<ResolvedName>,
        value: Box<TypedExpr>,
    },

    // Variables
    Let(#[drive(skip)] ResolvedName, Option<Box<TypedExpr>>),
    Assignment(Box<TypedExpr>, Box<TypedExpr>),
    Variable(#[drive(skip)] ResolvedName),

    If(Box<TypedExpr>, Box<TypedExpr>, Option<Box<TypedExpr>>),

    Loop(Option<Box<TypedExpr>>, Box<TypedExpr> /* body */),

    // Enum declaration
    EnumDecl {
        #[drive(skip)]
        name: ResolvedName,
        conformances: Vec<TypedExpr>,
        generics: Vec<TypedExpr>,
        body: Box<TypedExpr>,
    },

    // Individual enum variant in declaration
    EnumVariant(#[drive(skip)] ResolvedName, Vec<TypedExpr>),

    // Match expression
    Match(Box<TypedExpr>, Vec<TypedExpr>),

    // Individual match arm
    MatchArm(Box<TypedExpr>, Box<TypedExpr>),

    // Patterns (for match arms)
    PatternVariant(
        #[drive(skip)] Option<ResolvedName>,
        #[drive(skip)] ResolvedName,
        Vec<TypedExpr>,
    ),

    ProtocolDecl {
        #[drive(skip)]
        name: ResolvedName,
        associated_types: Vec<TypedExpr>,
        body: Box<TypedExpr>,
        conformances: Vec<TypedExpr>,
    },

    FuncSignature {
        #[drive(skip)]
        name: ResolvedName,
        params: Vec<TypedExpr>,
        generics: Vec<TypedExpr>,
        ret: Box<TypedExpr>,
    },
}

#[derive(Debug, Clone, PartialEq, Eq, DriveMut)]
pub struct TypedExpr {
    #[drive(skip)]
    pub id: ExprID,
    pub expr: Expr,
    #[drive(skip)]
    pub ty: Ty,
}

impl TypedExpr {
    pub fn new(id: ExprID, expr: Expr, ty: Ty) -> Self {
        Self { id, expr, ty }
    }

    pub fn apply(&mut self, substitutions: &mut Substitutions, env: &mut Environment) {
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
            Expr::ParsedPattern(_pattern) => (),
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
                if let Some(t) = type_repr.as_mut() {
                    t.apply(substitutions, env)
                }
                if let Some(t) = default_value.as_mut() {
                    t.apply(substitutions, env)
                }
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
                if let Some(t) = typed_expr.as_mut() {
                    t.apply(substitutions, env)
                }
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
                if let Some(t) = ret.as_mut() {
                    t.apply(substitutions, env)
                }
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

    pub fn find(&self, id: ExprID) -> Result<(), &TypedExpr> {
        let _s = trace_span!("finding", id = id.0).entered();

        if id == self.id {
            tracing::trace!("found: {self:?}");
            return Err(self);
        }

        match &self.expr {
            Expr::LiteralArray(items) => Self::find_in_err_res(items, id),
            Expr::LiteralInt(_) => Ok(()),
            Expr::LiteralFloat(_) => Ok(()),
            Expr::LiteralTrue => Ok(()),
            Expr::LiteralFalse => Ok(()),
            Expr::LiteralString(_) => Ok(()),
            Expr::Unary(_, rhs) => rhs.find(id),
            Expr::Binary(lhs, _, rhs) => {
                lhs.find(id)?;
                rhs.find(id)
            }
            Expr::Tuple(items) => Self::find_in_err_res(items, id),
            Expr::Block(items) => Self::find_in_err_res(items, id),
            Expr::Call {
                callee,
                type_args,
                args,
            } => {
                callee.find(id)?;
                Self::find_in_err_res(type_args, id)?;
                Self::find_in_err_res(args, id)
            }
            Expr::ParsedPattern(_pattern) => Ok(()),
            Expr::Return(ret) => {
                if let Some(ret) = &ret {
                    ret.find(id)?
                }

                Ok(())
            }
            Expr::Break => Ok(()),
            Expr::Extend {
                generics,
                conformances,
                body,
                ..
            } => {
                Self::find_in_err_res(conformances, id)?;
                Self::find_in_err_res(generics, id)?;
                body.find(id)
            }
            Expr::Struct {
                generics,
                conformances,
                body,
                ..
            } => {
                Self::find_in_err_res(conformances, id)?;
                Self::find_in_err_res(generics, id)?;
                body.find(id)
            }
            Expr::Property {
                type_repr,
                default_value,
                ..
            } => {
                if let Some(type_repr) = &type_repr {
                    type_repr.find(id)?;
                }

                if let Some(default_value) = &default_value {
                    default_value.find(id)?;
                }

                Ok(())
            }
            Expr::TypeRepr {
                generics,
                conformances,
                ..
            } => {
                Self::find_in_err_res(conformances, id)?;
                Self::find_in_err_res(generics, id)
            }
            Expr::FuncTypeRepr(params, ret, _) => {
                Self::find_in_err_res(params, id)?;
                ret.find(id)
            }
            Expr::TupleTypeRepr(typed_exprs, _) => Self::find_in_err_res(typed_exprs, id),
            Expr::Member(receiver, _) => {
                if let Some(receiver) = &receiver {
                    receiver.find(id)?;
                }

                Ok(())
            }
            Expr::Init(_, typed_expr) => typed_expr.find(id),
            Expr::Func {
                generics,
                params,
                body,
                ret,
                ..
            } => {
                body.find(id)?;
                Self::find_in_err_res(generics, id)?;
                Self::find_in_err_res(params, id)?;

                if let Some(ret) = &ret {
                    ret.find(id)?;
                }

                Ok(())
            }
            Expr::Parameter(_, typed_expr) => {
                if let Some(t) = &typed_expr {
                    t.find(id)?;
                }

                Ok(())
            }
            Expr::CallArg { value, .. } => value.find(id),
            Expr::Let(_, typed_expr) => {
                if let Some(t) = &typed_expr {
                    t.find(id)?;
                }

                Ok(())
            }
            Expr::Assignment(lhs, rhs) => {
                lhs.find(id)?;
                rhs.find(id)
            }
            Expr::Variable(_) => Ok(()),
            Expr::If(cond, conseq, alt) => {
                cond.find(id)?;
                conseq.find(id)?;
                if let Some(t) = &alt {
                    t.find(id)?;
                }

                Ok(())
            }
            Expr::Loop(cond, body) => {
                body.find(id)?;
                if let Some(t) = &cond {
                    t.find(id)?;
                }

                Ok(())
            }
            Expr::EnumDecl {
                conformances,
                generics,
                body,
                ..
            } => {
                Self::find_in_err_res(conformances, id)?;
                Self::find_in_err_res(generics, id)?;
                body.find(id)
            }
            Expr::EnumVariant(_, typed_exprs) => Self::find_in_err_res(typed_exprs, id),
            Expr::Match(pattern, arms) => {
                pattern.find(id)?;
                Self::find_in_err_res(arms, id)
            }
            Expr::MatchArm(pattern, body) => {
                pattern.find(id)?;
                body.find(id)
            }
            Expr::PatternVariant(_, _, values) => Self::find_in_err_res(values, id),
            Expr::ProtocolDecl {
                associated_types,
                body,
                conformances,
                ..
            } => {
                Self::find_in_err_res(associated_types, id)?;
                Self::find_in_err_res(conformances, id)?;
                body.find(id)
            }
            Expr::FuncSignature {
                params,
                generics,
                ret,
                ..
            } => {
                Self::find_in_err_res(params, id)?;
                Self::find_in_err_res(generics, id)?;
                ret.find(id)?;
                Ok(())
            }
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

    // Hijinks to get easier early returns
    pub fn find_in_err_res(exprs: &[TypedExpr], id: ExprID) -> Result<(), &TypedExpr> {
        for expr in exprs {
            expr.find(id)?;
        }

        Ok(())
    }

    pub fn find_in(exprs: &[TypedExpr], id: ExprID) -> Option<&TypedExpr> {
        for expr in exprs {
            if let Err(result) = expr.find(id) {
                return Some(result);
            }
        }

        None
    }

    pub fn span(&self, in_meta: &Rc<RefCell<ExprMetaStorage>>) -> (usize, usize) {
        if let Some(meta) = in_meta.borrow().get(&self.id) {
            meta.span()
        } else {
            Default::default()
        }
    }

    pub fn optional(&self) -> TypedExpr {
        TypedExpr {
            id: self.id,
            expr: self.expr.clone(),
            ty: self.ty.optional(),
        }
    }
}
