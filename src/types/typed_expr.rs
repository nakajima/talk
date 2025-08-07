use std::{cell::RefCell, rc::Rc};

use derive_visitor::DriveMut;
use tracing::trace_span;

use crate::{
    ExprMetaStorage, SymbolID, name::ResolvedName, parsing::expr_id::ExprID, token_kind::TokenKind,
    type_checker::TypeError, types::ty::Ty,
};

pub enum TypedExprResult {
    Ok(Box<TypedExpr>),
    Err(TypeError),
    None,
}

#[derive(Clone, Debug, PartialEq, DriveMut)]
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

    Struct {
        #[drive(skip)]
        struct_name: Option<ResolvedName>,
        fields: Vec<TypedExpr>,
        #[drive(skip)]
        field_names: Vec<ResolvedName>,
        #[drive(skip)]
        rest: bool,
    },
}

#[derive(Debug, Clone, PartialEq, DriveMut)]
pub enum Expr {
    LiteralArray(Vec<TypedExpr>),
    LiteralInt(#[drive(skip)] String),
    LiteralFloat(#[drive(skip)] String),
    LiteralTrue,
    LiteralFalse,
    Import(#[drive(skip)] String),
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

    RecordLiteral(Vec<TypedExpr>), // List of RecordField expressions

    RecordField {
        #[drive(skip)]
        label: String,
        value: Box<TypedExpr>,
    },

    // These are for type representations, not runtime values
    RecordTypeRepr {
        fields: Vec<TypedExpr>,
        row_var: Option<Box<TypedExpr>>,
        #[drive(skip)]
        introduces_type: bool,
    },

    RecordTypeField {
        #[drive(skip)]
        label: String,
        ty: Box<TypedExpr>,
    },

    RowVariable(#[drive(skip)] String),

    Spread(Box<TypedExpr>),
}

#[derive(Debug, Clone, PartialEq, DriveMut)]
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

    pub fn find(&self, id: ExprID) -> Result<(), &TypedExpr> {
        let _s = trace_span!("finding", id = id.0).entered();

        if id == self.id {
            tracing::trace!("found: {self:?}");
            return Err(self);
        }

        match &self.expr {
            Expr::LiteralArray(items) => Self::find_in_err_res(items, id),
            Expr::LiteralInt(_) => Ok(()),
            Expr::Import(_) => Ok(()),
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
            Expr::RecordLiteral(fields) => Self::find_in_err_res(fields, id),
            Expr::RecordField { value, .. } => value.find(id),
            Expr::RecordTypeRepr {
                fields, row_var, ..
            } => {
                Self::find_in_err_res(fields, id)?;
                if let Some(row) = row_var {
                    row.find(id)?;
                }
                Ok(())
            }
            Expr::RecordTypeField { ty, .. } => ty.find(id),
            Expr::RowVariable(_) => Ok(()),
            Expr::Spread(expr) => expr.find(id),
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
