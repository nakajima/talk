use std::collections::BTreeMap;

use crate::{
    expr_id::ExprID,
    parsed_expr::{Expr, ParsedExpr},
    type_checker::TypeError,
    types::{
        ty::Ty,
        typed_expr::{TypedExpr, TypedExprResult},
    },
};

impl std::ops::FromResidual<Result<Option<TypedExpr>, TypeError>> for TypedExprResult {
    fn from_residual(residual: Result<Option<TypedExpr>, TypeError>) -> Self {
        match residual {
            Ok(maybe) => match maybe {
                Some(expr) => Self::Ok(Box::new(expr)),
                None => Self::None,
            },
            Err(err) => Self::Err(err),
        }
    }
}

impl std::ops::Try for TypedExprResult {
    type Output = TypedExpr;
    type Residual = Result<Option<TypedExpr>, TypeError>;

    fn from_output(output: Self::Output) -> Self {
        Self::Ok(Box::new(output))
    }

    fn branch(self) -> std::ops::ControlFlow<Self::Residual, Self::Output> {
        match self {
            Self::Ok(expr) => std::ops::ControlFlow::Continue(*expr),
            Self::Err(err) => std::ops::ControlFlow::Break(Err(err)),
            Self::None => std::ops::ControlFlow::Break(Ok(None)),
        }
    }
}

macro_rules! lookup {
    ($id: expr, $ids: expr) => {{
        if let Some(ty) = $ids.get(&$id).cloned() {
            ty
        } else {
            return TypedExprResult::Err(TypeError::Unknown(format!(
                "Type not found in ids: {:?}, {:?}",
                $id, $ids
            )));
        }
    }};
}

macro_rules! resolve {
    ($name: expr) => {{
        match $name.resolved() {
            Ok(name) => name,
            Err(err) => return TypedExprResult::Err(err),
        }
    }};
}

macro_rules! maybe_resolve {
    ($name: expr) => {{
        if let Some(expr) = $name {
            match expr.resolved() {
                Ok(name) => Some(name),
                Err(err) => return TypedExprResult::Err(err),
            };
        }

        None
    }};
}

macro_rules! map {
    ($exprs: expr, $ids: expr) => {{
        let mut result = vec![];
        for expr in $exprs {
            result.push(expr.to_typed($ids)?)
        }
        result
    }};
}

macro_rules! map_fields {
    ($exprs: expr, $ids: expr) => {{
        let mut result = vec![];
        for expr in $exprs {
            match expr.to_typed($ids) {
                TypedExprResult::Ok(expr) => result.push(*expr),
                TypedExprResult::Err(err) => return Err(err),
                TypedExprResult::None => {
                    return Err(TypeError::Unknown("Could not figure out type".to_string()));
                }
            }
        }

        Ok(result)
    }};
}

macro_rules! maybe {
    ($expr: expr, $ids: expr) => {{
        if let Some(expr) = $expr {
            expr.to_typed($ids);
        }

        None
    }};
}

impl crate::parsing::parsed_expr::Pattern {
    pub fn to_typed(
        &self,
        typed_ids: &BTreeMap<ExprID, Ty>,
    ) -> Result<super::typed_expr::Pattern, TypeError> {
        match self {
            crate::parsed_expr::Pattern::LiteralInt(val) => {
                Ok(super::typed_expr::Pattern::LiteralInt(val.to_string()))
            }
            crate::parsed_expr::Pattern::LiteralFloat(val) => {
                Ok(super::typed_expr::Pattern::LiteralInt(val.to_string()))
            }
            crate::parsed_expr::Pattern::LiteralTrue => Ok(super::typed_expr::Pattern::LiteralTrue),
            crate::parsed_expr::Pattern::LiteralFalse => {
                Ok(super::typed_expr::Pattern::LiteralFalse)
            }
            crate::parsed_expr::Pattern::Bind(name) => {
                Ok(super::typed_expr::Pattern::Bind(name.resolved()?))
            }
            crate::parsed_expr::Pattern::Wildcard => Ok(super::typed_expr::Pattern::Wildcard),
            crate::parsed_expr::Pattern::Variant {
                enum_name,
                variant_name,
                fields,
            } => {
                let enum_name = if let Some(enum_name) = enum_name {
                    Some(enum_name.resolved()?)
                } else {
                    None
                };

                Ok(super::typed_expr::Pattern::Variant {
                    enum_name,
                    variant_name: variant_name.to_string(),
                    fields: map_fields!(fields, typed_ids)?,
                })
            }
            crate::parsed_expr::Pattern::Struct {
                struct_name,
                fields,
                field_names,
                rest,
            } => {
                let mut resolved_field_names = vec![];
                for field_name in field_names {
                    match field_name.resolved() {
                        Ok(name) => resolved_field_names.push(name),
                        Err(err) => return Err(err),
                    }
                }

                let struct_name = if let Some(struct_name) = struct_name {
                    Some(struct_name.resolved()?)
                } else {
                    None
                };

                Ok(super::typed_expr::Pattern::Struct {
                    struct_name,
                    fields: map_fields!(fields, typed_ids)?,
                    field_names: resolved_field_names,
                    rest: *rest,
                })
            }
        }
    }
}

impl ParsedExpr {
    pub fn to_typed(&self, typed_ids: &BTreeMap<ExprID, Ty>) -> TypedExprResult {
        match &self.expr {
            Expr::Incomplete(..) => TypedExprResult::None,
            Expr::Attribute(..) => TypedExprResult::None,
            Expr::LiteralArray(parsed_exprs) => {
                let expr =
                    crate::types::typed_expr::Expr::LiteralArray(map!(parsed_exprs, typed_ids));

                TypedExprResult::Ok(
                    crate::types::typed_expr::TypedExpr {
                        id: self.id,
                        expr,
                        ty: lookup!(self.id, typed_ids),
                    }
                    .into(),
                )
            }
            Expr::LiteralInt(val) => TypedExprResult::Ok(
                TypedExpr {
                    id: self.id,
                    expr: crate::types::typed_expr::Expr::LiteralInt(val.to_string()),
                    ty: lookup!(self.id, typed_ids),
                }
                .into(),
            ),
            Expr::LiteralFloat(val) => TypedExprResult::Ok(
                TypedExpr {
                    id: self.id,
                    expr: crate::types::typed_expr::Expr::LiteralFloat(val.to_string()),
                    ty: lookup!(self.id, typed_ids),
                }
                .into(),
            ),
            Expr::LiteralTrue => TypedExprResult::Ok(
                TypedExpr {
                    id: self.id,
                    expr: crate::types::typed_expr::Expr::LiteralTrue,
                    ty: lookup!(self.id, typed_ids),
                }
                .into(),
            ),
            Expr::LiteralFalse => TypedExprResult::Ok(
                TypedExpr {
                    id: self.id,
                    expr: crate::types::typed_expr::Expr::LiteralFalse,
                    ty: lookup!(self.id, typed_ids),
                }
                .into(),
            ),
            Expr::LiteralString(val) => TypedExprResult::Ok(
                TypedExpr {
                    id: self.id,
                    expr: crate::types::typed_expr::Expr::LiteralString(val.to_string()),
                    ty: lookup!(self.id, typed_ids),
                }
                .into(),
            ),
            Expr::Unary(token_kind, parsed_expr) => TypedExprResult::Ok(
                TypedExpr {
                    id: self.id,
                    expr: crate::types::typed_expr::Expr::Unary(
                        token_kind.clone(),
                        Box::new(parsed_expr.to_typed(typed_ids)?),
                    ),
                    ty: lookup!(self.id, typed_ids),
                }
                .into(),
            ),
            Expr::Binary(lhs, token_kind, rhs) => TypedExprResult::Ok(
                TypedExpr {
                    id: self.id,
                    expr: crate::types::typed_expr::Expr::Binary(
                        Box::new(lhs.to_typed(typed_ids)?),
                        token_kind.clone(),
                        Box::new(rhs.to_typed(typed_ids)?),
                    ),
                    ty: lookup!(self.id, typed_ids),
                }
                .into(),
            ),
            Expr::Tuple(parsed_exprs) => TypedExprResult::Ok(
                TypedExpr {
                    id: self.id,
                    expr: crate::types::typed_expr::Expr::Tuple(map!(parsed_exprs, typed_ids)),
                    ty: lookup!(self.id, typed_ids),
                }
                .into(),
            ),
            Expr::Block(parsed_exprs) => TypedExprResult::Ok(
                TypedExpr {
                    id: self.id,
                    expr: crate::types::typed_expr::Expr::Block(map!(parsed_exprs, typed_ids)),
                    ty: lookup!(self.id, typed_ids),
                }
                .into(),
            ),
            Expr::Call {
                callee,
                type_args,
                args,
            } => TypedExprResult::Ok(
                TypedExpr {
                    id: self.id,
                    expr: crate::types::typed_expr::Expr::Call {
                        callee: Box::new(callee.to_typed(typed_ids)?),
                        type_args: map!(type_args, typed_ids),
                        args: map!(args, typed_ids),
                    },
                    ty: lookup!(self.id, typed_ids),
                }
                .into(),
            ),
            Expr::ParsedPattern(pattern) => {
                let pattern = match pattern.to_typed(typed_ids) {
                    Ok(pattern) => pattern,
                    Err(e) => return TypedExprResult::Err(e),
                };
                TypedExprResult::Ok(
                    TypedExpr {
                        id: self.id,
                        expr: crate::types::typed_expr::Expr::ParsedPattern(pattern),
                        ty: lookup!(self.id, typed_ids),
                    }
                    .into(),
                )
            }
            Expr::Return(parsed_expr) => TypedExprResult::Ok(
                TypedExpr {
                    id: self.id,
                    expr: crate::types::typed_expr::Expr::Return(if let Some(expr) = parsed_expr {
                        Some(Box::new(expr.to_typed(typed_ids)?))
                    } else {
                        None
                    }),
                    ty: lookup!(self.id, typed_ids),
                }
                .into(),
            ),
            Expr::Break => TypedExprResult::Ok(
                TypedExpr {
                    id: self.id,
                    expr: crate::types::typed_expr::Expr::Break,
                    ty: lookup!(self.id, typed_ids),
                }
                .into(),
            ),
            Expr::Extend {
                name,
                generics,
                conformances,
                body,
            } => TypedExprResult::Ok(
                TypedExpr {
                    id: self.id,
                    expr: crate::types::typed_expr::Expr::Extend {
                        name: resolve!(name),
                        generics: map!(generics, typed_ids),
                        conformances: map!(conformances, typed_ids),
                        body: Box::new(body.to_typed(typed_ids)?),
                    },
                    ty: lookup!(self.id, typed_ids),
                }
                .into(),
            ),
            Expr::Struct {
                name,
                generics,
                conformances,
                body,
            } => TypedExprResult::Ok(
                TypedExpr {
                    id: self.id,
                    expr: crate::types::typed_expr::Expr::Struct {
                        name: resolve!(name),
                        generics: map!(generics, typed_ids),
                        conformances: map!(conformances, typed_ids),
                        body: Box::new(body.to_typed(typed_ids)?),
                    },
                    ty: lookup!(self.id, typed_ids),
                }
                .into(),
            ),
            Expr::Property {
                name,
                type_repr,
                default_value,
            } => TypedExprResult::Ok(
                TypedExpr {
                    id: self.id,
                    expr: crate::types::typed_expr::Expr::Property {
                        name: resolve!(name),
                        type_repr: maybe!(type_repr, typed_ids),
                        default_value: maybe!(default_value, typed_ids),
                    },
                    ty: lookup!(self.id, typed_ids),
                }
                .into(),
            ),
            Expr::TypeRepr {
                name,
                generics,
                conformances,
                introduces_type,
            } => TypedExprResult::Ok(
                TypedExpr {
                    id: self.id,
                    expr: crate::types::typed_expr::Expr::TypeRepr {
                        name: resolve!(name),
                        generics: map!(generics, typed_ids),
                        conformances: map!(conformances, typed_ids),
                        introduces_type: *introduces_type,
                    },
                    ty: lookup!(self.id, typed_ids),
                }
                .into(),
            ),
            Expr::FuncTypeRepr(parsed_exprs, parsed_expr, introduces_type) => TypedExprResult::Ok(
                TypedExpr {
                    id: self.id,
                    expr: crate::types::typed_expr::Expr::FuncTypeRepr(
                        map!(parsed_exprs, typed_ids),
                        Box::new(parsed_expr.to_typed(typed_ids)?),
                        *introduces_type,
                    ),
                    ty: lookup!(self.id, typed_ids),
                }
                .into(),
            ),
            Expr::TupleTypeRepr(parsed_exprs, introduces_type) => TypedExprResult::Ok(
                TypedExpr {
                    id: self.id,
                    expr: crate::types::typed_expr::Expr::TupleTypeRepr(
                        map!(parsed_exprs, typed_ids),
                        *introduces_type,
                    ),
                    ty: lookup!(self.id, typed_ids),
                }
                .into(),
            ),
            Expr::Member(parsed_expr, name) => TypedExprResult::Ok(
                TypedExpr {
                    id: self.id,
                    expr: crate::types::typed_expr::Expr::Member(
                        maybe!(parsed_expr, typed_ids),
                        name.to_string(),
                    ),
                    ty: lookup!(self.id, typed_ids),
                }
                .into(),
            ),
            Expr::Init(symbol_id, parsed_expr) => {
                let Some(symbol_id) = symbol_id else {
                    return TypedExprResult::Err(TypeError::Unresolved(
                        "Init not resolved".to_string(),
                    ));
                };
                TypedExprResult::Ok(
                    TypedExpr {
                        id: self.id,
                        expr: crate::types::typed_expr::Expr::Init(
                            *symbol_id,
                            Box::new(parsed_expr.to_typed(typed_ids)?),
                        ),
                        ty: lookup!(self.id, typed_ids),
                    }
                    .into(),
                )
            }
            Expr::Func {
                name,
                generics,
                params,
                body,
                ret,
                captures,
                attributes: _,
            } => TypedExprResult::Ok(
                TypedExpr {
                    id: self.id,
                    expr: crate::types::typed_expr::Expr::Func {
                        name: maybe_resolve!(name),
                        generics: map!(generics, typed_ids),
                        params: map!(params, typed_ids),
                        body: Box::new(body.to_typed(typed_ids)?),
                        ret: maybe!(ret, typed_ids),
                        captures: captures.clone(),
                    },
                    ty: lookup!(self.id, typed_ids),
                }
                .into(),
            ),
            Expr::Parameter(name, parsed_expr) => TypedExprResult::Ok(
                TypedExpr {
                    id: self.id,
                    expr: crate::types::typed_expr::Expr::Parameter(
                        resolve!(name),
                        maybe!(parsed_expr, typed_ids),
                    ),
                    ty: lookup!(self.id, typed_ids),
                }
                .into(),
            ),
            Expr::CallArg { value, .. } => TypedExprResult::Ok(
                TypedExpr {
                    id: self.id,
                    expr: crate::types::typed_expr::Expr::CallArg {
                        label: None, // TODO: actually resolve this
                        value: Box::new(value.to_typed(typed_ids)?),
                    },
                    ty: lookup!(self.id, typed_ids),
                }
                .into(),
            ),
            Expr::Let(name, parsed_expr) => TypedExprResult::Ok(
                TypedExpr {
                    id: self.id,
                    expr: crate::types::typed_expr::Expr::Let(
                        resolve!(name),
                        maybe!(parsed_expr, typed_ids),
                    ),
                    ty: lookup!(self.id, typed_ids),
                }
                .into(),
            ),
            Expr::Assignment(parsed_expr, parsed_expr1) => TypedExprResult::Ok(
                TypedExpr {
                    id: self.id,
                    expr: crate::types::typed_expr::Expr::Assignment(
                        Box::new(parsed_expr.to_typed(typed_ids)?),
                        Box::new(parsed_expr1.to_typed(typed_ids)?),
                    ),
                    ty: lookup!(self.id, typed_ids),
                }
                .into(),
            ),
            Expr::Variable(name) => TypedExprResult::Ok(
                TypedExpr {
                    id: self.id,
                    expr: crate::types::typed_expr::Expr::Variable(resolve!(name)),
                    ty: lookup!(self.id, typed_ids),
                }
                .into(),
            ),
            Expr::If(cond, conseq, alt) => TypedExprResult::Ok(
                TypedExpr {
                    id: self.id,
                    expr: crate::types::typed_expr::Expr::If(
                        Box::new(cond.to_typed(typed_ids)?),
                        Box::new(conseq.to_typed(typed_ids)?),
                        if let Some(alt) = alt {
                            Some(Box::new(alt.to_typed(typed_ids)?))
                        } else {
                            None
                        },
                    ),
                    ty: lookup!(self.id, typed_ids),
                }
                .into(),
            ),
            Expr::Loop(cond, body) => TypedExprResult::Ok(
                TypedExpr {
                    id: self.id,
                    expr: crate::types::typed_expr::Expr::Loop(
                        if let Some(cond) = cond {
                            Some(Box::new(cond.to_typed(typed_ids)?))
                        } else {
                            None
                        },
                        Box::new(body.to_typed(typed_ids)?),
                    ),
                    ty: lookup!(self.id, typed_ids),
                }
                .into(),
            ),
            Expr::EnumDecl {
                name,
                conformances,
                generics,
                body,
            } => TypedExprResult::Ok(
                TypedExpr {
                    id: self.id,
                    expr: crate::types::typed_expr::Expr::EnumDecl {
                        name: resolve!(name),
                        conformances: map!(conformances, typed_ids),
                        generics: map!(generics, typed_ids),
                        body: Box::new(body.to_typed(typed_ids)?),
                    },
                    ty: lookup!(self.id, typed_ids),
                }
                .into(),
            ),
            Expr::EnumVariant(name, fields) => TypedExprResult::Ok(
                TypedExpr {
                    id: self.id,
                    expr: crate::types::typed_expr::Expr::EnumVariant(
                        resolve!(name),
                        map!(fields, typed_ids),
                    ),
                    ty: lookup!(self.id, typed_ids),
                }
                .into(),
            ),
            Expr::Match(expr, arms) => TypedExprResult::Ok(
                TypedExpr {
                    id: self.id,
                    expr: crate::types::typed_expr::Expr::Match(
                        Box::new(expr.to_typed(typed_ids)?),
                        map!(arms, typed_ids),
                    ),
                    ty: lookup!(self.id, typed_ids),
                }
                .into(),
            ),
            Expr::MatchArm(pattern, body) => TypedExprResult::Ok(
                TypedExpr {
                    id: self.id,
                    expr: crate::types::typed_expr::Expr::MatchArm(
                        Box::new(pattern.to_typed(typed_ids)?),
                        Box::new(body.to_typed(typed_ids)?),
                    ),
                    ty: lookup!(self.id, typed_ids),
                }
                .into(),
            ),
            Expr::PatternVariant(enum_name, variant_name, values) => TypedExprResult::Ok(
                TypedExpr {
                    id: self.id,
                    expr: crate::types::typed_expr::Expr::PatternVariant(
                        maybe_resolve!(enum_name),
                        resolve!(variant_name),
                        map!(values, typed_ids),
                    ),
                    ty: lookup!(self.id, typed_ids),
                }
                .into(),
            ),
            Expr::RecordLiteral(fields) => TypedExprResult::Ok(
                TypedExpr {
                    id: self.id,
                    expr: crate::types::typed_expr::Expr::RecordLiteral(map!(fields, typed_ids)),
                    ty: lookup!(self.id, typed_ids),
                }
                .into(),
            ),
            Expr::RecordField { label, value } => TypedExprResult::Ok(
                TypedExpr {
                    id: self.id,
                    expr: crate::types::typed_expr::Expr::RecordField {
                        label: label.name_str().to_string(),
                        value: Box::new(value.to_typed(typed_ids)?),
                    },
                    ty: lookup!(self.id, typed_ids),
                }
                .into(),
            ),
            Expr::RecordTypeRepr {
                fields,
                row_var,
                introduces_type,
            } => TypedExprResult::Ok(
                TypedExpr {
                    id: self.id,
                    expr: crate::types::typed_expr::Expr::RecordTypeRepr {
                        fields: map!(fields, typed_ids),
                        row_var: if let Some(row) = row_var {
                            Some(Box::new(row.to_typed(typed_ids)?))
                        } else {
                            None
                        },
                        introduces_type: *introduces_type,
                    },
                    ty: lookup!(self.id, typed_ids),
                }
                .into(),
            ),
            Expr::RecordTypeField { label, ty } => TypedExprResult::Ok(
                TypedExpr {
                    id: self.id,
                    expr: crate::types::typed_expr::Expr::RecordTypeField {
                        label: label.name_str().to_string(),
                        ty: Box::new(ty.to_typed(typed_ids)?),
                    },
                    ty: lookup!(self.id, typed_ids),
                }
                .into(),
            ),
            Expr::RowVariable(name) => TypedExprResult::Ok(
                TypedExpr {
                    id: self.id,
                    expr: crate::types::typed_expr::Expr::RowVariable(name.name_str().to_string()),
                    ty: lookup!(self.id, typed_ids),
                }
                .into(),
            ),
            Expr::Spread(expr) => TypedExprResult::Ok(
                TypedExpr {
                    id: self.id,
                    expr: crate::types::typed_expr::Expr::Spread(Box::new(
                        expr.to_typed(typed_ids)?,
                    )),
                    ty: lookup!(self.id, typed_ids),
                }
                .into(),
            ),
            Expr::ProtocolDecl {
                name,
                associated_types,
                body,
                conformances,
            } => TypedExprResult::Ok(
                TypedExpr {
                    id: self.id,
                    expr: crate::types::typed_expr::Expr::ProtocolDecl {
                        name: resolve!(name),
                        associated_types: map!(associated_types, typed_ids),
                        body: Box::new(body.to_typed(typed_ids)?),
                        conformances: map!(conformances, typed_ids),
                    },
                    ty: lookup!(self.id, typed_ids),
                }
                .into(),
            ),
            Expr::FuncSignature {
                name,
                params,
                generics,
                ret,
            } => TypedExprResult::Ok(
                TypedExpr {
                    id: self.id,
                    expr: crate::types::typed_expr::Expr::FuncSignature {
                        name: resolve!(name),
                        params: map!(params, typed_ids),
                        generics: map!(generics, typed_ids),
                        ret: Box::new(ret.to_typed(typed_ids)?),
                    },
                    ty: lookup!(self.id, typed_ids),
                }
                .into(),
            ),
            Expr::Import(path) => TypedExprResult::Ok(
                TypedExpr {
                    id: self.id,
                    expr: crate::types::typed_expr::Expr::Import(path.clone()),
                    ty: lookup!(self.id, typed_ids),
                }
                .into(),
            ),
        }
    }
}
