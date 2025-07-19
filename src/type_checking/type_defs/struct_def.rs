use crate::{parsed_expr::ParsedExpr, parsing::expr_id::ExprID, ty::Ty, type_var_id::TypeVarID};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Property {
    pub index: usize,
    pub name: String,
    pub expr_id: ExprID,
    pub ty: Ty,
    pub has_default: bool,
}

impl Property {
    pub fn new(index: usize, name: String, expr_id: ExprID, ty: Ty, has_default: bool) -> Self {
        Self {
            index,
            name,
            expr_id,
            ty,
            has_default,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RawProperty<'a> {
    pub index: usize,
    pub name: String,
    pub expr: &'a ParsedExpr,
    pub placeholder: TypeVarID,
    pub default_value: &'a Option<Box<ParsedExpr>>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RawInitializer<'a> {
    pub name: String,
    pub expr: &'a ParsedExpr,
    pub func_id: ExprID,
    pub params: &'a [ParsedExpr],
    pub placeholder: TypeVarID,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Initializer {
    pub name: String,
    pub expr_id: ExprID,
    pub ty: Ty,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Method {
    pub name: String,
    pub expr_id: ExprID,
    pub ty: Ty,
}

impl Method {
    pub fn new(name: String, expr_id: ExprID, ty: Ty) -> Self {
        Self { name, expr_id, ty }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RawMethod<'a> {
    pub name: String,
    pub expr: &'a ParsedExpr,
    pub placeholder: TypeVarID,
}

impl<'a> RawMethod<'a> {
    pub fn new(name: String, expr: &'a ParsedExpr, placeholder: TypeVarID) -> Self {
        Self {
            name,
            expr,
            placeholder,
        }
    }
}
