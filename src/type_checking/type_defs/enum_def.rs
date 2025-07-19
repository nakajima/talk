use crate::{parsed_expr::ParsedExpr, ty::Ty};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RawEnumVariant<'a> {
    pub tag: usize,
    pub name: String,
    pub expr: &'a ParsedExpr,
    pub values: &'a [ParsedExpr],
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EnumVariant {
    pub tag: usize,
    pub name: String,
    pub ty: Ty,
}
