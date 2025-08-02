use std::collections::BTreeMap;

use crate::{
    ExprMetaStorage,
    diagnostic::Diagnostic,
    expr_id::ExprID,
    parsed_expr::ParsedExpr,
    type_checker::TypeError,
    types::{
        constraint::Constraint,
        ty::Ty,
        typed_expr::{TypedExpr, TypedExprResult},
    },
};

pub struct TypeCheckingResult {
    pub typed_roots: Vec<TypedExpr>,
    pub diagnostics: Vec<Diagnostic>,
}

#[derive(Debug)]
pub struct TypeCheckingSession<'a> {
    pub typed_expr_ids: BTreeMap<ExprID, Ty>,
    pub constraints: Vec<Constraint>,
    pub meta: &'a ExprMetaStorage,
    pub parsed_roots: &'a [ParsedExpr],
    pub diagnostics: Vec<Diagnostic>,
}

impl<'a> TypeCheckingSession<'a> {
    pub fn new(parsed_roots: &'a [ParsedExpr], meta: &'a ExprMetaStorage) -> Self {
        Self {
            parsed_roots,
            meta,
            typed_expr_ids: Default::default(),
            constraints: Default::default(),
            diagnostics: Default::default(),
        }
    }

    pub fn solve(self) -> Result<TypeCheckingResult, TypeError> {
        let mut typed_roots = vec![];
        for root in self.parsed_roots {
            match root.to_typed(&self.typed_expr_ids) {
                TypedExprResult::Ok(typed) => {
                    typed_roots.push(typed);
                }
                TypedExprResult::Err(err) => return Err(err),
                TypedExprResult::None => (),
            }
        }

        Ok(TypeCheckingResult {
            typed_roots,
            diagnostics: self.diagnostics,
        })
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        parser::parse,
        types::{
            checker::{TypeCheckingResult, TypeCheckingSession},
            ty::{Primitive, Ty},
        },
    };

    fn check(code: &'static str) -> TypeCheckingResult {
        let parsed = parse(code, "-");
        let meta = parsed.meta.borrow();
        let session = TypeCheckingSession::new(parsed.roots(), &meta);

        session.solve().unwrap()
    }

    #[test]
    fn checks_int() {
        let checked = check("123");
        assert_eq!(Ty::Primitive(Primitive::Int), checked.typed_roots[0].ty)
    }

    #[test]
    fn test_identity() {}
}
