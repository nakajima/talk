use crate::{
    environment::Environment, expr::Expr, token_kind::TokenKind, ty::Ty, type_checker::TypeError,
};

pub struct OperatorSolver<'a> {
    lhs: &'a Option<Ty>,
    rhs: &'a Ty,
    op: &'a TokenKind,
    env: &'a mut Environment,
}

impl<'a> OperatorSolver<'a> {
    pub fn new(
        lhs: &'a Option<Ty>,
        rhs: &'a Ty,
        op: &'a TokenKind,
        env: &'a mut Environment,
    ) -> Self {
        Self { lhs, rhs, op, env }
    }

    pub fn solve_binary(&self) -> Result<Ty, TypeError> {
        #[allow(clippy::unwrap_used)]
        let lhs = self.lhs.as_ref().unwrap(); // we'll only call this from infer_binary

        Err(TypeError::Handled)
    }

    pub fn solve_unary(&self) -> Result<Ty, TypeError> {
        Err(TypeError::Handled)
    }
}
