use std::collections::BTreeMap;

use tracing::trace_span;

use crate::{
    ExprMetaStorage,
    diagnostic::Diagnostic,
    expr_id::ExprID,
    parsed_expr::ParsedExpr,
    type_checker::TypeError,
    types::{
        visitor::Visitor,
        constraint_set::ConstraintSet,
        constraint_solver::ConstraintSolver,
        ty::Ty,
        type_var::{TypeVar, TypeVarDefault},
        type_var_context::TypeVarContext,
        typed_expr::{TypedExpr, TypedExprResult},
    },
};

pub struct TypeCheckingResult {
    pub typed_roots: Vec<TypedExpr>,
    pub diagnostics: Vec<Diagnostic>,
}

pub type ExprIDTypeMap = BTreeMap<ExprID, Ty>;

#[derive(Debug)]
pub struct TypeCheckingSession<'a> {
    pub typed_expr_ids: ExprIDTypeMap,
    pub constraints: ConstraintSet,
    pub meta: &'a ExprMetaStorage,
    pub parsed_roots: &'a [ParsedExpr],
    pub diagnostics: Vec<Diagnostic>,
    pub type_var_context: TypeVarContext,
}

impl<'a> TypeCheckingSession<'a> {
    pub fn new(parsed_roots: &'a [ParsedExpr], meta: &'a ExprMetaStorage) -> Self {
        Self {
            parsed_roots,
            meta,
            typed_expr_ids: Default::default(),
            constraints: Default::default(),
            diagnostics: Default::default(),
            type_var_context: TypeVarContext::default(),
        }
    }

    pub fn solve(&mut self) -> Result<TypeCheckingResult, TypeError> {
        let _s = trace_span!("type checking").entered();

        let mut visitor = Visitor::new(
            &mut self.type_var_context,
            &mut self.constraints,
            &mut self.typed_expr_ids,
            self.meta,
        );

        for root in self.parsed_roots {
            visitor.visit(root)?;
        }

        let mut solver = ConstraintSolver::new(&mut self.type_var_context, &mut self.constraints);
        self.typed_expr_ids
            .extend(solver.solve()?);

        // Apply the most recent substitutions to our types
        for ty in self.typed_expr_ids.values_mut() {
            *ty = self.type_var_context.resolve(ty)
        }

        let mut typed_roots = vec![];
        for root in self.parsed_roots {
            match root.to_typed(&self.typed_expr_ids) {
                TypedExprResult::Ok(typed) => {
                    typed_roots.push(typed);
                }
                TypedExprResult::Err(err) => return Err(err),
                TypedExprResult::None => {}
            }
        }

        Ok(TypeCheckingResult {
            typed_roots,
            diagnostics: self.diagnostics.clone(),
        })
    }

    pub fn new_type_var(&mut self, default: TypeVarDefault) -> TypeVar {
        self.type_var_context.new_var(default)
    }
}
