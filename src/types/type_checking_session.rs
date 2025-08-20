use std::collections::BTreeMap;

use derive_visitor::Drive;
use tracing::trace_span;

use crate::{
    ExprMetaStorage, SymbolTable,
    diagnostic::Diagnostic,
    expr_id::ExprID,
    parsed_expr::ParsedExpr,
    types::{
        constraint::ConstraintState,
        constraint_set::ConstraintSet,
        constraint_solver::ConstraintSolver,
        hoister::Hoister,
        ty::Ty,
        type_var::{TypeVar, TypeVarKind},
        type_var_context::TypeVarContext,
        typed_expr::{TypedExpr, TypedExprResult},
        visitor::Visitor,
        visitors::{
            self, definition_visitor::DefinitionVisitor, inference_visitor::InferenceVisitor,
        },
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
    pub symbols: &'a SymbolTable,
}

impl<'a> TypeCheckingSession<'a> {
    pub fn new(
        parsed_roots: &'a [ParsedExpr],
        meta: &'a ExprMetaStorage,
        symbols: &'a SymbolTable,
    ) -> Self {
        Self {
            parsed_roots,
            meta,
            typed_expr_ids: Default::default(),
            constraints: Default::default(),
            diagnostics: Default::default(),
            type_var_context: TypeVarContext::default(),
            symbols,
        }
    }

    pub fn solve(&mut self) -> TypeCheckingResult {
        let _s = trace_span!("type checking").entered();

        let mut visitor = Visitor::new(
            &mut self.type_var_context,
            &mut self.constraints,
            &mut self.typed_expr_ids,
            self.meta,
            self.symbols,
        );

        if Hoister::hoist(&mut visitor, self.parsed_roots).is_err() {
            return TypeCheckingResult {
                typed_roots: vec![],
                diagnostics: self.diagnostics.clone(),
            };
        }

        for root in self.parsed_roots {
            match visitor.visit(root) {
                Ok(_) => (),
                Err(err) => {
                    self.diagnostics.push(Diagnostic::typing(
                        self.meta.path.clone(),
                        self.meta.span(&root.id).unwrap_or_default().into(),
                        err,
                    ));
                }
            }
        }

        let solver = ConstraintSolver::new(
            &mut self.type_var_context,
            &mut self.constraints,
            self.symbols,
        );
        let errored = solver.solve();

        for constraint in errored {
            let ConstraintState::Error(err) = constraint.state else {
                continue;
            };
            self.diagnostics.push(crate::diagnostic::Diagnostic::typing(
                self.meta.path.clone(),
                self.meta
                    .span(&constraint.expr_id)
                    .unwrap_or_default()
                    .into(),
                err,
            ));
        }

        // Apply the most recent substitutions to our types
        for ty in self.typed_expr_ids.values_mut() {
            *ty = self.type_var_context.resolve(ty);
        }

        let mut typed_roots = vec![];
        for root in self.parsed_roots {
            match root.to_typed(&self.typed_expr_ids) {
                TypedExprResult::Ok(typed) => {
                    typed_roots.push(*typed);
                }
                TypedExprResult::Err(err) => {
                    self.diagnostics.push(Diagnostic::typing(
                        self.meta.path.clone(),
                        self.meta.span(&root.id).unwrap_or_default().into(),
                        err,
                    ));
                }
                TypedExprResult::None => {}
            }
        }

        TypeCheckingResult {
            typed_roots,
            diagnostics: self.diagnostics.clone(),
        }
    }

    pub fn solve_multi(&mut self) -> TypeCheckingResult {
        let _s = trace_span!("type checking").entered();

        let mut definition_visitor = DefinitionVisitor::new();

        for root in self.parsed_roots {
            root.drive(&mut definition_visitor);
        }

        let mut inference_visitor = InferenceVisitor::new(
            &mut self.type_var_context,
            &mut self.typed_expr_ids,
            &definition_visitor.definitions,
        );

        visitors::inference_visitor_hoisting::Hoister::hoist(
            &mut inference_visitor,
            self.parsed_roots,
        )
        .unwrap();

        for root in self.parsed_roots {
            match inference_visitor.visit(root) {
                Ok(_) => (),
                Err(err) => {
                    self.diagnostics.push(Diagnostic::typing(
                        self.meta.path.clone(),
                        self.meta.span(&root.id).unwrap_or_default().into(),
                        err,
                    ));
                }
            }
        }

        self.constraints.extend(&inference_visitor.constraints);

        let solver = ConstraintSolver::new(
            &mut self.type_var_context,
            &mut self.constraints,
            self.symbols,
        );
        let errored = solver.solve();

        for constraint in errored {
            let ConstraintState::Error(err) = constraint.state else {
                continue;
            };
            self.diagnostics.push(crate::diagnostic::Diagnostic::typing(
                self.meta.path.clone(),
                self.meta
                    .span(&constraint.expr_id)
                    .unwrap_or_default()
                    .into(),
                err,
            ));
        }

        // Apply the most recent substitutions to our types
        for ty in self.typed_expr_ids.values_mut() {
            *ty = self.type_var_context.resolve(ty);
        }

        let mut typed_roots = vec![];
        for root in self.parsed_roots {
            match root.to_typed(&self.typed_expr_ids) {
                TypedExprResult::Ok(typed) => {
                    typed_roots.push(*typed);
                }
                TypedExprResult::Err(err) => {
                    self.diagnostics.push(Diagnostic::typing(
                        self.meta.path.clone(),
                        self.meta.span(&root.id).unwrap_or_default().into(),
                        err,
                    ));
                }
                TypedExprResult::None => {}
            }
        }

        TypeCheckingResult {
            typed_roots,
            diagnostics: self.diagnostics.clone(),
        }
    }

    pub fn new_type_var(&mut self, default: TypeVarKind) -> TypeVar {
        self.type_var_context.new_var(default)
    }
}
