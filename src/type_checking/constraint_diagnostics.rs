//! Diagnostic helpers for constraint solver error messages
//! 
//! This module provides utilities to generate better error messages for
//! constraint solving failures by tracking constraint origins and providing
//! context about why constraints failed to solve.

use std::collections::HashMap;

use crate::{
    constraint::Constraint,
    expr_id::ExprID,
    ty::Ty,
    type_var_id::TypeVarID,
};

/// Tracks the origin and context of constraints for better diagnostics
#[derive(Debug, Default)]
pub struct ConstraintDiagnostics {
    /// Maps type variables to their origin context
    type_var_origins: HashMap<TypeVarID, TypeVarOrigin>,
    /// Maps expression IDs to their context description
    expr_contexts: HashMap<ExprID, String>,
    /// Tracks constraint dependencies
    #[allow(dead_code)]
    constraint_deps: Vec<ConstraintDependency>,
}

#[derive(Debug, Clone)]
pub struct TypeVarOrigin {
    pub expr_id: ExprID,
    pub context: String,
    pub kind_description: String,
}

#[derive(Debug, Clone)]
pub struct ConstraintDependency {
    pub from: ExprID,
    pub to: ExprID,
    pub reason: String,
}

impl ConstraintDiagnostics {
    pub fn new() -> Self {
        Self::default()
    }

    /// Record the origin of a type variable
    pub fn record_type_var(&mut self, var: &TypeVarID, context: String, kind_desc: String) {
        self.type_var_origins.insert(
            var.clone(),
            TypeVarOrigin {
                expr_id: var.expr_id,
                context,
                kind_description: kind_desc,
            },
        );
    }

    /// Record expression context
    pub fn record_expr_context(&mut self, expr_id: ExprID, context: String) {
        self.expr_contexts.insert(expr_id, context);
    }

    /// Get origin information for a type variable
    pub fn get_type_var_origin(&self, var: &TypeVarID) -> Option<&TypeVarOrigin> {
        self.type_var_origins.get(var)
    }

    /// Get context for an expression
    pub fn get_expr_context(&self, expr_id: &ExprID) -> Option<&String> {
        self.expr_contexts.get(expr_id)
    }

    /// Generate a diagnostic message for an unsolved constraint
    pub fn diagnose_constraint(&self, constraint: &Constraint) -> String {
        match constraint {
            Constraint::MemberAccess(expr_id, receiver_ty, member_name, _) => {
                let context = self
                    .get_expr_context(expr_id)
                    .map(|s| format!(" in {}", s))
                    .unwrap_or_default();
                
                match receiver_ty {
                    Ty::TypeVar(var) => {
                        if let Some(origin) = self.get_type_var_origin(var) {
                            format!(
                                "Cannot access member '{}' on unresolved type variable{} ({})",
                                member_name, context, origin.context
                            )
                        } else {
                            format!(
                                "Cannot access member '{}' on unresolved type variable{}",
                                member_name, context
                            )
                        }
                    }
                    _ => format!(
                        "Member '{}' not found on type '{}'{}",
                        member_name,
                        receiver_ty,
                        context
                    ),
                }
            }
            Constraint::Row { constraint: row_constraint, expr_id } => {
                let context = self
                    .get_expr_context(expr_id)
                    .map(|s| format!(" in {}", s))
                    .unwrap_or_default();
                
                format!("Row constraint failed{}: {:?}", context, row_constraint)
            }
            Constraint::Equality(expr_id, lhs, rhs) => {
                let context = self
                    .get_expr_context(expr_id)
                    .map(|s| format!(" in {}", s))
                    .unwrap_or_default();
                
                format!(
                    "Type mismatch{}: expected '{}', found '{}'",
                    context, lhs, rhs
                )
            }
            _ => format!("Constraint could not be solved: {:?}", constraint),
        }
    }

    /// Generate a chain of related errors for better context
    pub fn generate_error_chain(&self, constraint: &Constraint) -> Vec<String> {
        let mut chain = vec![self.diagnose_constraint(constraint)];
        
        // Add related type variable origins if applicable
        if let Some(vars) = extract_type_vars(constraint) {
            for var in vars {
                if let Some(origin) = self.get_type_var_origin(&var) {
                    chain.push(format!(
                        "  Note: Type variable originates from {} ({})",
                        origin.context, origin.kind_description
                    ));
                }
            }
        }
        
        chain
    }
}

/// Extract type variables from a constraint for diagnostic purposes
fn extract_type_vars(constraint: &Constraint) -> Option<Vec<TypeVarID>> {
    let mut vars = Vec::new();
    
    match constraint {
        Constraint::MemberAccess(_, receiver_ty, _, result_ty) => {
            if let Ty::TypeVar(var) = receiver_ty {
                vars.push(var.clone());
            }
            if let Ty::TypeVar(var) = result_ty {
                vars.push(var.clone());
            }
        }
        Constraint::Equality(_, lhs, rhs) => {
            if let Ty::TypeVar(var) = lhs {
                vars.push(var.clone());
            }
            if let Ty::TypeVar(var) = rhs {
                vars.push(var.clone());
            }
        }
        _ => {}
    }
    
    if vars.is_empty() {
        None
    } else {
        Some(vars)
    }
}