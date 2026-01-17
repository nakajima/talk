pub mod builtins;
pub mod conformance;
pub mod constraint_solver;
pub mod constraints;
pub mod format;
pub mod infer_row;
pub mod infer_ty;
pub mod mappable;
pub mod matcher;
pub mod passes;
pub mod predicate;
pub mod row;
pub mod scheme;
pub mod solve_context;
pub mod term_environment;
pub mod ty;
pub mod type_catalog;
pub mod type_error;
pub mod type_operations;
pub mod type_session;
pub mod type_snapshot;
pub mod typed_ast;
#[allow(clippy::module_inception)]
pub mod types;
pub mod types_decorator;
pub mod variational;
pub mod vars;

#[cfg(test)]
pub mod effects_tests;
#[cfg(test)]
pub mod types_tests;
