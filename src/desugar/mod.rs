//! The desugaring phase: syntactic transforms that lower surface sugar into a
//! smaller set of core constructs. Runs after parsing and before name
//! resolution, so name resolution and every later phase see the desugared
//! forms and never the surface sugar.
//!
//! Owning these here (rather than inside the name resolver) keeps each phase to
//! one job: the resolver binds names, it does not rewrite the tree.

pub mod lower_funcs_to_lets;
pub mod lower_if_to_match;
pub mod lower_operators;
pub mod lower_subscripts;
pub mod prepend_self_to_methods;
pub mod resolve_param_modes;

use crate::ast::{AST, Parsed};
use lower_funcs_to_lets::LowerFuncsToLets;
use lower_if_to_match::LowerIfToMatch;
use lower_operators::LowerOperators;
use lower_subscripts::LowerSubscripts;
use prepend_self_to_methods::PrependSelfToMethods;
use resolve_param_modes::ResolveParamModes;

/// Run every syntactic transform over each parsed file, in place.
pub fn desugar(asts: &mut [AST<Parsed>]) {
    for ast in asts.iter_mut() {
        // First, so user-written parameters get their default modes before
        // any pass synthesizes parameters of its own (synthesized params
        // keep `mode: None` = lowered as written).
        ResolveParamModes::run(ast);
        LowerFuncsToLets::run(ast);
        LowerSubscripts::run(ast);
        LowerOperators::run(ast);
        // After LowerOperators, which emits `if` expressions for `&&`/`||`.
        LowerIfToMatch::run(ast);
        PrependSelfToMethods::run(ast);
    }

    if std::env::var("SHOW_TRANSFORM").is_ok() {
        for ast in asts.iter() {
            println!("{:?}", ast.path);
            println!("{}", crate::formatter::format(ast, 80));
        }
    }
}
