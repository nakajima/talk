use std::path::PathBuf;

#[cfg(test)]
use crate::environment::Environment;
use crate::{SourceFile, SymbolTable, Typed, compiling::driver::Driver, type_checker::TypeError};

pub mod constraint_solver;
pub mod environment;
pub mod name_resolver;
pub mod scope_tree;
pub mod synthesis;
pub mod type_checker;
pub mod typed_expr;

#[cfg(test)]
struct CheckResult {
    pub source_file: SourceFile<Typed>,
    pub env: Environment,
}

#[cfg(test)]
pub fn check(input: &str) -> Result<CheckResult, TypeError> {
    let path = &PathBuf::from("./test.tlk");
    let mut driver = Driver::new(Default::default());
    driver.update_file(path, input.into());
    let typed_compilation_unit = driver.check().into_iter().next().unwrap().clone();
    let source_file = typed_compilation_unit.source_file(path).unwrap().clone();
    Ok(CheckResult {
        source_file,
        env: typed_compilation_unit.env,
    })
}

// pub fn check_with_symbols(input: &str) -> Result<(SourceFile<Typed>, SymbolTable), TypeError> {
//     use crate::{
//         constraint_solver::ConstraintSolver, environment::Environment, name_resolver::NameResolver,
//         parser::parse, prelude::compile_prelude, type_checker::TypeChecker,
//     };

//     let mut symbol_table = compile_prelude().symbols.clone();
//     let parsed = parse(input, "-".into());
//     let resolver = NameResolver::new(&mut symbol_table);
//     let resolved = resolver.resolve(parsed, &mut symbol_table);
//     let checker = TypeChecker;
//     let mut env = Environment::new();
//     let mut inferred = checker.infer(resolved, &mut symbol_table, &mut env);
//     let mut constraint_solver = ConstraintSolver::new(&mut inferred, &mut symbol_table);
//     constraint_solver.solve();
//     Ok((inferred, symbol_table.clone()))
// }
