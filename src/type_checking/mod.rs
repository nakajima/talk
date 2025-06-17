use std::path::PathBuf;

use crate::{SourceFile, SymbolTable, Typed, compiling::driver::Driver, type_checker::TypeError};

pub mod constraint_solver;
pub mod environment;
pub mod name_resolver;
pub mod scope_tree;
pub mod synthesis;
pub mod type_checker;
pub mod typed_expr;

pub fn check(input: &str) -> Result<SourceFile<Typed>, TypeError> {
    let path = &PathBuf::from("./test.tlk");
    let mut driver = Driver::new();
    driver.update_file(path, input.into());
    let typed = driver.units[0]
        .parse()
        .resolved(&mut driver.symbol_table)
        .typed(&mut driver.symbol_table);

    Ok(typed.source_file(path).unwrap().clone())
}

pub fn check_with_symbols(input: &str) -> Result<(SourceFile<Typed>, SymbolTable), TypeError> {
    use crate::{
        constraint_solver::ConstraintSolver, environment::Environment, name_resolver::NameResolver,
        parser::parse, prelude::compile_prelude, type_checker::TypeChecker,
    };

    let mut symbol_table = compile_prelude().symbols.clone();
    let parsed = parse(input, "-".into());
    let resolver = NameResolver::new(&mut symbol_table);
    let resolved = resolver.resolve(parsed, &mut symbol_table);
    let checker = TypeChecker;
    let mut env = Environment::new();
    let mut inferred = checker.infer(resolved, &mut symbol_table, &mut env);
    let mut constraint_solver = ConstraintSolver::new(&mut inferred, &mut symbol_table);
    constraint_solver.solve();
    Ok((inferred, symbol_table.clone()))
}
