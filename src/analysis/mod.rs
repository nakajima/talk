use crate::{SourceFile, SymbolTable, Typed, type_checker::TypeError};

pub mod constraint_solver;
pub mod environment;
pub mod name_resolver;
pub mod type_checker;
pub mod typed_expr;

#[cfg(test)]
pub fn check(input: &str) -> Result<SourceFile<Typed>, TypeError> {
    use crate::{
        constraint_solver::ConstraintSolver, environment::Environment, name_resolver::NameResolver,
        parser::parse, prelude::compile_prelude, type_checker::TypeChecker,
    };

    let symbol_table = &compile_prelude().symbols;
    let parsed = parse(input, 123);
    let resolver = NameResolver::new(symbol_table.clone());
    let (resolved, mut symbol_table) = resolver.resolve(parsed);
    let checker = TypeChecker;
    let mut env = Environment::new();
    let mut inferred = checker.infer(resolved, &mut symbol_table, &mut env);
    let mut constraint_solver = ConstraintSolver::new(&mut inferred, &mut symbol_table);
    constraint_solver.solve()?;
    Ok(inferred)
}

pub fn check_with_symbols(input: &str) -> Result<(SourceFile<Typed>, SymbolTable), TypeError> {
    use crate::{
        constraint_solver::ConstraintSolver, environment::Environment, name_resolver::NameResolver,
        parser::parse, prelude::compile_prelude, type_checker::TypeChecker,
    };

    let symbol_table = &compile_prelude().symbols;
    let parsed = parse(input, 123);
    let resolver = NameResolver::new(symbol_table.clone());
    let (resolved, mut symbol_table) = resolver.resolve(parsed);
    let checker = TypeChecker;
    let mut env = Environment::new();
    let mut inferred = checker.infer(resolved, &mut symbol_table, &mut env);
    let mut constraint_solver = ConstraintSolver::new(&mut inferred, &mut symbol_table);
    constraint_solver.solve()?;
    Ok((inferred, symbol_table))
}
