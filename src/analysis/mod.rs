#[cfg(test)]
use crate::{SourceFile, Typed, type_checker::TypeError};

pub mod constraint_solver;
pub mod environment;
pub mod name_resolver;
pub mod type_checker;
pub mod typed_expr;

#[cfg(test)]
pub fn check(input: &'static str) -> Result<SourceFile<Typed>, TypeError> {
    use crate::{
        SymbolTable, constraint_solver::ConstraintSolver, name_resolver::NameResolver,
        parser::parse, type_checker::TypeChecker,
    };

    let mut symbol_table = SymbolTable::default();

    let parsed = parse(input, 123).unwrap();
    let resolver = NameResolver::default();
    let resolved = resolver.resolve(parsed, &mut symbol_table);
    let checker = TypeChecker;
    let mut inferred = checker.infer(resolved, &mut symbol_table)?;
    let mut constraint_solver = ConstraintSolver::new(&mut inferred, &mut symbol_table);
    constraint_solver.solve()?;
    Ok(inferred)
}
