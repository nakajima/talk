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
        constraint_solver::ConstraintSolver, name_resolver::NameResolver, parser::parse,
        type_checker::TypeChecker,
    };

    let parsed = parse(input).unwrap();
    let resolver = NameResolver::default();
    let resolved = resolver.resolve(parsed);
    let checker = TypeChecker;
    let mut inferred = checker.infer(resolved)?;
    let mut constraint_solver = ConstraintSolver::new(&mut inferred);
    constraint_solver.solve()?;
    Ok(inferred)
}
