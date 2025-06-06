use lazy_static::lazy_static;
use std::collections::HashMap;

use crate::{
    SymbolID, SymbolTable,
    constraint_solver::ConstraintSolver,
    environment::{Environment, TypedExprs},
    name_resolver::NameResolver,
    parser::parse,
    type_checker::{Scheme, TypeChecker, TypeDefs},
};

lazy_static! {
    pub static ref PRELUDE: Prelude = compile_prelude();
}

pub struct Prelude {
    pub symbols: SymbolTable,
    pub types: TypeDefs,
    pub schemes: HashMap<SymbolID, Scheme>,
    pub typed_exprs: TypedExprs,
}

fn compile_prelude() -> Prelude {
    let source = load_stdlib_module("Optional").unwrap();
    let parsed = parse(source).unwrap();
    let resolved = NameResolver::new().resolve(parsed);
    let checker = TypeChecker;
    let mut inferred = checker
        .infer_without_prelude(Environment::new(), resolved)
        .unwrap();
    let mut solver = ConstraintSolver::new(&mut inferred);
    solver.solve().unwrap();

    let (symbols, types, schemes, typed_exprs) = inferred.export();

    Prelude {
        symbols,
        types,
        schemes,
        typed_exprs,
    }
}

macro_rules! stdlib_modules {
  ($($name:literal),*) => {
      pub fn load_stdlib_module(name: &str) -> Option<&'static str> {
          match name {
              $(
                  $name => Some(include_str!(concat!("../core/", $name, ".tlk"))),
              )*
              _ => None,
          }
      }
  };
}

stdlib_modules!("Optional");
