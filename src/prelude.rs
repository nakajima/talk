use std::collections::HashMap;

use crate::{
    SymbolID, SymbolTable,
    constraint_solver::ConstraintSolver,
    environment::{Environment, TypedExprs},
    name_resolver::NameResolver,
    parser::parse,
    type_checker::{Scheme, TypeChecker, TypeDefs},
};

pub struct Prelude {
    pub symbols: SymbolTable,
    pub types: TypeDefs,
    pub schemes: HashMap<SymbolID, Scheme>,
    pub typed_exprs: TypedExprs,
}

pub fn compile_prelude() -> Prelude {
    let source = load_stdlib_module("Optional").unwrap();
    let mut symbol_table = SymbolTable::default();
    let parsed = parse(source, 0).unwrap();
    let resolved = NameResolver::new().resolve(parsed, &mut symbol_table);
    let checker = TypeChecker;
    let mut inferred = checker
        .infer_without_prelude(Environment::new(), resolved, &mut symbol_table)
        .unwrap();
    let mut solver = ConstraintSolver::new(&mut inferred, &mut symbol_table);
    solver.solve().unwrap();

    println!("Symbol Table: {:?}", symbol_table);

    let (types, schemes, typed_exprs) = inferred.export();

    Prelude {
        symbols: symbol_table,
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
