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

pub struct Prelude {
    pub symbols: SymbolTable,
    pub types: TypeDefs,
    pub schemes: HashMap<SymbolID, Scheme>,
    pub typed_exprs: TypedExprs,
}

lazy_static! {
    static ref PRELUDE_FOR_NAME_RESOLVER: Prelude = _compile_prelude_for_name_resolver();
    static ref PRELUDE_TYPED: Prelude = _compile_prelude();
}

pub fn compile_prelude_for_name_resolver() -> &'static Prelude {
    &PRELUDE_FOR_NAME_RESOLVER
}

pub fn compile_prelude() -> &'static Prelude {
    &PRELUDE_TYPED
}

pub fn _compile_prelude_for_name_resolver() -> Prelude {
    let source = load_stdlib_module("Optional").unwrap();
    let symbol_table = SymbolTable::default();
    let parsed = parse(source, 0);
    let (_resolved, symbol_table) = NameResolver::new(symbol_table).resolve(parsed);

    Prelude {
        symbols: symbol_table,
        types: Default::default(),
        schemes: Default::default(),
        typed_exprs: Default::default(),
    }
}

pub fn _compile_prelude() -> Prelude {
    let source = load_stdlib_module("Optional").unwrap();
    let symbol_table = SymbolTable::default();
    let parsed = parse(source, 0);
    let (resolved, mut symbol_table) = NameResolver::new(symbol_table).resolve(parsed);
    let checker = TypeChecker;
    let mut env = Environment::new();
    let mut inferred = checker.infer_without_prelude(&mut env, resolved, &mut symbol_table);
    let mut solver = ConstraintSolver::new(&mut inferred, &mut symbol_table);
    solver.solve().unwrap();

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
