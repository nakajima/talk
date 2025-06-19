use lazy_static::lazy_static;
use std::{collections::HashMap, path::PathBuf};

use crate::{
    SymbolID, SymbolTable,
    compiling::driver::{Driver, DriverConfig},
    environment::TypedExprs,
    lowering::{ir_module::IRModule, ir_printer::print},
    type_checker::{Scheme, TypeDefs},
};

pub struct Prelude {
    pub symbols: SymbolTable,
    pub types: TypeDefs,
    pub schemes: HashMap<SymbolID, Scheme>,
    pub typed_exprs: TypedExprs,
    pub module: IRModule,
}

lazy_static! {
    static ref PRELUDE_TYPED: Prelude = _compile_prelude();
}

pub fn compile_prelude() -> &'static Prelude {
    &PRELUDE_TYPED
}

// pub fn _compile_prelude_for_name_resolver() -> Prelude {
//     let source = &[
//         load_stdlib_module("Optional").unwrap(),
//         load_stdlib_module("Array").unwrap(),
//     ]
//     .join("\n");
//     let mut symbol_table = SymbolTable::base();
//     let parsed = parse(source, "prelude".into());
//     let _ = NameResolver::new(&mut symbol_table).resolve(parsed, &mut symbol_table);

//     Prelude {
//         symbols: symbol_table,
//         types: Default::default(),
//         schemes: Default::default(),
//         typed_exprs: Default::default(),
//     }
// }

fn fresh_driver() -> Driver {
    let mut driver = Driver::new(DriverConfig {
        executable: false,
        include_prelude: false,
    });
    for file in [
        PathBuf::from("./core/Optional.tlk"),
        PathBuf::from("./core/Array.tlk"),
    ] {
        driver.update_file(&file, std::fs::read_to_string(&file).unwrap());
    }

    driver
}

#[track_caller]
pub fn _compile_prelude() -> Prelude {
    if cfg!(debug_assertions) {
        let loc = std::panic::Location::caller();
        println!("compiling prelude from {}:{}", loc.file(), loc.line());
    }

    // let source = &[
    //     load_stdlib_module("Optional").unwrap(),
    //     load_stdlib_module("Array").unwrap(),
    // ]
    // .join("\n");
    // println!("{}", source);
    // let mut symbol_table = SymbolTable::base();
    // let parsed = parse(source, "prelude".into());
    // let resolved = NameResolver::new(&mut symbol_table).resolve(parsed, &mut symbol_table);
    // let checker = TypeChecker;
    // let mut env = Environment::new();
    // let mut inferred = checker.infer_without_prelude(&mut env, resolved, &mut symbol_table);
    // let mut solver = ConstraintSolver::new(&mut inferred, &mut symbol_table);
    // solver.solve();

    // if !inferred.diagnostics().is_empty() {
    //     panic!("Error compiling prelude: {:#?}", inferred.diagnostics());
    // }

    // let (types, schemes, typed_exprs) = inferred.clone().export();

    let mut driver = fresh_driver();

    let checked = driver.check();
    // let lowered = driver.lower();

    let symbols = driver.symbol_table;
    let types = checked.iter().flat_map(|f| f.type_defs()).collect();
    let schemes = checked.iter().flat_map(|f| f.schemes()).collect();
    let typed_exprs = checked.iter().flat_map(|f| f.typed_exprs()).collect();

    let mut driver = fresh_driver();
    let module = driver.lower().into_iter().next().unwrap().module();
    println!("{module:?}");

    println!(
        "prelude module:\n{}",
        print(&driver.lower().into_iter().next().unwrap().module())
    );

    Prelude {
        symbols,
        types,
        schemes,
        typed_exprs,
        module,
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

stdlib_modules!("Optional", "Array");
