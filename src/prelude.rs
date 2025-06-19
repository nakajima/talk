use lazy_static::lazy_static;
use std::path::PathBuf;

use crate::{
    SymbolTable,
    compiling::driver::{Driver, DriverConfig},
    environment::Environment,
    lowering::{ir_module::IRModule, ir_printer},
};

pub struct Prelude {
    pub symbols: SymbolTable,
    pub environment: Environment,
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

pub fn _compile_prelude() -> Prelude {
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

    let module = driver.lower().into_iter().next().unwrap().module();
    let symbols = driver.symbol_table;
    let environment = driver.units[0].clone().env;

    Prelude {
        symbols,
        environment,
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
