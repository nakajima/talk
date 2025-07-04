use lazy_static::lazy_static;
use std::path::PathBuf;

use crate::{
    SymbolTable,
    compiling::driver::{Driver, DriverConfig},
    environment::Environment,
    lowering::ir_module::IRModule,
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

pub fn _compile_prelude() -> Prelude {
    let mut driver = Driver::new(DriverConfig {
        executable: false,
        include_prelude: false,
        include_comments: false,
    });
    for file in [
        PathBuf::from("./core/Optional.tlk"),
        PathBuf::from("./core/Operators.tlk"),
        PathBuf::from("./core/Array.tlk"),
        PathBuf::from("./core/String.tlk"),
        PathBuf::from("./core/Printable.tlk"),
    ] {
        #[allow(clippy::unwrap_used)]
        driver.update_file(&file, std::fs::read_to_string(&file).unwrap());
    }

    #[allow(clippy::unwrap_used)]
    let unit = driver.lower().into_iter().next().unwrap();
    let environment = unit.env.clone();
    let module = unit.module();
    let symbols = driver.symbol_table;

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

stdlib_modules!("Optional", "Array", "String", "Operators", "Printable");
