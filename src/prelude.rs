use lazy_static::lazy_static;
use std::{collections::BTreeMap, path::PathBuf, process::exit};

use crate::{
    SymbolID, SymbolTable,
    compiling::driver::{Driver, DriverConfig},
    environment::Environment,
    lowering::ir_module::IRModule,
};

pub struct Prelude {
    pub symbols: SymbolTable,
    pub environment: Environment,
    pub module: IRModule,
    pub global_scope: BTreeMap<String, SymbolID>,
}

lazy_static! {
    static ref PRELUDE_TYPED: Prelude = _compile_prelude();
}

pub fn compile_prelude() -> &'static Prelude {
    &PRELUDE_TYPED
}

pub fn _compile_prelude() -> Prelude {
    let _span = tracing::trace_span!("compile_prelude", prelude = true).entered();

    let mut driver = Driver::new(DriverConfig {
        executable: false,
        include_prelude: false,
        include_comments: false,
    });
    for file in [
        PathBuf::from("./core/Operators.tlk"),
        PathBuf::from("./core/Optional.tlk"),
        PathBuf::from("./core/Array.tlk"),
        PathBuf::from("./core/String.tlk"),
    ] {
        #[allow(clippy::unwrap_used)]
        driver.update_file(&file, std::fs::read_to_string(&file).unwrap());
    }

    #[allow(clippy::unwrap_used)]
    let resolved = driver
        .parse()
        .into_iter()
        .next()
        .unwrap()
        .resolved(&mut driver.symbol_table, &driver.config);
    let global_scope = resolved.stage.global_scope.clone();
    let unit = resolved
        .typed(&mut driver.symbol_table, &driver.config)
        .lower(&mut driver.symbol_table, &driver.config, IRModule::new());
    let mut environment = unit.env.clone();
    let module = unit.module();
    let symbols = driver.symbol_table;

    #[allow(clippy::panic)]
    if let Ok(session) = driver.session.lock()
        && !session.diagnostics.is_empty()
    {
        tracing::error!(
            "Prelude did not compile cleanly: {:#?}",
            session.diagnostics
        )
    }

    #[allow(clippy::unwrap_used)]
    if std::env::var("SHOW_BUILTIN_SYMBOLS").is_ok() {
        println!(
            "pub const ARRAY: SymbolID = SymbolID({});",
            symbols.lookup("Array").unwrap().0
        );
        println!(
            "pub const OPTIONAL: SymbolID = SymbolID({});",
            symbols.lookup("Optional").unwrap().0
        );
        println!(
            "pub const STRING: SymbolID = SymbolID({});",
            symbols.lookup("String").unwrap().0
        );
        println!(
            "pub const ADD: SymbolID = SymbolID({});",
            symbols.lookup("Add").unwrap().0
        );
        println!(
            "pub const SUBTRACT: SymbolID = SymbolID({});",
            symbols.lookup("Subtract").unwrap().0
        );
        println!(
            "pub const MULTIPLY: SymbolID = SymbolID({});",
            symbols.lookup("Multiply").unwrap().0
        );
        println!(
            "pub const DIVIDE: SymbolID = SymbolID({});",
            symbols.lookup("Divide").unwrap().0
        );

        exit(0)
    }

    environment.clear_constraints();

    Prelude {
        symbols,
        environment,
        global_scope,
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

stdlib_modules!("Operators", "Optional", "Array", "String");

#[cfg(test)]
mod tests {
    use crate::prelude::compile_prelude;

    #[test]
    fn compiles_clean() {
        compile_prelude();
    }
}
