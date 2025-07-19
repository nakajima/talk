use lazy_static::lazy_static;
use miette::Report;
use std::{collections::BTreeMap, path::PathBuf, process::exit};

use crate::{
    SymbolID, SymbolTable,
    compiling::{
        compiled_module::CompiledModule,
        driver::{Driver, DriverConfig},
    },
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
    static ref PRELUDE_TYPED: CompiledModule = _compile_prelude();
}

pub fn compile_prelude() -> &'static CompiledModule {
    &PRELUDE_TYPED
}

#[cfg(feature = "wasm")]
fn load_files(driver: &mut Driver) {
    for (path, contents) in [
        (
            "./core/Operators.tlk",
            include_str!("../core/Operators.tlk"),
        ),
        ("./core/Optional.tlk", include_str!("../core/Optional.tlk")),
        ("./core/Array.tlk", include_str!("../core/Array.tlk")),
        ("./core/String.tlk", include_str!("../core/String.tlk")),
        // ("./core/Iterable.tlk", include_str!("../core/Iterable.tlk")),
    ] {
        driver.update_file(&PathBuf::from(path), contents.to_string());
    }
}

#[cfg(not(feature = "wasm"))]
fn load_files(driver: &mut Driver) {
    for file in [
        PathBuf::from("./core/Operators.tlk"),
        PathBuf::from("./core/Optional.tlk"),
        PathBuf::from("./core/Array.tlk"),
        PathBuf::from("./core/String.tlk"),
        // PathBuf::from("./core/Iterable.tlk"),
    ] {
        #[allow(clippy::unwrap_used)]
        driver.update_file(&file, std::fs::read_to_string(&file).unwrap());
    }
}

pub fn _compile_prelude() -> CompiledModule {
    let _span = tracing::trace_span!("compile_prelude", prelude = true).entered();

    let mut driver = Driver::new(
        "Prelude",
        DriverConfig {
            executable: false,
            include_prelude: false,
            include_comments: false,
        },
    );

    crate::builtins::import_symbols_into(&mut driver.symbol_table);

    load_files(&mut driver);

    #[allow(clippy::unwrap_used)]
    if std::env::var("SHOW_BUILTIN_SYMBOLS").is_ok() {
        let resolved = driver.parse().into_iter().next().unwrap().resolved(
            &mut driver.symbol_table,
            &driver.config,
            &driver.module_env,
        );
        let global_scope = resolved.stage.global_scope.clone();
        let unit = resolved
            .typed(&mut driver.symbol_table, &driver.config, &driver.module_env)
            .lower(
                &mut driver.symbol_table,
                &driver.config,
                IRModule::new(),
                &driver.module_env,
            );
        let mut environment = unit.env.clone();
        let module = unit.module();
        let symbols = &driver.symbol_table;

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

    #[allow(clippy::expect_used)]
    driver
        .compile_modules()
        .expect("Unable to compile prelude.")
        .first()
        .expect("Did not get prelude module")
        .clone()
}

#[cfg(test)]
mod tests {
    use crate::prelude::compile_prelude;

    #[test]
    fn compiles_clean() {
        compile_prelude();
    }
}
