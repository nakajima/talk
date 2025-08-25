use lazy_static::lazy_static;
use miette::Report;
use std::{collections::BTreeMap, path::PathBuf, process::exit};

use crate::{
    SymbolID, SymbolTable,
    compiling::driver::{Driver, DriverConfig},
    environment::Environment,
};

pub struct Prelude {
    pub symbols: SymbolTable,
    pub environment: Environment,
    // pub module: IRModule,
    pub global_scope: BTreeMap<String, SymbolID>,
}

lazy_static! {
    static ref PRELUDE_TYPED: Prelude = _compile_prelude();
}

pub fn compile_prelude() -> &'static Prelude {
    &PRELUDE_TYPED
}

#[cfg(feature = "wasm")]
fn load_files(driver: &mut Driver) {
    for (path, contents) in [
        ("core/Operators.tlk", include_str!("../core/Operators.tlk")),
        ("core/Optional.tlk", include_str!("../core/Optional.tlk")),
        ("core/Array.tlk", include_str!("../core/Array.tlk")),
        ("core/String.tlk", include_str!("../core/String.tlk")),
        // ("core/Iterable.tlk", include_str!("../core/Iterable.tlk")),
    ] {
        // For WASM, we'll use absolute paths starting from root
        let absolute_path = PathBuf::from("/").join(path);
        driver.update_file(&absolute_path, contents.to_string());
    }
}

#[allow(clippy::unwrap_used)]
#[cfg(not(feature = "wasm"))]
fn load_files(driver: &mut Driver) {
    // Get the current directory to make absolute paths
    let current_dir = std::env::current_dir().unwrap_or_else(|_| PathBuf::from("."));

    for file in [
        current_dir.join("core/Operators.tlk"),
        current_dir.join("core/Optional.tlk"),
        current_dir.join("core/Array.tlk"),
        current_dir.join("core/String.tlk"),
        // current_dir.join("core/Iterable.tlk"),
    ] {
        let absolute_path = file.canonicalize().unwrap_or_else(|_| file.clone());
        driver.update_file(&absolute_path, std::fs::read_to_string(&file).unwrap());
    }
}

pub fn _compile_prelude() -> Prelude {
    let _span = tracing::trace_span!("compile_prelude", prelude = true).entered();

    let mut driver = Driver::new(
        "Prelude",
        DriverConfig {
            executable: false,
            include_prelude: false,
            include_comments: false,
        },
    );

    crate::builtins::import_symbols(&mut driver.symbol_table);

    load_files(&mut driver);

    #[allow(clippy::unwrap_used)]
    let resolved = driver.parse().into_iter().next().unwrap().resolved(
        &mut driver.symbol_table,
        &driver.config,
        &driver.module_env,
    );
    let global_scope = resolved.stage.global_scope.clone();
    let unit = resolved.typed(&mut driver.symbol_table, &driver.config, &driver.module_env);

    let mut environment = unit.env.clone();
    let symbols = &driver.symbol_table;

    #[allow(clippy::panic)]
    if let Ok(session) = &driver.session.lock()
        && !session.diagnostics.is_empty()
    {
        for diagnostic in session.diagnostics.iter() {
            let source = driver.contents(&diagnostic.path);
            if let Some(meta) = unit.meta_for(&diagnostic.path) {
                tracing::error!("{:?}", Report::new(diagnostic.expand(&meta, &source)));
            }
        }

        if std::env::var("SHOW_BUILTIN_SYMBOLS").is_ok() {
            tracing::error!(
                "Prelude did not compile cleanly: {:#?}",
                session.diagnostics
            );
        } else {
            panic!(
                "Prelude did not compile cleanly: {:#?}",
                session.diagnostics
            )
        }
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
        symbols: symbols.clone(),
        environment,
        global_scope,
    }
}

#[cfg(test)]
mod tests {
    use crate::prelude::compile_prelude;

    #[test]
    fn compiles_clean() {
        compile_prelude();
    }
}
