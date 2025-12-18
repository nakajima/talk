use talk::{
    compiling::driver::{Driver, DriverConfig, Lowered, Source},
    formatter::{DebugHTMLFormatter, Formatter},
    ir::interpreter::Interpreter,
};
use wasm_bindgen::prelude::*;

#[wasm_bindgen]
pub fn run_program(source: &str) -> Result<String, JsValue> {
    install_panic_hook();

    let lowered = compile_source(source)?;
    let module = lowered.module("talk");
    let interpreter = Interpreter::new(module.program, Some(module.symbol_names));
    let result = interpreter.run();

    Ok(format!("{result:?}"))
}

#[wasm_bindgen]
pub fn debug_html(source: &str) -> Result<String, JsValue> {
    install_panic_hook();

    let lowered = compile_source(source)?;
    let Some(ast) = lowered.phase.asts.values().next() else {
        return Err(JsValue::from_str("no source was provided"));
    };

    let formatter =
        Formatter::new_with_decorators(&ast.meta, vec![Box::new(DebugHTMLFormatter {})]);

    Ok(formatter.format(&ast.roots, 80))
}

#[wasm_bindgen]
pub fn version() -> String {
    env!("CARGO_PKG_VERSION").to_string()
}

type LoweredDriver = Driver<Lowered>;

fn compile_source(source: &str) -> Result<LoweredDriver, JsValue> {
    let driver = Driver::new(vec![Source::from(source)], DriverConfig::default());

    driver
        .parse()
        .map_err(to_js_error)?
        .resolve_names()
        .map_err(to_js_error)?
        .typecheck()
        .map_err(to_js_error)?
        .lower()
        .map_err(to_js_error)
}

fn to_js_error(err: impl std::fmt::Debug) -> JsValue {
    JsValue::from_str(&format!("{err:?}"))
}

fn install_panic_hook() {
    console_error_panic_hook::set_once();
}
