use talk::{
    compiling::driver::{Driver, DriverConfig, Lowered, Source},
    ir::interpreter::Interpreter,
};
use wasm_bindgen::prelude::*;

#[wasm_bindgen]
pub fn run_program(source: &str) -> Result<String, JsValue> {
    install_panic_hook();

    let lowered = compile_source(source)?;
    let module = lowered.module("talk");
    let mut interpreter = Interpreter::new(module.program, Some(module.symbol_names));
    let result = interpreter.run();

    Ok(format!("{result:?}"))
}

#[wasm_bindgen]
pub fn version() -> String {
    env!("CARGO_PKG_VERSION").to_string()
}

type LoweredDriver = Driver<Lowered>;

fn compile_source(source: &str) -> Result<LoweredDriver, JsValue> {
    let driver = Driver::new(vec![Source::from(source)], DriverConfig::new("_"));

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
