use talk::{
    compiling::driver::Driver, highlighter::Higlighter, interpret::interpreter::IRInterpreter,
    lowering::ir_printer::print, transforms::monomorphizer::Monomorphizer,
};
use wasm_bindgen::prelude::*;
use witgen::witgen;

use crate::io::WasmIO;

mod console;
mod io;

#[witgen]
#[wasm_bindgen(start)]
pub fn start() {
    console_error_panic_hook::set_once();
}

#[witgen]
#[wasm_bindgen]
pub struct TalkTalk {}

#[witgen]
#[wasm_bindgen]
pub fn ir(code: String) -> String {
    let mut driver = Driver::with_str(&code);
    let lowered = driver.lower().into_iter().next().unwrap();
    print(&lowered.module())
}

#[witgen]
#[wasm_bindgen]
pub fn run(code: String) {
    let mut driver = Driver::with_str(&code);
    let lowered = driver.lower().into_iter().next().unwrap();
    let mono = Monomorphizer::new(&lowered.env).run(lowered.module());
    let mut io = WasmIO::default();
    IRInterpreter::new(mono, &mut io, &driver.symbol_table)
        .run()
        .unwrap();
}

#[witgen]
#[wasm_bindgen]
pub fn higlight(code: String) -> Vec<HighlightToken> {
    Higlighter::new(&code)
        .highlight()
        .into_iter()
        .map(Into::into)
        .collect()
}
