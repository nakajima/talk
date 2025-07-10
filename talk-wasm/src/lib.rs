use talk::{
    compiling::driver::Driver, interpret::interpreter::IRInterpreter, lowering::ir_printer::print,
    transforms::monomorphizer::Monomorphizer,
};
use wasm_bindgen::prelude::*;

use crate::io::WasmIO;

mod console;
mod io;

#[wasm_bindgen(start)]
pub fn start() {
    console_error_panic_hook::set_once();
}

#[wasm_bindgen]
pub struct TalkTalk {}

#[wasm_bindgen]
pub fn ir(code: String) -> String {
    let mut driver = Driver::with_str(&code);
    let lowered = driver.lower().into_iter().next().unwrap();
    print(&lowered.module())
}

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
