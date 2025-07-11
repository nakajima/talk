use talk::interpret::io::InterpreterIO;

use crate::console;

#[derive(Default)]
pub struct WasmIO {}

impl InterpreterIO for WasmIO {
    fn write_all(&mut self, buf: &[u8]) {
        console::log(str::from_utf8(buf).unwrap());
    }

    fn write_all_err(&mut self, buf: &[u8]) {
        console::error(str::from_utf8(buf).unwrap());
    }

    fn read(&mut self, buf: &mut Vec<u8>) {
        *buf = console::confirm("").as_bytes().to_vec();
    }
}
