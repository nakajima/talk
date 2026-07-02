#![cfg_attr(not(test), deny(clippy::unwrap_used))]
#![cfg_attr(not(test), deny(clippy::expect_used))]
#![cfg_attr(not(test), deny(clippy::panic))]
#![cfg_attr(not(test), deny(clippy::todo))]

use std::panic::{AssertUnwindSafe, catch_unwind};
use std::slice;
use talk_runtime::Module;
use talk_runtime::interp::Value;

#[unsafe(no_mangle)]
pub extern "C" fn talk_runtime_run(ptr: *const u8, len: usize) -> i32 {
    let result = catch_unwind(AssertUnwindSafe(|| Runtime::new(ptr, len).run()));
    match result {
        Ok(code) => code,
        Err(_) => {
            eprintln!("talk runtime: internal panic");
            1
        }
    }
}

struct Runtime {
    ptr: *const u8,
    len: usize,
}

impl Runtime {
    fn new(ptr: *const u8, len: usize) -> Self {
        Self { ptr, len }
    }

    fn run(&self) -> i32 {
        let Some(bytes) = self.bytes() else {
            eprintln!("talk runtime: null bytecode pointer");
            return 1;
        };
        let module = match Module::decode_bytecode(bytes) {
            Ok(module) => module,
            Err(err) => {
                eprintln!("talk runtime: {err}");
                return 1;
            }
        };
        let mut io = talk_runtime::io::StdioIO;
        match talk_runtime::interp::run(&module, &mut io) {
            Ok(Value::Void) => 0,
            Ok(value) => {
                println!("{value:?}");
                0
            }
            Err(err) => {
                eprintln!("{err}");
                1
            }
        }
    }

    fn bytes(&self) -> Option<&[u8]> {
        if self.ptr.is_null() {
            return None;
        }
        // SAFETY: The generated launcher passes a pointer to a static byte
        // array and its exact length. Other C callers must uphold the same
        // contract for the duration of this call.
        Some(unsafe { slice::from_raw_parts(self.ptr, self.len) })
    }
}
