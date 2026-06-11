//! The machine's IO boundary. Both execution engines (reference evaluator
//! and bytecode VM) write through this trait so tests capture output and
//! `talk run` reaches the host (the CaptureIO/StdioIO split carried over
//! from the previous backend; CaptureIO is what example goldens and
//! differential tests compare).

use std::io::Write;

pub trait IO {
    /// POSIX-shaped write: bytes to a file descriptor, returning the byte
    /// count or a negative errno.
    fn write(&mut self, fd: i64, bytes: &[u8]) -> i64;
}

/// Host stdio (fd 1 = stdout, fd 2 = stderr).
#[derive(Default)]
pub struct StdioIO;

impl IO for StdioIO {
    fn write(&mut self, fd: i64, bytes: &[u8]) -> i64 {
        let result = match fd {
            1 => std::io::stdout().write_all(bytes),
            2 => std::io::stderr().write_all(bytes),
            _ => return -9, // EBADF
        };
        match result {
            Ok(()) => bytes.len() as i64,
            Err(_) => -5, // EIO
        }
    }
}

/// Captures writes for tests and the REPL.
#[derive(Default)]
pub struct CaptureIO {
    pub out: Vec<u8>,
    pub err: Vec<u8>,
}

impl IO for CaptureIO {
    fn write(&mut self, fd: i64, bytes: &[u8]) -> i64 {
        match fd {
            1 => self.out.extend_from_slice(bytes),
            2 => self.err.extend_from_slice(bytes),
            _ => return -9, // EBADF
        }
        bytes.len() as i64
    }
}
