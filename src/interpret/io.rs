use std::io::{Read, Write};

pub trait InterpreterIO {
    fn write_all(&self, buf: &[u8]);
    fn write_all_err(&self, buf: &[u8]);
    fn read(&self, buf: &mut Vec<u8>);
}

#[derive(Default)]
pub struct InterpreterStdIO {}

#[allow(clippy::unwrap_used)]
impl InterpreterIO for InterpreterStdIO {
    fn write_all(&self, buf: &[u8]) {
        std::io::stdout().write_all(buf).unwrap();
        std::io::stdout().flush().unwrap();
    }

    fn write_all_err(&self, buf: &[u8]) {
        std::io::stderr().write_all(buf).unwrap();
        std::io::stderr().flush().unwrap();
    }

    fn read(&self, buf: &mut Vec<u8>) {
        std::io::stdin().read_to_end(buf).unwrap();
    }
}

pub mod test_io {
    use std::cell::RefCell;

    use crate::interpret::io::InterpreterIO;

    #[derive(Default)]
    pub struct TestIO {
        pub stdout: RefCell<Vec<u8>>,
        pub stderr: RefCell<Vec<u8>>,
        pub stdin: RefCell<Vec<u8>>,
    }

    impl TestIO {
        pub fn new() -> Self {
            Self::default()
        }

        pub fn stdout(&self) -> Vec<u8> {
            self.stdout.borrow().clone()
        }

        pub fn stderr(&self) -> Vec<u8> {
            self.stderr.borrow().clone()
        }
    }

    #[allow(clippy::unwrap_used)]
    impl InterpreterIO for TestIO {
        fn write_all(&self, buf: &[u8]) {
            self.stdout.borrow_mut().extend_from_slice(buf);
        }

        fn write_all_err(&self, buf: &[u8]) {
            self.stderr.borrow_mut().extend_from_slice(buf);
        }

        fn read(&self, buf: &mut Vec<u8>) {
            buf.copy_from_slice(&self.stdin.borrow_mut());
        }
    }
}
