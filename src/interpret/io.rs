use std::io::{Read, Write};

pub trait InterpreterIO {
    fn write_all(&mut self, buf: &[u8]);
    fn write_all_err(&mut self, buf: &[u8]);
    fn read_exact(&mut self, buf: &mut [u8]);
}

#[derive(Default)]
pub struct InterpreterStdIO {}

#[allow(clippy::unwrap_used)]
impl InterpreterIO for InterpreterStdIO {
    fn write_all(&mut self, buf: &[u8]) {
        std::io::stdout().write_all(buf).unwrap();
        std::io::stdout().flush().unwrap();
    }

    fn write_all_err(&mut self, buf: &[u8]) {
        std::io::stderr().write_all(buf).unwrap();
        std::io::stderr().flush().unwrap();
    }

    fn read_exact(&mut self, buf: &mut [u8]) {
        std::io::stdin().read_exact(buf).unwrap();
    }
}

#[cfg(test)]
pub mod test_io {
    use std::collections::VecDeque;

    use crate::interpret::io::InterpreterIO;

    #[derive(Default)]
    pub struct TestIO {
        pub stdout: Vec<u8>,
        pub stderr: Vec<u8>,
        pub stdin: VecDeque<u8>,
    }

    impl TestIO {
        pub fn new() -> Self {
            Self::default()
        }
    }

    #[allow(clippy::unwrap_used)]
    impl InterpreterIO for TestIO {
        fn write_all(&mut self, buf: &[u8]) {
            self.stdout.extend_from_slice(buf);
        }

        fn write_all_err(&mut self, buf: &[u8]) {
            self.stderr.extend_from_slice(buf);
        }

        fn read_exact(&mut self, buf: &mut [u8]) {
            for i in buf {
                *i = self.stdin.pop_front().unwrap()
            }
        }
    }
}
