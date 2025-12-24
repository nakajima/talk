use std::{
    collections::VecDeque,
    io::{Read, Write},
};

#[derive(Debug, Clone)]
pub enum IOError {
    ReadError(String),
    WriteError(String),
    Unsupported,
}

pub trait IO {
    fn write_stdout(&mut self, bytes: &[u8]) -> Result<(), IOError>;
    fn write_stderr(&mut self, bytes: &[u8]) -> Result<(), IOError>;
    fn read_stdio(&mut self, bytes: &mut [u8]) -> Result<usize, IOError>;
}

pub struct StdioIO {}
impl IO for StdioIO {
    fn write_stdout(&mut self, bytes: &[u8]) -> Result<(), IOError> {
        std::io::stdout()
            .write_all(bytes)
            .map_err(|a| IOError::WriteError(format!("{a:?}")))?;
        std::io::stdout()
            .flush()
            .map_err(|a| IOError::WriteError(format!("{a:?}")))
    }

    fn write_stderr(&mut self, bytes: &[u8]) -> Result<(), IOError> {
        std::io::stderr()
            .write_all(bytes)
            .map_err(|a| IOError::WriteError(format!("{a:?}")))?;
        std::io::stderr()
            .flush()
            .map_err(|a| IOError::WriteError(format!("{a:?}")))
    }

    fn read_stdio(&mut self, bytes: &mut [u8]) -> Result<usize, IOError> {
        std::io::stdin()
            .read(bytes)
            .map_err(|a| IOError::ReadError(format!("{a:?}")))
    }
}

#[derive(Default, Debug)]
pub struct CaptureIO {
    pub stdout: Vec<u8>,
    pub stderr: Vec<u8>,
    pub stdin: VecDeque<u8>,
}
impl IO for CaptureIO {
    fn write_stdout(&mut self, bytes: &[u8]) -> Result<(), IOError> {
        self.stdout.extend_from_slice(bytes);
        Ok(())
    }

    fn write_stderr(&mut self, bytes: &[u8]) -> Result<(), IOError> {
        self.stderr.extend_from_slice(bytes);
        Ok(())
    }

    fn read_stdio(&mut self, bytes: &mut [u8]) -> Result<usize, IOError> {
        let len = self.stdin.len();
        for byte in bytes {
            *byte = self.stdin.pop_front().unwrap_or(0);
        }
        Ok(len)
    }
}

pub struct MultiWriteIO<'a> {
    pub adapters: Vec<Box<&'a mut dyn IO>>,
}
impl<'a> IO for MultiWriteIO<'a> {
    fn write_stdout(&mut self, bytes: &[u8]) -> Result<(), IOError> {
        for io in self.adapters.iter_mut() {
            io.write_stdout(bytes)?
        }

        Ok(())
    }

    fn write_stderr(&mut self, bytes: &[u8]) -> Result<(), IOError> {
        for io in self.adapters.iter_mut() {
            io.write_stderr(bytes)?
        }

        Ok(())
    }

    fn read_stdio(&mut self, _bytes: &mut [u8]) -> Result<usize, IOError> {
        Err(IOError::Unsupported)
    }
}
