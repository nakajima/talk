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

    // File I/O operations - return values follow POSIX conventions
    // (negative values indicate errors, using negated errno)

    /// Open a file. Returns fd on success, negative errno on failure.
    fn io_open(&mut self, path: &[u8], flags: i64, mode: i64) -> i64;

    /// Read from fd into buffer. Returns bytes read on success, negative errno on failure.
    fn io_read(&mut self, fd: i64, buf: &mut [u8]) -> i64;

    /// Write buffer to fd. Returns bytes written on success, negative errno on failure.
    fn io_write(&mut self, fd: i64, buf: &[u8]) -> i64;

    /// Close fd. Returns 0 on success, negative errno on failure.
    fn io_close(&mut self, fd: i64) -> i64;

    /// Control operation on fd. Returns operation-specific value or negative errno.
    fn io_ctl(&mut self, fd: i64, op: i64, arg: i64) -> i64;

    /// Poll fds for events. fds is array of (fd: i32, events: i16, revents: i16).
    /// Returns number of ready fds on success, negative errno on failure.
    fn io_poll(&mut self, fds: &mut [(i32, i16, i16)], timeout: i64) -> i64;

    /// Sleep for ms milliseconds. Returns 0 on success.
    fn io_sleep(&mut self, ms: i64) -> i64;
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

    fn io_open(&mut self, path: &[u8], flags: i64, mode: i64) -> i64 {
        #[cfg(unix)]
        {
            use std::ffi::CString;

            // Convert path to CString
            let Ok(path_cstr) = CString::new(path) else {
                return -libc::EINVAL as i64;
            };

            // Use libc::open directly for full flag support
            let fd = unsafe { libc::open(path_cstr.as_ptr(), flags as i32, mode as u32) };

            if fd < 0 { -errno() as i64 } else { fd as i64 }
        }

        #[cfg(not(unix))]
        {
            let _ = (path, flags, mode);
            -1 // EPERM
        }
    }

    fn io_read(&mut self, fd: i64, buf: &mut [u8]) -> i64 {
        #[cfg(unix)]
        {
            let result = unsafe { libc::read(fd as i32, buf.as_mut_ptr() as *mut _, buf.len()) };

            if result < 0 {
                -errno() as i64
            } else {
                result as i64
            }
        }

        #[cfg(not(unix))]
        {
            let _ = (fd, buf);
            -1 // EPERM
        }
    }

    fn io_write(&mut self, fd: i64, buf: &[u8]) -> i64 {
        #[cfg(unix)]
        {
            let result = unsafe { libc::write(fd as i32, buf.as_ptr() as *const _, buf.len()) };

            if result < 0 {
                -errno() as i64
            } else {
                result as i64
            }
        }

        #[cfg(not(unix))]
        {
            let _ = (fd, buf);
            -1 // EPERM
        }
    }

    fn io_close(&mut self, fd: i64) -> i64 {
        #[cfg(unix)]
        {
            let result = unsafe { libc::close(fd as i32) };

            if result < 0 { -errno() as i64 } else { 0 }
        }

        #[cfg(not(unix))]
        {
            let _ = fd;
            -1 // EPERM
        }
    }

    fn io_ctl(&mut self, fd: i64, op: i64, arg: i64) -> i64 {
        #[cfg(unix)]
        {
            let result = unsafe { libc::ioctl(fd as i32, op as u64, arg) };

            if result < 0 {
                -errno() as i64
            } else {
                result as i64
            }
        }

        #[cfg(not(unix))]
        {
            let _ = (fd, op, arg);
            -1 // EPERM
        }
    }

    fn io_poll(&mut self, fds: &mut [(i32, i16, i16)], timeout: i64) -> i64 {
        #[cfg(unix)]
        {
            // Convert our tuple format to pollfd structs
            let mut pollfds: Vec<libc::pollfd> = fds
                .iter()
                .map(|(fd, events, _)| libc::pollfd {
                    fd: *fd,
                    events: *events,
                    revents: 0,
                })
                .collect();

            let result =
                unsafe { libc::poll(pollfds.as_mut_ptr(), pollfds.len() as u64, timeout as i32) };

            // Copy revents back
            for (i, pfd) in pollfds.iter().enumerate() {
                fds[i].2 = pfd.revents;
            }

            if result < 0 {
                -errno() as i64
            } else {
                result as i64
            }
        }

        #[cfg(not(unix))]
        {
            let _ = (fds, timeout);
            -1 // EPERM
        }
    }

    fn io_sleep(&mut self, ms: i64) -> i64 {
        std::thread::sleep(std::time::Duration::from_millis(ms as u64));
        0
    }
}

#[cfg(unix)]
fn errno() -> i32 {
    std::io::Error::last_os_error().raw_os_error().unwrap_or(0)
}

#[derive(Default, Debug)]
pub struct CaptureIO {
    pub stdout: Vec<u8>,
    pub stderr: Vec<u8>,
    pub stdin: VecDeque<u8>,
    // For testing: simulated file system
    pub files: std::collections::HashMap<i64, Vec<u8>>,
    pub file_positions: std::collections::HashMap<i64, usize>,
    next_fd: i64,
}

impl CaptureIO {
    /// Create a simulated file for testing
    pub fn create_file(&mut self, content: Vec<u8>) -> i64 {
        let fd = self.next_fd + 3; // Start after stdin/stdout/stderr
        self.next_fd += 1;
        self.files.insert(fd, content);
        self.file_positions.insert(fd, 0);
        fd
    }
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

    fn io_open(&mut self, _path: &[u8], _flags: i64, _mode: i64) -> i64 {
        // For testing, just return a simulated fd
        let fd = self.next_fd + 3;
        self.next_fd += 1;
        self.files.insert(fd, Vec::new());
        self.file_positions.insert(fd, 0);
        fd
    }

    fn io_read(&mut self, fd: i64, buf: &mut [u8]) -> i64 {
        if fd == 0 {
            return self.read_stdio(buf).unwrap_or(0) as i64;
        }
        if let Some(content) = self.files.get(&fd) {
            let pos = self.file_positions.get(&fd).copied().unwrap_or(0);
            let remaining = &content[pos..];
            let to_read = std::cmp::min(buf.len(), remaining.len());
            buf[..to_read].copy_from_slice(&remaining[..to_read]);
            self.file_positions.insert(fd, pos + to_read);
            to_read as i64
        } else {
            -9 // EBADF
        }
    }

    fn io_write(&mut self, fd: i64, buf: &[u8]) -> i64 {
        if fd == 1 {
            self.stdout.extend_from_slice(buf);
            return buf.len() as i64;
        }
        if fd == 2 {
            self.stderr.extend_from_slice(buf);
            return buf.len() as i64;
        }
        if let Some(content) = self.files.get_mut(&fd) {
            content.extend_from_slice(buf);
            buf.len() as i64
        } else {
            -9 // EBADF
        }
    }

    fn io_close(&mut self, fd: i64) -> i64 {
        if self.files.remove(&fd).is_some() {
            self.file_positions.remove(&fd);
            0
        } else {
            -9 // EBADF
        }
    }

    fn io_ctl(&mut self, _fd: i64, _op: i64, _arg: i64) -> i64 {
        // Not implemented for testing
        -22 // EINVAL
    }

    fn io_poll(&mut self, fds: &mut [(i32, i16, i16)], _timeout: i64) -> i64 {
        // For testing, mark all fds as ready
        let mut ready = 0i64;
        for (fd, events, revents) in fds.iter_mut() {
            if self.files.contains_key(&(*fd as i64)) {
                *revents = *events; // All requested events are ready
                ready += 1;
            } else {
                *revents = 0;
            }
        }
        ready
    }

    fn io_sleep(&mut self, _ms: i64) -> i64 {
        // No-op for testing
        0
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

    fn io_open(&mut self, _path: &[u8], _flags: i64, _mode: i64) -> i64 {
        -1 // EPERM - not supported for multi-write
    }

    fn io_read(&mut self, _fd: i64, _buf: &mut [u8]) -> i64 {
        -1 // EPERM
    }

    fn io_write(&mut self, _fd: i64, _buf: &[u8]) -> i64 {
        -1 // EPERM
    }

    fn io_close(&mut self, _fd: i64) -> i64 {
        -1 // EPERM
    }

    fn io_ctl(&mut self, _fd: i64, _op: i64, _arg: i64) -> i64 {
        -1 // EPERM
    }

    fn io_poll(&mut self, _fds: &mut [(i32, i16, i16)], _timeout: i64) -> i64 {
        -1 // EPERM
    }

    fn io_sleep(&mut self, _ms: i64) -> i64 {
        -1 // EPERM - not supported for multi-write
    }
}
