//! The machine's IO boundary. Both execution engines (reference evaluator
//! and bytecode VM) run against this trait, so two-engine tests agree on
//! io semantics by construction (the CaptureIO/StdioIO split carried over
//! from the previous backend; CaptureIO is what the expected-output files
//! and two-engine tests compare against).
//!
//! All operations follow POSIX return conventions: a non-negative result
//! is the operation's value, a negative result is a negated errno (the
//! constants in core/IO.tlk).
//!
//! CaptureIO simulates descriptors in memory: files and sockets are byte
//! buffers where writes append and reads advance a cursor — so a test
//! that writes to a connection can read the same bytes back. That
//! loopback is how server slices are scripted without touching the host.

use std::collections::{HashMap, VecDeque};
use std::io::Write;

pub trait IO {
    /// POSIX-shaped write: bytes to a file descriptor, returning the byte
    /// count or a negative errno.
    fn write(&mut self, fd: i64, bytes: &[u8]) -> i64;

    /// Sleep for `ms` milliseconds, returning 0. Only the host-backed IO
    /// sleeps for real; tests must stay fast.
    fn sleep(&mut self, ms: i64) -> i64;

    /// Read into `buf`: bytes read (0 = end of stream) or negative errno.
    fn read(&mut self, fd: i64, buf: &mut [u8]) -> i64;

    /// Open a path (bytes, no NUL): fd or negative errno.
    fn open(&mut self, path: &[u8], flags: i64, mode: i64) -> i64;

    /// Close a descriptor: 0 or negative errno.
    fn close(&mut self, fd: i64) -> i64;

    /// Device control: operation-specific value or negative errno.
    fn ctl(&mut self, fd: i64, op: i64, arg: i64) -> i64;

    /// Poll `(fd, events, revents)` records, filling `revents`: the ready
    /// count or negative errno.
    fn poll(&mut self, fds: &mut [(i32, i16, i16)], timeout: i64) -> i64;

    /// Create a socket: fd or negative errno.
    fn socket(&mut self, domain: i64, socktype: i64, protocol: i64) -> i64;

    /// Bind to an IPv4 address and port: 0 or negative errno.
    fn bind(&mut self, fd: i64, addr: i64, port: i64) -> i64;

    /// Mark a socket listening: 0 or negative errno.
    fn listen(&mut self, fd: i64, backlog: i64) -> i64;

    /// Connect to an IPv4 address and port: 0 or negative errno.
    fn connect(&mut self, fd: i64, addr: i64, port: i64) -> i64;

    /// Accept a connection: the new fd or negative errno.
    fn accept(&mut self, fd: i64) -> i64;
}

const EIO: i64 = -5;
const EBADF: i64 = -9;
const EINVAL: i64 = -22;
#[cfg(not(unix))]
const EPERM: i64 = -1;

/// Host stdio and POSIX syscalls (fd 1 = stdout, fd 2 = stderr; other
/// descriptors go straight to the OS).
#[derive(Default)]
pub struct StdioIO;

#[cfg(unix)]
fn errno() -> i64 {
    -(std::io::Error::last_os_error().raw_os_error().unwrap_or(5) as i64)
}

impl IO for StdioIO {
    fn write(&mut self, fd: i64, bytes: &[u8]) -> i64 {
        match fd {
            1 => match std::io::stdout()
                .write_all(bytes)
                .and_then(|()| std::io::stdout().flush())
            {
                Ok(()) => bytes.len() as i64,
                Err(_) => EIO,
            },
            2 => match std::io::stderr().write_all(bytes) {
                Ok(()) => bytes.len() as i64,
                Err(_) => EIO,
            },
            _ => {
                #[cfg(unix)]
                {
                    let n =
                        unsafe { libc::write(fd as i32, bytes.as_ptr() as *const _, bytes.len()) };
                    if n < 0 { errno() } else { n as i64 }
                }
                #[cfg(not(unix))]
                {
                    EBADF
                }
            }
        }
    }

    fn sleep(&mut self, ms: i64) -> i64 {
        if ms > 0 {
            std::thread::sleep(std::time::Duration::from_millis(ms as u64));
        }
        0
    }

    fn read(&mut self, fd: i64, buf: &mut [u8]) -> i64 {
        #[cfg(unix)]
        {
            let n = unsafe { libc::read(fd as i32, buf.as_mut_ptr() as *mut _, buf.len()) };
            if n < 0 { errno() } else { n as i64 }
        }
        #[cfg(not(unix))]
        {
            let _ = (fd, buf);
            EPERM
        }
    }

    fn open(&mut self, path: &[u8], flags: i64, mode: i64) -> i64 {
        #[cfg(unix)]
        {
            let Ok(path) = std::ffi::CString::new(path) else {
                return EINVAL;
            };
            let fd = unsafe { libc::open(path.as_ptr(), flags as i32, mode as libc::mode_t) };
            if fd < 0 { errno() } else { fd as i64 }
        }
        #[cfg(not(unix))]
        {
            let _ = (path, flags, mode);
            EPERM
        }
    }

    fn close(&mut self, fd: i64) -> i64 {
        #[cfg(unix)]
        {
            let result = unsafe { libc::close(fd as i32) };
            if result < 0 { errno() } else { 0 }
        }
        #[cfg(not(unix))]
        {
            let _ = fd;
            EPERM
        }
    }

    fn ctl(&mut self, fd: i64, op: i64, arg: i64) -> i64 {
        #[cfg(unix)]
        {
            let result = unsafe { libc::ioctl(fd as i32, op as _, arg) };
            if result < 0 { errno() } else { result as i64 }
        }
        #[cfg(not(unix))]
        {
            let _ = (fd, op, arg);
            EPERM
        }
    }

    fn poll(&mut self, fds: &mut [(i32, i16, i16)], timeout: i64) -> i64 {
        #[cfg(unix)]
        {
            let mut pollfds: Vec<libc::pollfd> = fds
                .iter()
                .map(|&(fd, events, _)| libc::pollfd {
                    fd,
                    events,
                    revents: 0,
                })
                .collect();
            let result = unsafe {
                libc::poll(
                    pollfds.as_mut_ptr(),
                    pollfds.len() as libc::nfds_t,
                    timeout as i32,
                )
            };
            for (record, pollfd) in fds.iter_mut().zip(&pollfds) {
                record.2 = pollfd.revents;
            }
            if result < 0 { errno() } else { result as i64 }
        }
        #[cfg(not(unix))]
        {
            let _ = (fds, timeout);
            EPERM
        }
    }

    fn socket(&mut self, domain: i64, socktype: i64, protocol: i64) -> i64 {
        #[cfg(unix)]
        {
            let fd = unsafe { libc::socket(domain as i32, socktype as i32, protocol as i32) };
            if fd < 0 { errno() } else { fd as i64 }
        }
        #[cfg(not(unix))]
        {
            let _ = (domain, socktype, protocol);
            EPERM
        }
    }

    fn bind(&mut self, fd: i64, addr: i64, port: i64) -> i64 {
        #[cfg(unix)]
        {
            // SO_REUSEADDR first: restarting a server must not wait out
            // TIME_WAIT (the previous backend's behavior).
            let optval: i32 = 1;
            unsafe {
                libc::setsockopt(
                    fd as i32,
                    libc::SOL_SOCKET,
                    libc::SO_REUSEADDR,
                    &optval as *const i32 as *const _,
                    std::mem::size_of::<i32>() as libc::socklen_t,
                );
            }
            let sockaddr = sockaddr_in(addr, port);
            let result = unsafe {
                libc::bind(
                    fd as i32,
                    &sockaddr as *const libc::sockaddr_in as *const libc::sockaddr,
                    std::mem::size_of::<libc::sockaddr_in>() as libc::socklen_t,
                )
            };
            if result < 0 { errno() } else { 0 }
        }
        #[cfg(not(unix))]
        {
            let _ = (fd, addr, port);
            EPERM
        }
    }

    fn listen(&mut self, fd: i64, backlog: i64) -> i64 {
        #[cfg(unix)]
        {
            let result = unsafe { libc::listen(fd as i32, backlog as i32) };
            if result < 0 { errno() } else { 0 }
        }
        #[cfg(not(unix))]
        {
            let _ = (fd, backlog);
            EPERM
        }
    }

    fn connect(&mut self, fd: i64, addr: i64, port: i64) -> i64 {
        #[cfg(unix)]
        {
            let sockaddr = sockaddr_in(addr, port);
            let result = unsafe {
                libc::connect(
                    fd as i32,
                    &sockaddr as *const libc::sockaddr_in as *const libc::sockaddr,
                    std::mem::size_of::<libc::sockaddr_in>() as libc::socklen_t,
                )
            };
            if result < 0 { errno() } else { 0 }
        }
        #[cfg(not(unix))]
        {
            let _ = (fd, addr, port);
            EPERM
        }
    }

    fn accept(&mut self, fd: i64) -> i64 {
        #[cfg(unix)]
        {
            let result =
                unsafe { libc::accept(fd as i32, std::ptr::null_mut(), std::ptr::null_mut()) };
            if result < 0 { errno() } else { result as i64 }
        }
        #[cfg(not(unix))]
        {
            let _ = fd;
            EPERM
        }
    }
}

#[cfg(unix)]
fn sockaddr_in(addr: i64, port: i64) -> libc::sockaddr_in {
    let mut sockaddr: libc::sockaddr_in = unsafe { std::mem::zeroed() };
    sockaddr.sin_family = libc::AF_INET as libc::sa_family_t;
    sockaddr.sin_port = (port as u16).to_be();
    sockaddr.sin_addr.s_addr = (addr as u32).to_be();
    sockaddr
}

/// Captures writes for tests and the REPL; everything else is simulated
/// in memory. Descriptors above 2 are byte buffers: writes append, reads
/// advance a cursor — files and sockets alike (the loopback the scripted
/// server tests rely on). Sleeping is a no-op.
#[derive(Default)]
pub struct CaptureIO {
    pub out: Vec<u8>,
    pub err: Vec<u8>,
    /// Scripted standard input (fd 0 reads drain it).
    pub stdin: VecDeque<u8>,
    files: HashMap<i64, Vec<u8>>,
    cursors: HashMap<i64, usize>,
    next_fd: i64,
}

impl CaptureIO {
    /// Mint a simulated descriptor (open/socket/accept all share it).
    fn fresh_fd(&mut self) -> i64 {
        let fd = self.next_fd + 3; // after stdin/stdout/stderr
        self.next_fd += 1;
        self.files.insert(fd, Vec::new());
        self.cursors.insert(fd, 0);
        fd
    }
}

impl IO for CaptureIO {
    fn write(&mut self, fd: i64, bytes: &[u8]) -> i64 {
        match fd {
            1 => self.out.extend_from_slice(bytes),
            2 => self.err.extend_from_slice(bytes),
            _ => match self.files.get_mut(&fd) {
                Some(buffer) => buffer.extend_from_slice(bytes),
                None => return EBADF,
            },
        }
        bytes.len() as i64
    }

    fn sleep(&mut self, _ms: i64) -> i64 {
        0
    }

    fn read(&mut self, fd: i64, buf: &mut [u8]) -> i64 {
        if fd == 0 {
            let count = buf.len().min(self.stdin.len());
            for slot in buf.iter_mut().take(count) {
                *slot = self.stdin.pop_front().unwrap_or(0);
            }
            return count as i64;
        }
        let Some(buffer) = self.files.get(&fd) else {
            return EBADF;
        };
        let cursor = self.cursors.get(&fd).copied().unwrap_or(0);
        let remaining = &buffer[cursor.min(buffer.len())..];
        let count = buf.len().min(remaining.len());
        buf[..count].copy_from_slice(&remaining[..count]);
        self.cursors.insert(fd, cursor + count);
        count as i64
    }

    fn open(&mut self, _path: &[u8], _flags: i64, _mode: i64) -> i64 {
        self.fresh_fd()
    }

    fn close(&mut self, fd: i64) -> i64 {
        if self.files.remove(&fd).is_some() {
            self.cursors.remove(&fd);
            0
        } else {
            EBADF
        }
    }

    fn ctl(&mut self, _fd: i64, _op: i64, _arg: i64) -> i64 {
        EINVAL
    }

    fn poll(&mut self, fds: &mut [(i32, i16, i16)], _timeout: i64) -> i64 {
        // Simulated descriptors are always ready for what was asked.
        let mut ready = 0;
        for (fd, events, revents) in fds.iter_mut() {
            if self.files.contains_key(&(*fd as i64)) {
                *revents = *events;
                ready += 1;
            } else {
                *revents = 0;
            }
        }
        ready
    }

    fn socket(&mut self, _domain: i64, _socktype: i64, _protocol: i64) -> i64 {
        self.fresh_fd()
    }

    fn bind(&mut self, _fd: i64, _addr: i64, _port: i64) -> i64 {
        0
    }

    fn listen(&mut self, _fd: i64, _backlog: i64) -> i64 {
        0
    }

    fn connect(&mut self, _fd: i64, _addr: i64, _port: i64) -> i64 {
        0
    }

    fn accept(&mut self, fd: i64) -> i64 {
        if !self.files.contains_key(&fd) {
            return EBADF;
        }
        self.fresh_fd()
    }
}
