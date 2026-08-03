//! The shared native C runtime source consumed by both native backends
//! (ADR 0047): the C emitter prepends it to generated programs, and the
//! LLVM backend links it against emitted IR. One tracked copy; neither
//! backend depends on the other to obtain it.

/// The complete native runtime as C source.
pub const fn source() -> &'static str {
    include_str!("runtime.c")
}
