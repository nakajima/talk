//! LLVM code generation for Talk's backend IR.
//!
//! This crate owns target lowering and the native runtime bridge. It consumes
//! the public finalized MIR module published by the Talk compiler (ADR 0047).

mod emit;

use std::fmt;

#[derive(Debug)]
pub struct Artifact {
    pub ir: String,
    pub runtime_c: String,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Error {
    message: String,
}

impl Error {
    pub fn new(message: impl Into<String>) -> Self {
        Self {
            message: message.into(),
        }
    }

    pub fn message(&self) -> &str {
        &self.message
    }
}

impl fmt::Display for Error {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(&self.message)
    }
}

impl std::error::Error for Error {}

/// Emit LLVM IR and the runtime C source for a finalized MIR module. The
/// module carries every fact the emitter reads: functions, layouts,
/// display metadata, and the well-known String and Storage identities.
pub fn emit(module: &talk_mir::Module) -> Result<Artifact, Error> {
    emit::emit(module)
}
