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

/// A library-mode emission (ADR 0048): IR and runtime C with every
/// cross-translation-unit symbol namespaced under the caller's prefix,
/// no `main`, plus the matching C header and export-name-to-symbol
/// manifest. The convention is the shared boundary in
/// `talk_native_runtime::library`.
#[derive(Debug)]
pub struct LibraryArtifact {
    pub ir: String,
    pub runtime_c: String,
    pub header: String,
    pub manifest: String,
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

/// Emit a library artifact for a finalized MIR module: one externally
/// visible wrapper per `Module.exports` entry under `prefix`, namespaced
/// lifecycle entry points, and contained traps (ADR 0048).
pub fn emit_library(
    module: &talk_mir::Module,
    prefix: &str,
) -> Result<LibraryArtifact, Error> {
    emit::emit_library(module, prefix)
}
