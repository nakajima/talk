//! LLVM code generation for Talk's backend IR.
//!
//! This crate owns target lowering and the native runtime bridge. It consumes
//! the public code-generation model produced by the Talk compiler.

mod emit;

use std::fmt;
use std::hash::Hash;

pub use talk::codegen::{
    BlockData, CmpKind, Constant, DisplayNames, Function, Inst, MemTy, Operand, Program, ScalarOp,
    Term, TypeKind,
};

pub struct Runtime<'a, S> {
    pub native_prelude: &'a str,
    pub display_names: DisplayNames<S>,
    pub string_symbol: S,
    pub storage_symbol: S,
}

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

pub fn emit<S>(program: &Program<S>, runtime: Runtime<'_, S>) -> Result<Artifact, Error>
where
    S: Copy + Eq + Hash,
{
    emit::emit(program, runtime)
}
