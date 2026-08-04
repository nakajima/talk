//! The compiler's backend: MIR construction, ownership checking,
//! optimization, register allocation, and frame shaping — everything up
//! to the public finalized module (ADR 0047). Target adapters live in
//! their own crates: `talk-bytecode` lowers the module to VM bytecode,
//! and the `talk-c` and `talk-llvm` emitters consume it directly.

mod optimize;

/// The compiler-to-runtime symbol mapping, for the frontend result
/// bridge (ADR 0043 §5): the identities in a returned value graph are
/// runtime symbols.

/// Source-symbol-to-runtime-symbol mapping for host bridges: executable
/// identities map structurally; anything else folds to the library
/// fallback.
pub(crate) fn runtime_symbol(
    symbol: crate::name_resolution::symbol::Symbol,
) -> talk_vm::symbol::Symbol {
    match build::from_source(symbol) {
        Some(mir) => talk_bytecode::vm_symbol(mir),
        None => talk_vm::symbol::Symbol::Library,
    }
}
mod build;
mod regalloc;

pub(crate) use build::{Entry, ProgramInput};

use crate::parsing::span::Span;

/// The number of concrete rewrites performed by one optimization pass.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct OptimizationPassStats {
    pub name: &'static str,
    pub applied: u64,
}

/// Optimization counts accumulated while compiling one executable.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct OptimizationStats {
    pub passes: Vec<OptimizationPassStats>,
}

/// The core String record symbol, for fabricating host string
/// arguments (layout owned by core/String.tlk; parity tests pin it).
pub(crate) fn string_shape() -> talk_vm::symbol::Symbol {
    runtime_symbol(crate::name_resolution::symbol::Symbol::String)
}

/// A backend rejection: either a source construct no wave supports yet, or
/// an internal invariant failure.
#[derive(Debug)]
pub(crate) struct BackendError {
    pub message: String,
    pub span: Span,
}

impl BackendError {
    pub(crate) fn new(message: String, span: Span) -> Self {
        Self { message, span }
    }

    /// A deliberate fail-closed rejection of source the backend does not
    /// execute yet. The message always says "not supported yet".
    pub(crate) fn unsupported(message: String, span: Span) -> Self {
        debug_assert!(message.contains("not supported yet"));
        Self { message, span }
    }
}

/// Run the ownership analysis without lowering or executing: `talk
/// check`'s second half (wave F of docs/ownership.md).
/// Everything `compile` would reject at the MIR stage — ownership,
/// exclusivity, the unsafe gate — reports here.
pub(crate) fn check(programs: &[ProgramInput<'_>], entry: Entry) -> Result<(), BackendError> {
    // Checking means checking everything: every body compiles, called
    // or not, entry or no entry.
    build::build(programs, entry, true).map(|_| ())
}

/// The one finalized producer every target shares (ADR 0047): build and
/// ownership-check, optimize, pre-allocation escape summaries, register
/// allocation, and post-allocation frame stamping. The bytecode adapter
/// ignores the frame facts; stamping them uniformly is what lets C
/// consume the same module without a compiler-private prepass.
pub(crate) fn compile_mir(
    programs: &[ProgramInput<'_>],
    entry: Entry,
) -> Result<(build::Program, OptimizationStats), BackendError> {
    let mut program = build::build(programs, entry, false)?;
    let optimizations = finalize(&mut program);
    Ok((program, optimizations))
}

fn finalize(program: &mut build::Program) -> OptimizationStats {
    let optimizations = optimize::run(program);
    // Parameter escape summaries must read the pre-allocation program,
    // where a parameter's slot is still only ever the parameter; the
    // shaping itself runs on the final numbering (ADR 0045).
    let summaries = build::escape::parameter_summaries(program);
    allocate_registers(program);
    build::escape::shape_frames(program, &summaries);
    optimizations
}

/// Register allocation over the whole program. Layout classes are
/// program-wide facts (they read every function's return repr), so they
/// derive here once and publish on each function's locals table under
/// the final numbering.
fn allocate_registers(program: &mut build::Program) {
    let returns: Vec<Option<build::layout::LayoutId>> = program
        .functions
        .iter()
        .map(|function| function.return_repr)
        .collect();
    for function in &mut program.functions {
        regalloc::reuse_locals(function, &program.layout_table, &returns);
    }
}

/// Render the middle representation for inspection (TOOL-10).
pub(crate) fn render_mir(
    programs: &[ProgramInput<'_>],
    entry: Entry,
    optimized: bool,
) -> Result<String, BackendError> {
    let mut program = build::build(programs, entry, false)?;
    if optimized {
        finalize(&mut program);
    }
    Ok(program.render())
}
