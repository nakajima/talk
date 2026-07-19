//! The bytecode backend: one deep interface over private phases (ADR 0034).
//!
//! ```text
//! compile(typed programs, entry) -> runtime module or diagnostics
//! execute(module, host IO)       -> rendered result or runtime failure
//! ```
//!
//! MIR construction, ownership checking, and bytecode lowering are private
//! stages of `compile`. In-memory modules from this compiler run as
//! constructed; modules loaded from bytes validate first (the JVM's
//! placement of bytecode verification — Leroy 2003, "Java Bytecode
//! Verification: Algorithms and Formalizations").

mod inline;
mod lower;
mod mir;
mod regalloc;

pub(crate) use mir::{Entry, ProgramInput};

use crate::parsing::span::Span;
use talk_runtime::interp::{ValueNames, run_displayed_counted};

/// A compiled program: the runtime module plus the display metadata that
/// renders results Talk-style (enum case names, struct fields).
pub struct Executable {
    pub(crate) module: talk_runtime::Module,
    pub(crate) names: ValueNames,
}

impl Executable {
    /// Serialize the executable module (TOOL-13). Display metadata is not
    /// part of the wire format; an image renders values with symbols only.
    pub fn encode_bytecode(&self) -> Result<Vec<u8>, talk_runtime::bytecode::EncodeError> {
        self.module.encode_bytecode()
    }

    /// Render the target bytecode for inspection (TOOL-12).
    pub fn render_bytecode(&self) -> String {
        self.module.render()
    }
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

/// Compile the reachable source graph as one unit. `programs[0]` is the
/// user's program; the rest supply dependency bodies (core, stdlib).
pub(crate) fn compile(
    programs: &[ProgramInput<'_>],
    aliases: rustc_hash::FxHashMap<u16, u16>,
    entry: Entry,
) -> Result<Executable, BackendError> {
    let _alias_scope = mir::module_alias_scope(aliases);
    let mut program = mir::build(programs, entry)?;
    inline::inline_small(&mut program);
    for function in &mut program.functions {
        regalloc::reuse_locals(function);
    }
    let module = lower::lower(&program)?;
    Ok(Executable {
        module,
        names: display_names(programs),
    })
}

/// Run the ownership analysis without lowering or executing: `talk
/// check`'s second half (wave F of docs/ownership-rethink-plan.md).
/// Everything `compile` would reject at the MIR stage — ownership,
/// exclusivity, the unsafe gate — reports here.
pub(crate) fn check(
    programs: &[ProgramInput<'_>],
    aliases: rustc_hash::FxHashMap<u16, u16>,
    entry: Entry,
) -> Result<(), BackendError> {
    let _alias_scope = mir::module_alias_scope(aliases);
    mir::build(programs, entry).map(|_| ())
}

/// Render the middle representation for inspection (TOOL-10).
pub(crate) fn render_mir(
    programs: &[ProgramInput<'_>],
    aliases: rustc_hash::FxHashMap<u16, u16>,
    entry: Entry,
) -> Result<String, BackendError> {
    let _alias_scope = mir::module_alias_scope(aliases);
    let program = mir::build(programs, entry)?;
    Ok(program.render())
}

/// Rendering metadata from the compiled programs' catalogs: the runtime
/// itself only carries symbols.
fn display_names(programs: &[ProgramInput<'_>]) -> ValueNames {
    let mut names = ValueNames::default();
    for input in programs {
        let types = input.program.types();
        let resolved = input.program.resolved_names();
        for (symbol, def) in &types.catalog.enums {
            let runtime = lower::runtime_symbol(mir::canonical(*symbol, input.module));
            if let Some(name) = resolved.symbol_names.get(symbol) {
                names.types.insert(runtime, name.clone());
            }
            names
                .cases
                .insert(runtime, def.variants.keys().cloned().collect());
        }
        for (symbol, def) in &types.catalog.structs {
            let runtime = lower::runtime_symbol(mir::canonical(*symbol, input.module));
            if let Some(name) = resolved.symbol_names.get(symbol) {
                names.types.insert(runtime, name.clone());
            }
            names
                .fields
                .insert(runtime, def.fields.keys().cloned().collect());
        }
    }
    names.string_struct = Some(lower::runtime_symbol(
        crate::name_resolution::symbol::Symbol::String,
    ));
    names
}

/// Execute a compiled module and return its Talk-rendered result (`None`
/// for Unit). Every run is counted: a nonzero allocation or object balance
/// at exit is a failure, not a warning.
pub(crate) fn execute(
    executable: &Executable,
    io: &mut dyn talk_runtime::io::IO,
) -> Result<Option<String>, String> {
    if std::env::var_os("TALK_BACKEND_DEBUG").is_some() {
        eprintln!("{}", executable.module.render());
    }
    let (value, rendered, balance) =
        run_displayed_counted(&executable.module, io, &executable.names)?;
    // The result value's own footprint is alive at exit by definition;
    // anything beyond it leaked.
    if balance.result_exact
        && (balance.live_allocations != balance.result_allocations
            || balance.live_objects != balance.result_objects)
    {
        return Err(format!(
            "resource leak: {} live allocations, {} live 'heap objects at exit (result owns {}, {})",
            balance.live_allocations,
            balance.live_objects,
            balance.result_allocations,
            balance.result_objects
        ));
    }
    Ok(match value {
        talk_runtime::interp::Value::Void => None,
        _ => Some(rendered),
    })
}
