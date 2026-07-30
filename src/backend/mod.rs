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

mod checked_indexed_load;
mod lower;
mod optimize;

/// The compiler-to-runtime symbol mapping, for the frontend result
/// bridge (ADR 0043 §5): the identities in a returned value graph are
/// runtime symbols.
pub(crate) use lower::runtime_symbol;
mod mir;
mod regalloc;

pub(crate) use mir::{Entry, ProgramInput};

use crate::parsing::span::Span;
use talk_runtime::interp::{StringShape, ValueNames, run_displayed_counted};

pub use talk_runtime::VmStats;
pub use talk_runtime::interp::{Budgets, HostValue, RunOutcome};

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

/// Compiler and VM statistics for one executable.
#[derive(Debug)]
pub struct ExecutableStats {
    pub optimizations: OptimizationStats,
    pub vm: VmStats,
}

impl ExecutableStats {
    pub fn render(&self) -> String {
        use std::fmt::Write as _;

        let mut out = String::new();
        let _ = writeln!(out, "Optimization statistics");
        let _ = writeln!(out, "  {:<28} {:>12}", "pass", "applied");
        for pass in &self.optimizations.passes {
            let _ = writeln!(out, "  {:<28} {:>12}", pass.name, pass.applied);
        }
        let total: u64 = self
            .optimizations
            .passes
            .iter()
            .map(|pass| pass.applied)
            .sum();
        let _ = writeln!(out, "  {:<28} {:>12}", "total", total);
        let _ = writeln!(out);
        out.push_str(&self.vm.render());
        out
    }
}

/// A compiled program: the runtime module plus the display metadata that
/// renders results Talk-style (enum case names, struct fields).
pub struct Executable {
    pub(crate) module: talk_runtime::Module,
    pub(crate) names: ValueNames,
    pub(crate) optimizations: OptimizationStats,
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

    /// Optimization counts recorded while compiling this executable.
    pub fn optimization_stats(&self) -> &OptimizationStats {
        &self.optimizations
    }

    /// Create a statistics collector for this executable. Optimization
    /// counts are fixed at compilation; VM counts accumulate across runs.
    pub fn stats(&self) -> ExecutableStats {
        ExecutableStats {
            optimizations: self.optimizations.clone(),
            vm: VmStats::for_module(&self.module),
        }
    }

    /// Call an exported service function on a fresh machine (ADR 0043
    /// call ABI). Only executables from `compile_service` have exports.
    pub fn run_export<'io>(
        &self,
        name: &str,
        args: &[HostValue],
        budgets: Budgets,
        io: &'io mut dyn talk_runtime::io::IO,
    ) -> Result<RunOutcome<'io>, String> {
        talk_runtime::interp::run_export(&self.module, name, args, string_shape(), budgets, io)
    }

    /// Run an export while collecting exact VM instruction counts.
    pub fn run_export_with_stats<'io>(
        &self,
        name: &str,
        args: &[HostValue],
        budgets: Budgets,
        io: &'io mut dyn talk_runtime::io::IO,
        stats: &mut ExecutableStats,
    ) -> Result<RunOutcome<'io>, String> {
        if stats.optimizations != self.optimizations {
            return Err("statistics collector belongs to a different executable".into());
        }
        talk_runtime::interp::run_export_with_stats(
            &self.module,
            name,
            args,
            string_shape(),
            budgets,
            io,
            &mut stats.vm,
        )
    }
}

/// The core String layout's record symbols, for fabricating host string
/// arguments (layout owned by core/String.tlk; parity tests pin it).
pub(crate) fn string_shape() -> StringShape {
    StringShape {
        string: lower::runtime_symbol(crate::name_resolution::symbol::Symbol::String),
        storage: lower::runtime_symbol(crate::name_resolution::symbol::Symbol::Storage),
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
    entry: Entry,
) -> Result<Executable, BackendError> {
    crate::profile::init();
    profiling::scope!("backend.compile");
    let mut program = {
        profiling::scope!("backend.mir_build");
        mir::build(programs, entry, false)?
    };
    let mut optimizations = {
        profiling::scope!("backend.optimize");
        optimize::run(&mut program)
    };
    {
        profiling::scope!("backend.regalloc");
        for function in &mut program.functions {
            regalloc::reuse_locals(function);
        }
    }
    let mut module = {
        profiling::scope!("backend.lower");
        lower::lower(&program)?
    };
    let checked_indexed_loads = checked_indexed_load::run(&mut module);
    optimizations.passes.push(OptimizationPassStats {
        name: "checked_indexed_load",
        applied: checked_indexed_loads,
    });
    Ok(Executable {
        module,
        names: display_names(programs),
        optimizations,
    })
}

/// Run the ownership analysis without lowering or executing: `talk
/// check`'s second half (wave F of docs/ownership.md).
/// Everything `compile` would reject at the MIR stage — ownership,
/// exclusivity, the unsafe gate — reports here.
pub(crate) fn check(programs: &[ProgramInput<'_>], entry: Entry) -> Result<(), BackendError> {
    // Checking means checking everything: every body compiles, called
    // or not, entry or no entry.
    mir::build(programs, entry, true).map(|_| ())
}

/// Render the middle representation for inspection (TOOL-10).
pub(crate) fn render_mir(
    programs: &[ProgramInput<'_>],
    entry: Entry,
) -> Result<String, BackendError> {
    let program = mir::build(programs, entry, false)?;
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
            let runtime = lower::runtime_symbol(*symbol);
            if let Some(name) = resolved.symbol_names.get(symbol) {
                names.types.insert(runtime, name.clone());
            }
            names
                .cases
                .insert(runtime, def.variants.keys().cloned().collect());
        }
        for (symbol, def) in &types.catalog.structs {
            let runtime = lower::runtime_symbol(*symbol);
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
    crate::profile::init();
    profiling::scope!("backend.execute");
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
