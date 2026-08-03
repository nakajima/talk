//! MIR-to-VM-bytecode adapter (ADR 0047). Consumes the public finalized
//! MIR module and owns lowering, target pools, block linearization,
//! checked-load fusion, and the compiled executable wrapper. Depends on
//! `talk-mir` and `talk-vm` only; the compiler drives it through
//! `compile_mir` plus `compile`.

mod checked_indexed_load;
mod lower;

use talk_vm::interp::{Budgets, HostValue, RunOutcome, ValueNames, run_displayed_counted};

/// A bytecode-adapter rejection: malformed public MIR supplied manually,
/// or a target-internal invariant failure. Adapter errors carry no
/// parser spans; the compiler locates source errors before publishing
/// MIR.
#[derive(Debug)]
pub struct Error {
    message: String,
}

impl Error {
    fn new(message: String) -> Self {
        Self { message }
    }

    pub fn message(&self) -> &str {
        &self.message
    }
}

impl std::fmt::Display for Error {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter.write_str(&self.message)
    }
}

impl std::error::Error for Error {}

/// Counts recorded by the adapter itself (as distinct from the
/// compiler's optimization counts and the VM's execution counts).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct AdapterStats {
    pub checked_indexed_loads: u64,
}

/// A compiled program: the runtime module plus the display metadata that
/// renders results Talk-style (enum case names, struct fields).
pub struct Executable {
    module: talk_vm::Module,
    names: ValueNames,
    adapter: AdapterStats,
    string_symbol: talk_vm::symbol::Symbol,
}

/// Lower a finalized MIR module to a validated VM module, fusing
/// checked indexed loads on the way.
pub fn compile(program: &talk_mir::Module) -> Result<Executable, Error> {
    let mut module = lower::lower(program)?;
    let checked_indexed_loads = checked_indexed_load::run(&mut module);
    let string_symbol = vm_symbol(program.string_symbol);
    Ok(Executable {
        names: value_names(program),
        module,
        adapter: AdapterStats {
            checked_indexed_loads,
        },
        string_symbol,
    })
}

impl Executable {
    /// Wrap an already-decoded VM module (the procedural macro host's
    /// artifact path). Display names default to structural rendering;
    /// the String symbol for host string arguments comes from the
    /// caller's well-known identity mapping.
    pub fn from_vm_module(module: talk_vm::Module, string_symbol: talk_vm::symbol::Symbol) -> Self {
        Self {
            module,
            names: ValueNames::default(),
            adapter: AdapterStats::default(),
            string_symbol,
        }
    }

    /// Serialize the executable module (TOOL-13). Display metadata is not
    /// part of the wire format; an image renders values with symbols only.
    pub fn encode_bytecode(&self) -> Result<Vec<u8>, talk_vm::bytecode::EncodeError> {
        self.module.encode_bytecode()
    }

    /// Render the target bytecode for inspection (TOOL-12).
    pub fn render_bytecode(&self) -> String {
        self.module.render()
    }

    /// The adapter's own counts for this executable.
    pub fn adapter_stats(&self) -> AdapterStats {
        self.adapter
    }

    /// A VM statistics collector for this executable; counts accumulate
    /// across runs.
    pub fn vm_stats(&self) -> talk_vm::VmStats {
        talk_vm::VmStats::for_module(&self.module)
    }

    /// Execute the module and return its Talk-rendered result (`None`
    /// for Unit). Every run is counted: a nonzero allocation or object
    /// balance at exit is a failure, not a warning.
    pub fn run(&self, io: &mut dyn talk_vm::io::IO) -> Result<Option<String>, String> {
        if std::env::var_os("TALK_BACKEND_DEBUG").is_some() {
            eprintln!("{}", self.module.render());
        }
        let (value, rendered, balance) = run_displayed_counted(&self.module, io, &self.names)?;
        // The result value's own footprint is alive at exit by
        // definition; anything beyond it leaked.
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
            talk_vm::interp::Value::Void => None,
            _ => Some(rendered),
        })
    }

    /// Call an exported service function on a fresh machine (ADR 0043
    /// call ABI). Only service executables have exports.
    pub fn run_export<'io>(
        &self,
        name: &str,
        args: &[HostValue],
        budgets: Budgets,
        io: &'io mut dyn talk_vm::io::IO,
    ) -> Result<RunOutcome<'io>, String> {
        talk_vm::interp::run_export(&self.module, name, args, self.string_shape(), budgets, io)
    }

    /// Run an export while collecting exact VM instruction counts.
    pub fn run_export_with_stats<'io>(
        &self,
        name: &str,
        args: &[HostValue],
        budgets: Budgets,
        io: &'io mut dyn talk_vm::io::IO,
        stats: &mut talk_vm::VmStats,
    ) -> Result<RunOutcome<'io>, String> {
        talk_vm::interp::run_export_with_stats(
            &self.module,
            name,
            args,
            self.string_shape(),
            budgets,
            io,
            stats,
        )
    }

    /// The core String record symbol, for fabricating host string
    /// arguments (layout owned by core/String.tlk; parity tests pin it).
    fn string_shape(&self) -> talk_vm::symbol::Symbol {
        self.string_symbol
    }
}

/// Validate and execute a serialized bytecode image (TOOL-14). Images are
/// untrusted bytes: decoding validates every index, register, and opcode
/// before execution (ADR 0034's trust seam).
pub fn run_image(bytes: &[u8], io: &mut dyn talk_vm::io::IO) -> Result<Option<String>, String> {
    let module = talk_vm::Module::decode_bytecode(bytes)
        .map_err(|error| format!("invalid bytecode image: {error}"))?;
    Executable::from_vm_module(module, talk_vm::symbol::Symbol::Library).run(io)
}

/// The runtime display names implied by the module's published display
/// metadata: the runtime itself only carries symbols.
fn value_names(program: &talk_mir::Module) -> ValueNames {
    let mut names = ValueNames::default();
    for (symbol, entry) in &program.display.entries {
        let runtime = vm_symbol(*symbol);
        names.types.insert(runtime, entry.name.clone());
        match entry.kind {
            talk_mir::TypeKind::Enum => {
                names.cases.insert(runtime, entry.members.clone());
            }
            _ => {
                names.fields.insert(runtime, entry.members.clone());
            }
        }
    }
    names.string_struct = Some(vm_symbol(program.string_symbol));
    names
}

/// Aggregate identities carried by the layout table map structurally to
/// the runtime's own symbol type; anything else folds to the library
/// fallback.
pub fn vm_symbol(symbol: talk_mir::MirSymbol) -> talk_vm::symbol::Symbol {
    use talk_mir::MirSymbolKind as K;
    use talk_vm::symbol::{ModuleId, ModuleSymbolId, Symbol as R};
    let id = ModuleSymbolId::new(ModuleId(symbol.module), symbol.local);
    match symbol.kind {
        K::Struct => R::Struct(id),
        K::Enum => R::Enum(id),
        _ => R::Library,
    }
}
