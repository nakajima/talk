//! The frame-stack register interpreter. Frames are plain data (so M9
//! continuation capture can copy them — Hieb, Dybvig & Bruggeman, PLDI
//! 1990); cells live in a slot arena outside the frames (assignment
//! conversion put them there — Kranz et al., ORBIT, 1986). Dispatch is a
//! plain `match` over the decoded instruction (Ertl & Gregg, JILP 2003).

use crate::CmpOp;

// Worker threads: native `std::thread`, or Web-Worker-backed threads on
// wasm32 with shared-memory atomics (`wasm_thread` mirrors the std API;
// each spawn is a Worker over the same module and shared memory).
// Without atomics wasm has no threads at all — the spawn-site inline
// paths below are the whole story there.
#[cfg(not(target_arch = "wasm32"))]
use std::thread;
#[cfg(all(target_arch = "wasm32", target_feature = "atomics"))]
use wasm_thread as thread;
use crate::VmStats;
use crate::io::IO;
use crate::memory::{Allocations, MemoryError, Pointer};
use crate::objects::{ObjectError, Objects};
use crate::symbol::Symbol;
use crate::{Chunk, Constant, FieldShape, Insn, LayoutBody, LayoutDesc, MemKind, Module};
use rustc_hash::FxHashMap;
use std::rc::Rc;

/// Whether `TALK_TRACE_MEM` is set, read once: the check guards the
/// interpreter's hottest paths, and a per-instruction `getenv` costs
/// more than the instruction itself.
fn trace_mem() -> bool {
    static TRACE: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *TRACE.get_or_init(|| std::env::var_os("TALK_TRACE_MEM").is_some())
}

#[derive(Clone, Debug, PartialEq)]
pub enum Value {
    I64(i64),
    F64(f64),
    Bool(bool),
    Byte(u8),
    Void,
    /// An address and allocation identity in the VM's byte memory.
    Ptr(Pointer),
    /// An aggregate — struct, tuple, record, or enum variant — in the
    /// one flat representation (ADR 0045): its published layout id and
    /// its slot vector, nested inline children spliced in place, a sum's
    /// tag at slot 0. One allocation covers the whole inline tree; `Rc`
    /// makes copies O(1) and field update clones the slots first (CoW —
    /// mutable value semantics, Racordon et al., JOT 2022).
    Agg(u32, Rc<Vec<Value>>),
    /// A protocol existential: hidden payload plus erased witness closures.
    Existential(Rc<Value>, Rc<Vec<Value>>),
    /// A flat closure: target chunk plus its captured environment
    /// (Cardelli, LFP 1984).
    Closure(u32, Rc<Vec<Value>>),
    /// Index into the VM's slot arena (a mutable cell).
    Cell(usize),
    /// A `'heap` object handle: index into the machine's object arena.
    /// Copies alias; the region, not the handle, owns the storage.
    Object(u32),
    /// A reified one-shot return continuation (`MakeCont`): the index and
    /// identity of the frame it returns from. `CallCont` unwinds to that
    /// frame and returns from it; the identity check makes an escaped
    /// continuation a clean trap instead of a smashed stack.
    Cont(u32, u64),
}

impl From<Constant> for Value {
    fn from(value: Constant) -> Self {
        match value {
            Constant::I64(value) => Self::I64(value),
            Constant::F64(value) => Self::F64(value),
            Constant::Bool(value) => Self::Bool(value),
            Constant::Byte(value) => Self::Byte(value),
            Constant::Void => Self::Void,
            Constant::Ptr(value) => Self::Ptr(Pointer::static_at(value)),
        }
    }
}

/// A register-or-constant operand normalized without cloning aggregate
/// register values or materializing scalar constants as full VM values.
#[derive(Clone, Copy)]
enum OperandValue<'a> {
    I64(i64),
    F64(f64),
    Bool(bool),
    Byte(u8),
    Void,
    Ptr(Pointer),
    Aggregate(&'a Value),
}

impl<'a> OperandValue<'a> {
    fn from_value(value: &'a Value) -> Self {
        match value {
            Value::I64(value) => Self::I64(*value),
            Value::F64(value) => Self::F64(*value),
            Value::Bool(value) => Self::Bool(*value),
            Value::Byte(value) => Self::Byte(*value),
            Value::Void => Self::Void,
            Value::Ptr(value) => Self::Ptr(*value),
            value => Self::Aggregate(value),
        }
    }
}

impl std::fmt::Debug for OperandValue<'_> {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::I64(value) => formatter.debug_tuple("I64").field(value).finish(),
            Self::F64(value) => formatter.debug_tuple("F64").field(value).finish(),
            Self::Bool(value) => formatter.debug_tuple("Bool").field(value).finish(),
            Self::Byte(value) => formatter.debug_tuple("Byte").field(value).finish(),
            Self::Void => formatter.write_str("Void"),
            Self::Ptr(value) => formatter.debug_tuple("Ptr").field(value).finish(),
            Self::Aggregate(value) => formatter.debug_tuple("Aggregate").field(value).finish(),
        }
    }
}

impl<'a> From<Constant> for OperandValue<'a> {
    fn from(value: Constant) -> Self {
        match value {
            Constant::I64(value) => Self::I64(value),
            Constant::F64(value) => Self::F64(value),
            Constant::Bool(value) => Self::Bool(value),
            Constant::Byte(value) => Self::Byte(value),
            Constant::Void => Self::Void,
            Constant::Ptr(value) => Self::Ptr(Pointer::static_at(value)),
        }
    }
}

struct Frame<'module> {
    chunk: u32,
    /// Immutable executable code for `chunk`. Keeping the slice in the frame
    /// avoids rebuilding it from the module's chunk and instruction Vecs on
    /// every dispatch.
    code: &'module [Insn],
    pc: usize,
    regs: Vec<Value>,
    /// The closure environment this frame runs under (empty for direct
    /// calls).
    env: Rc<Vec<Value>>,
    /// Register in the *caller's* frame that receives this frame's Ret.
    dest: u16,
    /// This frame's identity for reified continuations: unique across the
    /// whole run, so a `Cont` outliving its frame can be detected.
    id: u64,
}

/// Far above any reasonable program, far below host memory: frames are
/// heap data, so this only bounds runaway recursion.
const MAX_FRAMES: usize = 1 << 20;

/// Execution budgets (ADR 0043 §7). Defaults are effectively unlimited
/// (frames keep the historical cap), so script runs are unchanged;
/// `run_export` callers pass real limits. Exhaustion is an ordinary VM
/// error on the call that spent the budget.
#[derive(Debug, Clone, Copy)]
pub struct Budgets {
    /// Instructions executed before the run fails.
    pub instructions: u64,
    /// Maximum live frames (the historical `MAX_FRAMES` by default).
    pub frames: usize,
    /// Ceiling on byte-memory size (statics plus every allocation).
    pub memory_bytes: usize,
}

impl Default for Budgets {
    fn default() -> Self {
        Self {
            instructions: u64::MAX,
            frames: MAX_FRAMES,
            memory_bytes: usize::MAX,
        }
    }
}

/// Frame.dest sentinel for finalizer frames: their Ret writes nowhere.
const FINALIZER_DEST: u16 = u16::MAX;
/// A frame running a spawned task's closure (ADR 0058, sequential
/// reference executor): its return value goes to the task slot recorded
/// on the worker's task-destination stack, not to a caller register.
const TASK_DEST: u16 = u16::MAX - 1;

pub fn run(module: &Module, io: &mut dyn IO) -> Result<Value, String> {
    Ok(run_machine(module, io)?.0)
}

/// Allocation balance at VM exit, read before the machine is dropped —
/// the test-suite leak fences assert `live == result` on both counters
/// (everything still live must be owned by the result value itself),
/// but only when the result footprint is exact.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct RunBalance {
    /// Live allocation records at exit.
    pub live_allocations: usize,
    /// Live `'heap` objects at exit.
    pub live_objects: usize,
    /// Allocation records reachable from the result value.
    pub result_allocations: usize,
    /// `'heap` objects kept live by regions the result value holds.
    pub result_objects: usize,
    /// Whether the footprint walk saw the result's whole ownership tree.
    /// Raw buffer contents are untyped bytes the walk can't see through,
    /// so a buffer big enough to hold a word (pointers and boxed-aggregate
    /// handles are 8-byte words) makes the counts a lower bound:
    /// allocations reachable only through element loads (e.g. an
    /// array-of-Strings result) go uncounted. Fences must then check only
    /// `live >= result`. Shorter buffers (a short String's bytes) can't
    /// reference anything and stay exact.
    pub result_exact: bool,
}

/// `run_displayed` with the allocation balance — the REPL tests' fence.
pub fn run_displayed_counted(
    module: &Module,
    io: &mut dyn IO,
    names: &ValueNames,
) -> Result<(Value, String, RunBalance), String> {
    let (value, machine) = run_machine(module, io)?;
    let display = render_value(&machine, names, &value)?;
    let balance = machine.balance(&value);
    Ok((value, display, balance))
}

/// Run and render the program value Talk-style while the machine is
/// still alive (strings point into its byte memory).
#[cfg(test)]
pub(crate) fn run_displayed(
    module: &Module,
    io: &mut dyn IO,
    names: &ValueNames,
) -> Result<(Value, String), String> {
    let (value, machine) = run_machine(module, io)?;
    let display = render_value(&machine, names, &value)?;
    Ok((value, display))
}

/// A host-supplied argument for `run_export`.
#[derive(Debug, Clone)]
pub enum HostValue {
    Int(i64),
    Float(f64),
    Bool(bool),
    Byte(u8),
    /// UTF-8 bytes surfaced to the callee as a core String backed by the
    /// machine's static prefix: `free`/`retain` on static memory are
    /// no-ops, so the value can neither leak nor double-free, and a
    /// mutating callee takes the copy-on-write path.
    String(Vec<u8>),
}

/// A finished export call: the result value plus the still-live machine
/// whose byte memory string results point into.
pub struct RunOutcome<'io> {
    pub value: Value,
    machine: Machine<'io>,
}

/// The bridge-facing logical shape of one aggregate value: its display
/// identity, the live case tag for sums, and how many logical elements
/// it has.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct AggregateView {
    pub symbol: Option<Symbol>,
    pub tag: Option<u16>,
    pub len: usize,
}

impl RunOutcome<'_> {
    /// Bridge access (ADR 0043 §5): read one 8-byte word of the
    /// machine's memory, for walking array storage out of a returned
    /// value graph.
    pub fn read_word(&self, pointer: Pointer) -> Result<u64, String> {
        self.machine.read_word(pointer)
    }

    /// Bridge access: one raw byte of the machine's memory (byte-array
    /// element storage).
    pub fn read_byte(&self, pointer: Pointer) -> Result<u8, String> {
        self.machine.check_access(pointer, 1, "load")?;
        self.machine
            .mem
            .get(pointer.address() as usize)
            .copied()
            .ok_or_else(|| "vm: load out of bounds".into())
    }

    /// Bridge access: a boxed arena slot — the storage representation of
    /// record, enum, and nested-array elements inside arrays.
    pub fn boxed_value(&self, handle: u64) -> Result<&Value, String> {
        let handle = handle as usize;
        if handle == 0 {
            return Err("vm: load of a bad arena handle".into());
        }
        self.machine
            .boxed
            .get(handle)
            .ok_or_else(|| "vm: load of a bad arena handle".into())
    }

    /// The logical view of one aggregate value for the host bridge:
    /// display identity, case tag for sums, and logical element count.
    /// Flat values resolve through the module's published layout table —
    /// the one source of representation truth — so the bridge walks
    /// logical structure without knowing offsets.
    pub fn aggregate(&self, value: &Value) -> Result<AggregateView, String> {
        match value {
            Value::Agg(layout, slots) => {
                let desc = self
                    .machine
                    .layouts
                    .get(*layout as usize)
                    .ok_or("vm: aggregate with an unknown layout")?;
                match &desc.body {
                    LayoutBody::Product(fields) => Ok(AggregateView {
                        symbol: desc.symbol,
                        tag: None,
                        len: fields.len(),
                    }),
                    LayoutBody::Sum(variants) => {
                        let Some(Value::I64(tag)) = slots.first() else {
                            return Err("vm: flat sum without a tag".into());
                        };
                        let tag =
                            u16::try_from(*tag).map_err(|_| "vm: flat sum tag out of range")?;
                        let len = variants
                            .get(usize::from(tag))
                            .ok_or("vm: flat sum tag out of range")?
                            .len();
                        Ok(AggregateView {
                            symbol: desc.symbol,
                            tag: Some(tag),
                            len,
                        })
                    }
                    LayoutBody::Unshaped => Err("vm: aggregate with an unshaped layout".into()),
                }
            }
            other => Err(format!("expected an aggregate value, got {other:?}")),
        }
    }

    /// One logical element of an aggregate (a record field, tuple item,
    /// or the live variant's payload element), by index.
    pub fn element(&self, value: &Value, index: u16) -> Result<Value, String> {
        match value {
            Value::Agg(layout, slots) => {
                let (offset, shape) = field_site(&self.machine.layouts, *layout, slots, index)?;
                read_slots(&self.machine.layouts, slots, offset, shape)
            }
            other => Err(format!("expected an aggregate value, got {other:?}")),
        }
    }

    /// The UTF-8 bytes of a String-shaped value in this outcome.
    pub fn string_bytes(&self, value: &Value) -> Result<&[u8], String> {
        let Value::Agg(_, fields) = value else {
            return Err("not a string value".into());
        };
        let Some((base, len)) = string_bytes(fields) else {
            return Err("not a string value".into());
        };
        self.machine.string_display_bytes(base, len)
    }

    pub fn balance(&self) -> RunBalance {
        self.machine.balance(&self.value)
    }

    pub fn display(&self, names: &ValueNames) -> Result<String, String> {
        render_value(&self.machine, names, &self.value)
    }
}

/// Call an exported function by name on a fresh machine. Each call is a
/// complete run: the export's wrapper chunk installs the host handlers
/// and runs global init/teardown, so effects behave exactly as in a
/// script run.
pub fn run_export<'io>(
    module: &Module,
    name: &str,
    args: &[HostValue],
    string: Symbol,
    budgets: Budgets,
    io: &'io mut dyn IO,
) -> Result<RunOutcome<'io>, String> {
    let mut stats = NoStats;
    run_export_inner(module, name, args, string, budgets, io, &mut stats)
}

/// [`run_export`] with exact per-opcode and per-instruction execution counts.
/// The caller-owned collector remains available when the VM traps and can
/// aggregate multiple exports from the same module.
pub fn run_export_with_stats<'io>(
    module: &Module,
    name: &str,
    args: &[HostValue],
    string: Symbol,
    budgets: Budgets,
    io: &'io mut dyn IO,
    stats: &mut VmStats,
) -> Result<RunOutcome<'io>, String> {
    run_export_inner(module, name, args, string, budgets, io, stats)
}

trait StatsSink {
    fn begin_run(&mut self, module: &Module) -> Result<(), String>;
    fn record(&mut self, chunk: usize, pc: usize);
    fn finish_run(&mut self);
}

struct NoStats;

impl StatsSink for NoStats {
    #[inline(always)]
    fn begin_run(&mut self, _module: &Module) -> Result<(), String> {
        Ok(())
    }

    #[inline(always)]
    fn record(&mut self, _chunk: usize, _pc: usize) {}

    #[inline(always)]
    fn finish_run(&mut self) {}
}

impl StatsSink for VmStats {
    #[inline(always)]
    fn begin_run(&mut self, module: &Module) -> Result<(), String> {
        VmStats::begin_run(self, module)
    }

    #[inline(always)]
    fn record(&mut self, chunk: usize, pc: usize) {
        VmStats::record(self, chunk, pc);
    }

    #[inline(always)]
    fn finish_run(&mut self) {
        VmStats::finish_run(self);
    }
}

fn run_export_inner<'io, S: StatsSink>(
    module: &Module,
    name: &str,
    args: &[HostValue],
    string: Symbol,
    budgets: Budgets,
    io: &'io mut dyn IO,
    stats: &mut S,
) -> Result<RunOutcome<'io>, String> {
    crate::profile::init();
    profiling::scope!("vm.run_export", name);
    let Some(&(_, chunk_index)) = module.exports.iter().find(|(export, _)| export == name) else {
        return Err(format!("vm: no exported function named `{name}`"));
    };
    let target = chunk(module, chunk_index)?;
    if args.len() != target.arity as usize {
        return Err(format!(
            "vm: export `{name}` takes {} arguments, got {}",
            target.arity,
            args.len()
        ));
    }

    // String arguments live in the machine's static prefix, exactly like
    // string literals: appended after the module statics, before the
    // machine snapshots its static length.
    let mut mem = module.statics.clone();
    let flat_string = string_layout(module, string)?;
    let mut values: Vec<Value> = Vec::with_capacity(args.len());
    for arg in args {
        values.push(match arg {
            HostValue::Int(v) => Value::I64(*v),
            HostValue::Float(v) => Value::F64(*v),
            HostValue::Bool(v) => Value::Bool(*v),
            HostValue::Byte(v) => Value::Byte(*v),
            HostValue::String(bytes) => {
                let base = mem.len() as u32;
                mem.extend_from_slice(bytes);
                // A zero-length string still needs a base address inside
                // the static range: one past the prefix would read as a
                // managed pointer, and freeing it faults.
                if bytes.is_empty() {
                    mem.push(0);
                }
                let len = bytes.len() as i64;
                // The flat String its code reads: storage spliced at
                // slot 0, then byte count and capacity.
                let Some(layout) = flat_string else {
                    return Err(
                        "vm: module publishes no String layout for host string arguments".into(),
                    );
                };
                Value::Agg(
                    layout,
                    Rc::new(vec![
                        Value::Ptr(Pointer::static_at(base)),
                        Value::I64(len),
                        Value::I64(len),
                    ]),
                )
            }
        });
    }

    let mut machine = Machine {
        slots: vec![],
        static_len: mem.len() as u32,
        mem,
        layouts: module.layouts.clone(),
        static_strings: FxHashMap::default(),
        allocations: Allocations::default(),
        boxed: vec![Value::Void],
        objects: Objects::default(),
        tasks: vec![],
        shared_module: None,
        external: Vec::new(),
        deadlines: Vec::new(),
        io,
    };
    stats.begin_run(module)?;
    let result = run_loop(
        module,
        &mut machine,
        chunk_index,
        values,
        Rc::new(vec![]),
        &budgets,
        stats,
    );
    stats.finish_run();
    match result {
        Ok(value) => Ok(RunOutcome { value, machine }),
        Err(err) => Err(format!(
            "{err} [balance at trap: {} live allocations, {} live 'heap objects]",
            machine.allocations.live_count(),
            machine.objects.live_objects()
        )),
    }
}

/// The published layout of the core String struct, if this module has
/// one — the shape host string arguments must fabricate. Present but
/// unexpected is an error: fabricating the wrong width would corrupt the
/// callee's reads.
fn string_layout(module: &Module, string: Symbol) -> Result<Option<u32>, String> {
    for (id, desc) in module.layouts.iter().enumerate() {
        if desc.symbol == Some(string) && !matches!(desc.body, LayoutBody::Unshaped) {
            if desc.width != 3 {
                return Err("vm: string layout has an unexpected shape".into());
            }
            return Ok(Some(
                u32::try_from(id).map_err(|_| "vm: layout table too large")?,
            ));
        }
    }
    Ok(None)
}

fn run_machine<'io>(module: &Module, io: &'io mut dyn IO) -> Result<(Value, Machine<'io>), String> {
    let mut machine = Machine {
        slots: vec![],
        mem: module.statics.clone(),
        static_len: module.statics.len() as u32,
        layouts: module.layouts.clone(),
        static_strings: FxHashMap::default(),
        allocations: Allocations::default(),
        // Slot 0 is a reserved placeholder (like arg_pool's) so that a
        // zeroed, never-stored cell can't alias a real handle.
        boxed: vec![Value::Void],
        objects: Objects::default(),
        tasks: vec![],
        shared_module: None,
        external: Vec::new(),
        deadlines: Vec::new(),
        io,
    };
    let mut stats = NoStats;
    match run_loop(
        module,
        &mut machine,
        module.entry,
        vec![],
        Rc::new(vec![]),
        &Budgets::default(),
        &mut stats,
    ) {
        Ok(value) => Ok((value, machine)),
        // Balance-at-trap: a runtime trap (double free, use-after-free, …)
        // reports the allocation-balance state alongside the message — the
        // cheap diagnostic for the ownership test fences.
        Err(err) => Err(format!(
            "{err} [balance at trap: {} live allocations, {} live 'heap objects]",
            machine.allocations.live_count(),
            machine.objects.live_objects()
        )),
    }
}

/// An installed deep handler (ADR 0032 dynamic nearest-handler routing).
/// Entries tie to their installing frame by (depth, frame id) and go
/// stale with it — no pop-site bookkeeping.
#[derive(Clone)]
struct HandlerEntry {
    effect: u32,
    clause: Value,
    cont: Value,
    /// ADR 0068: the clause binds the stored resumption — performs that
    /// match this entry suspend their extent instead of calling.
    binds: bool,
    depth: usize,
    frame_id: u64,
}

/// One frame of a suspended extent (ADR 0064): a `Frame` without the
/// borrowed code slice, so it can outlive the dispatch that captured it.
/// Rehydrated against the module's chunk table on resume or cancel.
struct SuspendedFrame {
    chunk: u32,
    pc: usize,
    regs: Vec<Value>,
    env: Rc<Vec<Value>>,
    dest: u16,
    id: u64,
}

impl SuspendedFrame {
    fn capture(frame: Frame<'_>) -> Self {
        SuspendedFrame {
            chunk: frame.chunk,
            pc: frame.pc,
            regs: frame.regs,
            env: frame.env,
            dest: frame.dest,
            id: frame.id,
        }
    }
}

/// A stored one-shot resumption (ADR 0064): the frames of a suspended
/// extent from its installing frame through its perform site, the
/// handler entries those frames had installed (depths relative to the
/// segment base), and the register in the top frame that receives the
/// resume value. Named by a worker-local slot; the slot is taken
/// exactly once — the Talk-level `Resumption` value is linear, and the
/// take is the dynamic backstop.
struct Segment {
    frames: Vec<SuspendedFrame>,
    handlers: Vec<HandlerEntry>,
    dest: u16,
}

/// One worker's interpreter state (ADR 0050): frame stack, handler
/// stack, handler-search floor, unwind state, frame-id source, and the
/// register-buffer pool are per-worker. A parallel VM runs one `Worker`
/// per OS thread over the shared immutable `Module`; a task never
/// inherits another worker's frame-bound state, so handler delimiters
/// and continuations cannot cross workers.
struct Worker<'m> {
    frames: Vec<Frame<'m>>,
    /// Finalizer frames currently on the stack: the teardown walk must
    /// not advance (and above all must not bulk-free) while one is
    /// running.
    finalizer_frames: usize,
    handlers: Vec<HandlerEntry>,
    /// A clause runs outside its own handler (CHG-01): performs inside
    /// it search below this floor.
    handler_floor: usize,
    /// An effect abort in progress (ADR 0027): the delimiter's frame
    /// index and the value to deliver once every frame above it has run
    /// its unwind entry and popped.
    unwinding: Option<(usize, Value)>,
    next_frame_id: u64,
    regs_pool: Vec<Vec<Value>>,
    empty_env: Rc<Vec<Value>>,
    /// Task slots awaiting the return of a `TASK_DEST` frame, innermost
    /// last (task frames return LIFO under the sequential executor).
    task_dests: Vec<usize>,
    /// Stored suspended extents (ADR 0064), named by slot. `None` =
    /// spent: resuming or cancelling takes the slot, and a second take
    /// is the one-shot trap.
    suspended: Vec<Option<Segment>>,
}

impl Worker<'_> {
    fn new() -> Self {
        Worker {
            frames: Vec::new(),
            finalizer_frames: 0,
            handlers: Vec::new(),
            handler_floor: usize::MAX,
            unwinding: None,
            next_frame_id: 0,
            regs_pool: Vec::new(),
            empty_env: Rc::new(vec![]),
            task_dests: Vec::new(),
            suspended: Vec::new(),
        }
    }

    fn fresh_frame_id(&mut self) -> u64 {
        let id = self.next_frame_id;
        self.next_frame_id += 1;
        id
    }
}

/// One isolated VM worker (ADR 0058): a fresh machine over the shared
/// module, entered at the transferred closure with the transferred
/// argument in its first register, under a buffering IO sink the parent
/// replays at join. The worker's exit balance is enforced like a
/// program's: everything but the output must be released.
#[cfg(any(not(target_arch = "wasm32"), target_feature = "atomics"))]
fn worker_task_main(
    module: std::sync::Arc<Module>,
    worker: Transfer,
    arg: Transfer,
    budgets: Budgets,
) -> Result<(Transfer, Vec<u8>, Vec<u8>), String> {
    let mut io = crate::io::CaptureIO::default();
    let result = {
        let mut machine = Machine {
            slots: vec![],
            mem: module.statics.clone(),
            static_len: module.statics.len() as u32,
            layouts: module.layouts.clone(),
            static_strings: FxHashMap::default(),
            allocations: Allocations::default(),
            boxed: vec![Value::Void],
            objects: Objects::default(),
            tasks: vec![],
            shared_module: Some(module.clone()),
            external: Vec::new(),
            deadlines: Vec::new(),
            io: &mut io,
        };
        let worker_value = machine.deserialize_transfer(&worker)?;
        let arg_value = machine.deserialize_transfer(&arg)?;
        let Value::Closure(entry, env) = worker_value else {
            return Err("vm: task spawn of a non-closure".into());
        };
        let mut stats = NoStats;
        let value = run_loop(
            &module,
            &mut machine,
            entry,
            vec![arg_value],
            env,
            &budgets,
            &mut stats,
        )?;
        let balance = machine.balance(&value);
        if balance.result_exact
            && (balance.live_allocations != balance.result_allocations
                || balance.live_objects != balance.result_objects)
        {
            return Err(format!(
                "vm: worker resource leak: {} live allocations, {} live 'heap objects (task output owns {}, {})",
                balance.live_allocations,
                balance.live_objects,
                balance.result_allocations,
                balance.result_objects
            ));
        }
        machine.serialize_transfer(&value)?
    };
    Ok((result, io.out, io.err))
}

fn run_loop<S: StatsSink>(
    module: &Module,
    machine: &mut Machine,
    entry_index: u32,
    args: Vec<Value>,
    entry_env: Rc<Vec<Value>>,
    budgets: &Budgets,
    stats: &mut S,
) -> Result<Value, String> {
    crate::profile::init();
    profiling::scope!("vm.run_loop");
    let mut fuel = budgets.instructions;
    let entry = chunk(module, entry_index)?;
    let mut worker = Worker::new();
    let mut regs = vec![Value::Void; entry.n_regs as usize];
    for (index, arg) in args.into_iter().enumerate() {
        regs[index] = arg;
    }
    let entry_id = worker.fresh_frame_id();
    worker.frames.push(Frame {
        chunk: entry_index,
        code: &entry.code,
        pc: 0,
        regs,
        env: entry_env,
        dest: 0,
        id: entry_id,
    });

    let trace_mem = trace_mem();
    loop {
        if fuel == 0 {
            return Err("vm: instruction budget exhausted".into());
        }
        fuel -= 1;
        // Region-teardown pump: while a region is finalizing, run its
        // members' finalizer thunks (reverse allocation order) as ordinary
        // worker.frames before executing anything else; the walk's bulk free
        // happens inside `next_finalizer` when members are exhausted.
        if worker.finalizer_frames == 0
            && machine.objects.finalizing()
            && let Some((thunk, object)) = machine.objects.next_finalizer()
        {
            if worker.frames.len() >= budgets.frames {
                return Err("vm: call stack overflow".into());
            }
            let Value::Closure(fin_chunk, env) = thunk else {
                return Err("vm: finalizer is not a function value".into());
            };
            let target = chunk(module, fin_chunk)?;
            check_call_shape(target, 1)?;
            let mut regs = worker.regs_pool.pop().unwrap_or_default();
            regs.resize(target.n_regs as usize, Value::Void);
            regs[0] = Value::Object(object);
            let id = worker.fresh_frame_id();
            worker.frames.push(Frame {
                chunk: fin_chunk,
                code: &target.code,
                pc: 0,
                regs,
                env,
                dest: FINALIZER_DEST,
                id,
            });
            worker.finalizer_frames += 1;
            continue;
        }

        let frame_count = worker.frames.len();
        let frame_index = frame_count - 1;
        let frame = &mut worker.frames[frame_index];
        let current_chunk = frame.chunk;
        let pc = frame.pc;
        let Some(&insn) = frame.code.get(pc) else {
            return Err(format!(
                "vm: fell off the end of chunk {}",
                chunk(module, current_chunk)?.name
            ));
        };
        stats.record(current_chunk as usize, pc);
        frame.pc = pc + 1;

        match insn {
            Insn::Call {
                dest,
                chunk: callee,
                args_start,
                args_len,
            } => {
                if frame_count >= budgets.frames {
                    let mut cycle: Vec<String> = worker
                        .frames
                        .iter()
                        .rev()
                        .take(8)
                        .map(|f| chunk(module, f.chunk).map(|c| c.name.clone()).unwrap_or_default())
                        .collect();
                    cycle.reverse();
                    return Err(format!("vm: call stack overflow [top frames: {}]", cycle.join(" -> ")));
                }
                let target = chunk(module, callee)?;
                check_call_shape(target, args_len)?;
                let regs = call_regs(
                    module,
                    frame,
                    args_start,
                    args_len,
                    target.n_regs,
                    &mut worker.regs_pool,
                )?;
                let id = worker.fresh_frame_id();
                let env = worker.empty_env.clone();
                worker.frames.push(Frame {
                    chunk: callee,
                    code: &target.code,
                    pc: 0,
                    regs,
                    env,
                    dest,
                    id,
                });
            }
            Insn::CallIndirect {
                dest,
                callee,
                args_start,
                args_len,
            } => {
                if frame_count >= budgets.frames {
                    return Err("vm: call stack overflow".into());
                }
                let Some(callee_value) = frame.regs.get(callee as usize).cloned() else {
                    return Err("vm: callee register out of range".into());
                };
                let Value::Closure(target, env) = callee_value else {
                    return Err("vm: indirect call of a non-closure".into());
                };
                let target_chunk = chunk(module, target)?;
                check_call_shape(target_chunk, args_len)?;
                let regs = call_regs(
                    module,
                    frame,
                    args_start,
                    args_len,
                    target_chunk.n_regs,
                    &mut worker.regs_pool,
                )?;
                let id = worker.fresh_frame_id();
                worker.frames.push(Frame {
                    chunk: target,
                    code: &target_chunk.code,
                    pc: 0,
                    regs,
                    env,
                    dest,
                    id,
                });
            }
            Insn::Ret { src } => {
                let value = frame.regs[src as usize].clone();
                if let Some(value) =
                    deliver_return(
                        &mut worker.frames,
                        &mut worker.finalizer_frames,
                        &mut worker.regs_pool,
                        &mut worker.task_dests,
                        &mut machine.tasks,
                        value,
                    )
                {
                    return Ok(value);
                }
            }
            Insn::Trap { message } => {
                return Err(module
                    .traps
                    .get(message as usize)
                    .cloned()
                    .unwrap_or_else(|| "vm: trap".into()));
            }
            Insn::MakeCont { dest } => {
                frame.regs[dest as usize] = Value::Cont(frame_index as u32, frame.id);
            }
            Insn::PushHandler {
                effect,
                clause,
                cont,
                binds,
            } => {
                while worker.handlers.last().is_some_and(|entry| {
                    worker.frames
                        .get(entry.depth)
                        .is_none_or(|frame| frame.id != entry.frame_id)
                }) {
                    worker.handlers.pop();
                }
                let frame = &worker.frames[frame_index];
                worker.handlers.push(HandlerEntry {
                    effect,
                    clause: frame.regs[clause as usize].clone(),
                    cont: frame.regs[cont as usize].clone(),
                    binds,
                    depth: frame_index,
                    frame_id: frame.id,
                });
            }
            Insn::FindHandler {
                clause,
                cont,
                index,
                binds,
                effect,
            } => {
                let limit = worker.handler_floor.min(worker.handlers.len());
                let found = worker.handlers[..limit]
                    .iter()
                    .enumerate()
                    .rev()
                    .find(|(_, entry)| {
                        entry.effect == effect
                            && worker.frames
                                .get(entry.depth)
                                .is_some_and(|frame| frame.id == entry.frame_id)
                    });
                let Some((position, entry)) = found else {
                    return Err("vm: perform with no installed handler".into());
                };
                let (clause_value, cont_value, binds_value) =
                    (entry.clause.clone(), entry.cont.clone(), entry.binds);
                let regs = &mut worker.frames[frame_index].regs;
                regs[clause as usize] = clause_value;
                regs[cont as usize] = cont_value;
                regs[index as usize] = Value::I64(position as i64);
                regs[binds as usize] = Value::Bool(binds_value);
            }
            Insn::GetFloor { dest } => {
                let floor = i64::try_from(worker.handler_floor).unwrap_or(i64::MAX);
                frame.regs[dest as usize] = Value::I64(floor);
            }
            Insn::SetFloor { src } => {
                let Value::I64(floor) = frame.regs[src as usize] else {
                    return Err("vm: handler floor must be an Int".into());
                };
                worker.handler_floor = usize::try_from(floor).unwrap_or(usize::MAX);
            }
            Insn::CallCont { callee, src } => {
                if worker.unwinding.is_some() {
                    return Err("vm: abort during abort worker.unwinding".into());
                }
                let cont = frame.regs[callee as usize].clone();
                let value = frame.regs[src as usize].clone();
                let Value::Cont(target, id) = cont else {
                    return Err("vm: continuation call on a non-continuation".into());
                };
                let mut target = target as usize;
                if worker.frames.get(target).is_none_or(|frame| frame.id != id) {
                    // A frame that traveled inside a suspended extent
                    // (ADR 0064) resumes at a different depth; identity
                    // is the frame id, the index is only a hint.
                    match worker.frames.iter().position(|frame| frame.id == id) {
                        Some(found) => target = found,
                        None => {
                            return Err(
                                "vm: continuation is no longer live (its scope already exited)"
                                    .into(),
                            );
                        }
                    }
                }
                // The aborted computation's handler-search floor dies with
                // it.
                worker.handler_floor = usize::MAX;
                if target == worker.frames.len() - 1 {
                    // The continuation targets the executing frame itself:
                    // the delimiter is the aborting frame, whose drops
                    // already ran on its path here — deliver in place as a
                    // Ret would. No suspended worker.frames, so no unwind walk.
                    if let Some(value) =
                        deliver_return(
                        &mut worker.frames,
                        &mut worker.finalizer_frames,
                        &mut worker.regs_pool,
                        &mut worker.task_dests,
                        &mut machine.tasks,
                        value,
                    )
                    {
                        return Ok(value);
                    }
                } else {
                    // Begin the unwind (ADR 0027): pop the aborting
                    // handler's own frame (its drops already ran on its
                    // path to the abort), then walk down to the delimiter's
                    // frame, entering each suspended frame once at its
                    // unwind entry (one-shot delimited abort — Hieb, Dybvig
                    // & Bruggeman, PLDI 1990's stack slice — consumed
                    // through its cleanup, OCaml's `discontinue`).
                    pop_frame(&mut worker.frames, &mut worker.finalizer_frames, &mut worker.regs_pool);
                    worker.unwinding = Some((target, value));
                    if let Some(value) = advance_unwind(
                        module,
                        &mut worker.frames,
                        &mut worker.finalizer_frames,
                        &mut worker.regs_pool,
                        &mut worker.task_dests,
                        &mut machine.tasks,
                        &mut worker.unwinding,
                    )? {
                        return Ok(value);
                    }
                }
            }
            Insn::TaskSpawn {
                dest,
                arg,
                worker: worker_reg,
            } => {
                let Some(closure) = frame.regs.get(worker_reg as usize).cloned() else {
                    return Err("vm: task worker register out of range".into());
                };
                let Some(arg_value) = frame.regs.get(arg as usize).cloned() else {
                    return Err("vm: task argument register out of range".into());
                };
                let Value::Closure(target, _) = closure.clone() else {
                    return Err("vm: task spawn of a non-closure".into());
                };
                let target_chunk = chunk(module, target)?;
                check_call_shape(target_chunk, 1)?;
                #[cfg(any(not(target_arch = "wasm32"), target_feature = "atomics"))]
                {
                    // Isolated worker (ADR 0058): image the Send-checked
                    // values, release this machine's copies (the worker
                    // owns them now), and run the closure on a fresh
                    // machine over the shared module on its own thread.
                    let worker_transfer = machine.serialize_transfer(&closure)?;
                    let arg_transfer = machine.serialize_transfer(&arg_value)?;
                    machine.release_transferred(&closure)?;
                    machine.release_transferred(&arg_value)?;
                    let shared = match &machine.shared_module {
                        Some(shared) => shared.clone(),
                        None => {
                            let shared = std::sync::Arc::new(module.clone());
                            machine.shared_module = Some(shared.clone());
                            shared
                        }
                    };
                    let worker_budgets = *budgets;
                    let handle = thread::Builder::new()
                        .name("talk-task".into())
                        .spawn(move || {
                            worker_task_main(shared, worker_transfer, arg_transfer, worker_budgets)
                        })
                        .map_err(|error| format!("vm: task spawn failed: {error}"))?;
                    let slot = machine.tasks.len();
                    machine.tasks.push(TaskSlot::Running(handle));
                    frame.regs[dest as usize] = Value::I64(slot as i64);
                }
                #[cfg(all(target_arch = "wasm32", not(target_feature = "atomics")))]
                {
                    // Single-threaded host: the task runs to completion at
                    // the spawn site, as a frame whose return routes to
                    // its task slot. Physical parallelism is runtime
                    // policy; a correct program cannot tell.
                    if frame_count >= budgets.frames {
                        return Err("vm: call stack overflow".into());
                    }
                    let Value::Closure(_, env) = closure else {
                        return Err("vm: task spawn of a non-closure".into());
                    };
                    let slot = machine.tasks.len();
                    machine.tasks.push(TaskSlot::Pending);
                    frame.regs[dest as usize] = Value::I64(slot as i64);
                    let mut regs = worker.regs_pool.pop().unwrap_or_default();
                    regs.resize(target_chunk.n_regs as usize, Value::Void);
                    regs[0] = arg_value;
                    let id = worker.fresh_frame_id();
                    worker.task_dests.push(slot);
                    worker.frames.push(Frame {
                        chunk: target,
                        code: &target_chunk.code,
                        pc: 0,
                        regs,
                        env,
                        dest: TASK_DEST,
                        id,
                    });
                }
            }
            Insn::Suspend {
                dest,
                effect,
                args_start,
                args_len,
                entry,
            } => {
                // ADR 0064: capture the extent from the installing frame
                // through this perform site into a stored resumption and
                // run the clause in the installer's place, with the
                // installer's outward linkage — a clause that completes
                // without resuming simply returns where the installer
                // would have.
                if frame_count >= budgets.frames {
                    return Err("vm: call stack overflow".into());
                }
                if worker.unwinding.is_some() {
                    return Err("vm: suspend during an unwind".into());
                }
                // Read the perform's arguments before the frame moves
                // into the segment.
                let mut args = Vec::with_capacity(usize::from(args_len));
                let start = usize::try_from(args_start)
                    .map_err(|_| "vm: bad argument pool range")?;
                let end = start
                    .checked_add(usize::from(args_len))
                    .ok_or("vm: bad argument pool range")?;
                let arg_regs = module
                    .arg_pool
                    .get(start..end)
                    .ok_or("vm: bad argument pool range")?;
                for &src in arg_regs {
                    args.push(rk_value(module, frame, src)?);
                }
                // ADR 0068: the preceding FindHandler located the entry
                // (and branched on its clause kind); this instruction
                // consumes that index — one handler search per perform.
                let Value::I64(position) = frame.regs[entry as usize] else {
                    return Err("vm: suspend without a located handler entry".into());
                };
                let Ok(position) = usize::try_from(position) else {
                    return Err("vm: suspend without a located handler entry".into());
                };
                let live = worker.handlers.get(position).is_some_and(|entry| {
                    entry.effect == effect
                        && worker
                            .frames
                            .get(entry.depth)
                            .is_some_and(|frame| frame.id == entry.frame_id)
                });
                if !live {
                    return Err("vm: suspending handler entry lost its clause".into());
                }
                let base = worker.handlers[position].depth;
                // Every handler installed by a frame of the extent
                // travels with it (the triggering entry included, so a
                // resume re-installs it at the new base). Live entries
                // with depth >= base form a suffix of the stack.
                let boundary = worker
                    .handlers
                    .iter()
                    .position(|entry| {
                        entry.depth >= base
                            && worker
                                .frames
                                .get(entry.depth)
                                .is_some_and(|frame| frame.id == entry.frame_id)
                    })
                    .unwrap_or(worker.handlers.len());
                let mut captured: Vec<HandlerEntry> =
                    worker.handlers.split_off(boundary);
                captured.retain(|entry| {
                    worker
                        .frames
                        .get(entry.depth)
                        .is_some_and(|frame| frame.id == entry.frame_id)
                });
                for entry in &mut captured {
                    entry.depth -= base;
                }
                let clause = captured
                    .iter()
                    .find(|entry| entry.effect == effect && entry.depth == 0)
                    .map(|entry| entry.clause.clone())
                    .ok_or("vm: suspending handler entry lost its clause")?;
                // Capture the frames: installer through perform site.
                let split = worker.frames.split_off(base);
                let installer_dest = split.first().map(|frame| frame.dest).unwrap_or(0);
                let segment = Segment {
                    frames: split.into_iter().map(SuspendedFrame::capture).collect(),
                    handlers: captured,
                    dest,
                };
                let slot = match worker.suspended.iter().position(Option::is_none) {
                    Some(free) => {
                        worker.suspended[free] = Some(segment);
                        free
                    }
                    None => {
                        worker.suspended.push(Some(segment));
                        worker.suspended.len() - 1
                    }
                };
                // The clause's prologue wraps the raw slot in a
                // properly-laid-out `Resumption` aggregate — layout ids
                // are compile-time facts the runtime does not mint.
                let resumption = Value::I64(slot as i64);
                // Push the clause where the installer stood, with its
                // outward linkage. The clause runs under the handlers
                // that remain — its own entry left with the segment.
                let Value::Closure(target, env) = clause else {
                    return Err("vm: suspending handler clause is not a closure".into());
                };
                let target_chunk = chunk(module, target)?;
                check_call_shape(target_chunk, args_len + 1)?;
                let mut regs = worker.regs_pool.pop().unwrap_or_default();
                regs.reserve(usize::from(target_chunk.n_regs));
                regs.extend(args);
                regs.push(resumption);
                regs.resize(usize::from(target_chunk.n_regs), Value::Void);
                let id = worker.fresh_frame_id();
                worker.frames.push(Frame {
                    chunk: target,
                    code: &target_chunk.code,
                    pc: 0,
                    regs,
                    env,
                    dest: installer_dest,
                    id,
                });
                worker.handler_floor = usize::MAX;
            }
            Insn::Resume { dest, cont, value } => {
                // ADR 0064: splice the suspended extent above this frame,
                // rewiring its base to this call site — the extent's
                // completion arrives as this instruction's result, like
                // any call's. Its handlers re-install at the new base.
                let cont = frame.regs[cont as usize].clone();
                let value = frame.regs[value as usize].clone();
                let slot = resumption_slot(&cont)?;
                let Some(mut segment) =
                    worker.suspended.get_mut(slot).and_then(Option::take)
                else {
                    return Err("vm: resumption already spent (one-shot)".into());
                };
                if frame_count + segment.frames.len() >= budgets.frames {
                    return Err("vm: call stack overflow".into());
                }
                let base = worker.frames.len();
                if let Some(bottom) = segment.frames.first_mut() {
                    bottom.dest = dest;
                }
                for image in segment.frames {
                    let target_chunk = chunk(module, image.chunk)?;
                    worker.frames.push(Frame {
                        chunk: image.chunk,
                        code: &target_chunk.code,
                        pc: image.pc,
                        regs: image.regs,
                        env: image.env,
                        dest: image.dest,
                        id: image.id,
                    });
                }
                for mut entry in segment.handlers {
                    entry.depth += base;
                    worker.handlers.push(entry);
                }
                // The resumed extent runs under the handlers live HERE
                // plus its own (the dynamic-extent rule, ADR 0064).
                worker.handler_floor = usize::MAX;
                // Deliver the resume value to the suspended perform.
                #[allow(clippy::expect_used)]
                let top = worker
                    .frames
                    .last_mut()
                    .expect("a resumed segment has frames");
                top.regs[usize::from(segment.dest)] = value;
            }
            Insn::Cancel { cont } => {
                // ADR 0064: discard a suspended extent, unwinding its
                // frames through their cleanup entries (the ADR 0027
                // machinery), then return from this frame with unit —
                // exactly the cancel intrinsic's contract.
                if worker.unwinding.is_some() {
                    return Err("vm: cancel during an unwind".into());
                }
                let cont = frame.regs[cont as usize].clone();
                let slot = resumption_slot(&cont)?;
                let Some(segment) =
                    worker.suspended.get_mut(slot).and_then(Option::take)
                else {
                    return Err("vm: resumption already spent (one-shot)".into());
                };
                let target = worker.frames.len() - 1;
                for image in segment.frames {
                    let target_chunk = chunk(module, image.chunk)?;
                    worker.frames.push(Frame {
                        chunk: image.chunk,
                        code: &target_chunk.code,
                        pc: image.pc,
                        regs: image.regs,
                        env: image.env,
                        dest: image.dest,
                        id: image.id,
                    });
                }
                // The captured handlers die unrestored: cleanup code
                // performs no effects (CHG-08).
                worker.unwinding = Some((target, Value::Void));
                if let Some(value) = advance_unwind(
                    module,
                    &mut worker.frames,
                    &mut worker.finalizer_frames,
                    &mut worker.regs_pool,
                    &mut worker.task_dests,
                    &mut machine.tasks,
                    &mut worker.unwinding,
                )? {
                    return Ok(value);
                }
            }
            Insn::UnwindRet => {
                // An unwind entry finished. If this was the delimiter's
                // frame, deliver the stashed value (the unchanged tail of
                // the pre-ADR-0027 CallCont); otherwise pop the cleaned
                // frame and continue the unwind toward the delimiter.
                let Some((target, _)) = worker.unwinding else {
                    return Err("vm: unwind_ret outside an abort unwind".into());
                };
                if worker.frames.len() - 1 == target {
                    #[allow(clippy::expect_used)]
                    let (_, value) = worker.unwinding.take().expect("worker.unwinding checked above");
                    if let Some(value) =
                        deliver_return(
                        &mut worker.frames,
                        &mut worker.finalizer_frames,
                        &mut worker.regs_pool,
                        &mut worker.task_dests,
                        &mut machine.tasks,
                        value,
                    )
                    {
                        return Ok(value);
                    }
                } else {
                    pop_frame(&mut worker.frames, &mut worker.finalizer_frames, &mut worker.regs_pool);
                    if let Some(value) = advance_unwind(
                        module,
                        &mut worker.frames,
                        &mut worker.finalizer_frames,
                        &mut worker.regs_pool,
                        &mut worker.task_dests,
                        &mut machine.tasks,
                        &mut worker.unwinding,
                    )? {
                        return Ok(value);
                    }
                }
            }
            local => {
                if trace_mem {
                    let traced = match local {
                        Insn::Free { ptr, .. } => Some(("free-site", ptr)),
                        Insn::Retain { ptr, .. } => Some(("retain-site", ptr)),
                        _ => None,
                    };
                    // Allocation sites print after execution (the
                    // pointer only exists then), keyed by dest.
                    if let Insn::Alloc { .. } = local
                        && let Ok(target) = chunk(module, current_chunk)
                    {
                        eprintln!("MEM alloc-site in {} at {pc}", target.name.as_str());
                    }
                    if let Some((kind, ptr)) = traced
                        && let Value::Ptr(pointer) = frame.regs[ptr as usize]
                    {
                        let address = pointer.address();
                        eprintln!(
                            "MEM {kind} ptr={address} in {} at {pc}",
                            chunk(module, current_chunk)
                                .map(|target| target.name.as_str())
                                .unwrap_or("?")
                        );
                        // TALK_TRACE_MEM_PTR=<address>: show the site's
                        // surrounding code, the same window a trap prints.
                        if std::env::var("TALK_TRACE_MEM_PTR")
                            .is_ok_and(|filter| filter == address.to_string())
                            && let Ok(target) = chunk(module, current_chunk)
                        {
                            let start = pc.saturating_sub(10);
                            let end = (pc + 4).min(target.code.len());
                            for (offset, insn) in target.code[start..end].iter().enumerate() {
                                eprintln!("  [{}] {insn:?}", start + offset);
                            }
                        }
                    }
                }
                exec_local(module, frame, machine, local, budgets).map_err(|error| {
                    if trace_mem && let Ok(target) = chunk(module, current_chunk) {
                        let start = pc.saturating_sub(8);
                        let end = (pc + 4).min(target.code.len());
                        for (offset, insn) in target.code[start..end].iter().enumerate() {
                            eprintln!("  [{}] {insn:?}", start + offset);
                        }
                    }
                    format!(
                        "{error} [in {} (chunk {current_chunk}) at {pc}]",
                        chunk(module, current_chunk)
                            .map(|target| target.name.as_str())
                            .unwrap_or("?")
                    )
                })?
            }
        }
    }
}

/// Pop the top frame, keeping the finalizer-pump count in step — every
/// frame discarded on the abort-unwind paths shares this bookkeeping.
fn pop_frame(
    frames: &mut Vec<Frame<'_>>,
    finalizer_frames: &mut usize,
    pool: &mut Vec<Vec<Value>>,
) {
    if let Some(frame) = frames.pop() {
        if frame.dest == FINALIZER_DEST {
            *finalizer_frames = finalizer_frames.saturating_sub(1);
        }
        recycle(pool, frame.regs);
    }
}

/// Return a popped frame's register buffer to the pool: values drop
/// now (exactly as the frame drop would), the allocation survives for
/// the next call. The cap bounds idle memory.
fn recycle(pool: &mut Vec<Vec<Value>>, mut regs: Vec<Value>) {
    regs.clear();
    if pool.len() < 64 {
        pool.push(regs);
    }
}

/// Pop the returning frame and deliver `value` to its destination: a
/// finalizer frame's value is discarded (the teardown pump may resume),
/// an ordinary caller receives it in the saved dest register, and with
/// no caller left it is the program's value (returned as `Some`).
fn deliver_return(
    frames: &mut Vec<Frame<'_>>,
    finalizer_frames: &mut usize,
    pool: &mut Vec<Vec<Value>>,
    task_dests: &mut Vec<usize>,
    tasks: &mut Vec<TaskSlot>,
    value: Value,
) -> Option<Value> {
    #[allow(clippy::expect_used)]
    let dest = frames.last().expect("a frame is returning").dest;
    if let Some(frame) = frames.pop() {
        recycle(pool, frame.regs);
    }
    match frames.last_mut() {
        Some(_) if dest == FINALIZER_DEST => {
            *finalizer_frames = finalizer_frames.saturating_sub(1);
            None
        }
        Some(_) if dest == TASK_DEST => {
            if let Some(slot) = task_dests.pop()
                && let Some(entry) = tasks.get_mut(slot)
            {
                *entry = TaskSlot::Done(value);
            }
            None
        }
        Some(caller) => {
            caller.regs[dest as usize] = value;
            None
        }
        None => Some(value),
    }
}

/// Walk the abort unwind (ADR 0027) down toward the delimiter's frame:
/// for each frame from the top, look its suspension pc up in its chunk's
/// unwind table. A hit steers the frame into its unwind entry (return
/// `Ok(None)`: normal dispatch runs the drops in that frame — they may
/// make real calls — and the entry's `UnwindRet` resumes the walk). A
/// miss means nothing owned is live there: pop and continue. Reaching
/// the delimiter's frame with a miss delivers the stashed value to its
/// caller (`Ok(Some(v))` = the program's value when there is no caller).
fn advance_unwind(
    module: &Module,
    frames: &mut Vec<Frame<'_>>,
    finalizer_frames: &mut usize,
    pool: &mut Vec<Vec<Value>>,
    task_dests: &mut Vec<usize>,
    tasks: &mut Vec<TaskSlot>,
    unwinding: &mut Option<(usize, Value)>,
) -> Result<Option<Value>, String> {
    loop {
        let Some((target, _)) = *unwinding else {
            return Err("vm: unwind walk without an unwind in progress".into());
        };
        let Some(frame) = frames.last() else {
            return Err("vm: unwind walk ran out of frames".into());
        };
        let table = &chunk(module, frame.chunk)?.unwind;
        let entry = table
            .binary_search_by_key(&(frame.pc as u32), |&(suspension, _)| suspension)
            .ok()
            .map(|i| table[i].1);
        if let Some(entry_pc) = entry {
            #[allow(clippy::expect_used)]
            let top = frames.last_mut().expect("frame checked above");
            top.pc = entry_pc as usize;
            return Ok(None);
        }
        if frames.len() - 1 == target {
            #[allow(clippy::expect_used)]
            let (_, value) = unwinding.take().expect("unwinding checked above");
            return Ok(deliver_return(
                frames,
                finalizer_frames,
                pool,
                task_dests,
                tasks,
                value,
            ));
        }
        pop_frame(frames, finalizer_frames, pool);
    }
}

/// Display names for rendering values Talk-style — built upstream from
/// the checker's catalog (the machine itself only has symbols).
#[derive(Default)]
pub struct ValueNames {
    /// Struct/enum symbol → display name.
    pub types: rustc_hash::FxHashMap<Symbol, String>,
    /// Struct symbol → field names in declaration order.
    pub fields: rustc_hash::FxHashMap<Symbol, Vec<String>>,
    /// Enum symbol → case names in tag (declaration) order.
    pub cases: rustc_hash::FxHashMap<Symbol, Vec<String>>,
    /// The core String struct: its values render as quoted text read
    /// from byte memory.
    pub string_struct: Option<Symbol>,
}

/// Talk-style rendering, matching the derived-show formats:
/// `2`, `1.5`, `true`, `"hi"`, `(1, true)`, `Name(field: v…)`,
/// `Enum.case(payload…)`.
fn render_value(machine: &Machine, names: &ValueNames, value: &Value) -> Result<String, String> {
    match value {
        Value::I64(v) => Ok(v.to_string()),
        Value::F64(v) => {
            let rendered = v.to_string();
            Ok(
                if rendered.contains('.') || rendered.contains('e') || !v.is_finite() {
                    rendered
                } else {
                    format!("{rendered}.0")
                },
            )
        }
        Value::Bool(v) => Ok(v.to_string()),
        Value::Byte(v) => Ok(v.to_string()),
        Value::Void => Ok("()".to_string()),
        Value::Ptr(pointer) => Ok(format!("RawPtr({})", pointer.address())),
        Value::Agg(layout, slots) => render_agg(machine, names, *layout, slots),
        Value::Existential(payload, _) => render_value(machine, names, payload),
        Value::Closure(..) => Ok("<func>".to_string()),
        Value::Cell(_) => Ok("<cell>".to_string()),
        Value::Cont(..) => Ok("<continuation>".to_string()),
        // Shallow: structural rendering would cycle through the graph.
        Value::Object(object) => Ok(format!("<object #{object}>")),
    }
}

/// Render a flat aggregate through its published layout: the descriptor
/// says where each field lives and what identity to display — static
/// type information at the point of the value, not headers recovered
/// from it (ADR 0045).
fn render_agg(
    machine: &Machine,
    names: &ValueNames,
    layout: u32,
    slots: &[Value],
) -> Result<String, String> {
    let desc = machine
        .layouts
        .get(layout as usize)
        .ok_or("vm: render of an unknown layout")?;
    if desc.symbol.is_some()
        && desc.symbol == names.string_struct
        && let Some((base, len)) = string_bytes(slots)
    {
        let bytes = machine.string_display_bytes(base, len)?;
        return Ok(format!(
            "\"{}\"",
            escape_string(&String::from_utf8_lossy(bytes))
        ));
    }
    let type_name = |symbol: &Symbol| {
        names
            .types
            .get(symbol)
            .cloned()
            .unwrap_or_else(|| symbol.to_string())
    };
    match &desc.body {
        LayoutBody::Product(fields) => {
            let field_names = desc
                .symbol
                .as_ref()
                .and_then(|symbol| names.fields.get(symbol));
            let rendered: Vec<String> = fields
                .iter()
                .enumerate()
                .map(|(index, &(offset, shape))| {
                    let field = read_slots(&machine.layouts, slots, offset, shape)?;
                    let value = render_value(machine, names, &field)?;
                    Ok(match field_names.and_then(|fields| fields.get(index)) {
                        Some(field_name) => format!("{field_name}: {value}"),
                        None => value,
                    })
                })
                .collect::<Result<_, String>>()?;
            Ok(match &desc.symbol {
                Some(symbol) => format!("{}({})", type_name(symbol), rendered.join(", ")),
                None => format!("({})", rendered.join(", ")),
            })
        }
        LayoutBody::Sum(variants) => {
            let Some(Value::I64(tag)) = slots.first() else {
                return Err("vm: flat sum without a tag".into());
            };
            let payloads = variants
                .get(usize::try_from(*tag).unwrap_or(usize::MAX))
                .ok_or("vm: flat sum tag out of range")?;
            let symbol = desc
                .symbol
                .as_ref()
                .ok_or("vm: flat sum without identity")?;
            let name = type_name(symbol);
            let case = names
                .cases
                .get(symbol)
                .and_then(|cases| cases.get(usize::try_from(*tag).unwrap_or(usize::MAX)))
                .cloned()
                .unwrap_or_else(|| format!("case{tag}"));
            if payloads.is_empty() {
                Ok(format!("{name}.{case}"))
            } else {
                let rendered: Vec<String> = payloads
                    .iter()
                    .map(|&(offset, shape)| {
                        let payload = read_slots(&machine.layouts, slots, offset, shape)?;
                        render_value(machine, names, &payload)
                    })
                    .collect::<Result<_, _>>()?;
                Ok(format!("{name}.{case}({})", rendered.join(", ")))
            }
        }
        LayoutBody::Unshaped => Err("vm: render of an unshaped layout".into()),
    }
}

fn string_bytes(field_values: &[Value]) -> Option<(Pointer, i64)> {
    match field_values {
        [Value::Ptr(base), Value::I64(len), ..] => Some((*base, *len)),
        _ => None,
    }
}

/// Build one flat aggregate: a `Void`-filled slot vector of the layout's
/// width, the tag stamped into slot 0 for sums, and each argument written
/// through its field's (offset, shape).
fn build_agg(
    layouts: &[LayoutDesc],
    layout: u32,
    tag: u16,
    args: Vec<Value>,
) -> Result<Value, String> {
    let desc = layouts
        .get(layout as usize)
        .ok_or("vm: construction of an unknown layout")?;
    let mut slots = vec![Value::Void; usize::from(desc.width)];
    let fields = match &desc.body {
        LayoutBody::Product(fields) => {
            if tag != 0 {
                return Err("vm: construction does not match its layout".into());
            }
            fields
        }
        LayoutBody::Sum(variants) => {
            *slots
                .get_mut(0)
                .ok_or("vm: sum layout without a tag slot")? = Value::I64(i64::from(tag));
            variants
                .get(usize::from(tag))
                .ok_or("vm: construction tag out of range")?
        }
        LayoutBody::Unshaped => {
            return Err("vm: construction of an unshaped layout".into());
        }
    };
    if fields.len() != args.len() {
        return Err("vm: construction arity does not match its layout".into());
    }
    for (&(offset, shape), value) in fields.iter().zip(args) {
        write_slots(layouts, &mut slots, offset, shape, value)?;
    }
    Ok(Value::Agg(layout, Rc::new(slots)))
}

/// Write one field into a flat slot vector: a slot field takes the value
/// as-is; a spliced field flattens the child aggregate across its span.
fn write_slots(
    layouts: &[LayoutDesc],
    slots: &mut [Value],
    offset: u16,
    shape: FieldShape,
    value: Value,
) -> Result<(), String> {
    match shape {
        FieldShape::Slot => {
            *slots
                .get_mut(usize::from(offset))
                .ok_or("vm: field offset out of range")? = value;
            Ok(())
        }
        FieldShape::Spliced(child) => flatten_into(layouts, slots, offset, child, value),
    }
}

/// Splice one aggregate value flat into `slots[offset..offset+width]`.
/// A flat child of the right layout copies its slots; `Void` leaves the
/// span blank (a declared-blank init receiver).
fn flatten_into(
    layouts: &[LayoutDesc],
    slots: &mut [Value],
    offset: u16,
    child: u32,
    value: Value,
) -> Result<(), String> {
    let desc = layouts
        .get(child as usize)
        .ok_or("vm: spliced field of an unknown layout")?;
    let start = usize::from(offset);
    let total = slots.len();
    let span = slots.get_mut(start..start + usize::from(desc.width)).ok_or_else(|| {
        format!(
            "vm: spliced field out of range (child layout {child} width {} at offset {start}, container has {total} slots)",
            desc.width,
        )
    })?;
    match value {
        Value::Agg(id, child_slots) if id == child => {
            span.clone_from_slice(&child_slots);
            Ok(())
        }
        // A blank cell (`Inst::Blank`): the spliced child too is all-Void
        // until the initializer assigns it.
        Value::Void => Ok(()),
        _ => Err("vm: spliced value does not match its layout".into()),
    }
}

/// Read one field of a flat aggregate: a slot field clones its slot; a
/// spliced field reconstitutes the child aggregate from its span.
fn read_slots(
    layouts: &[LayoutDesc],
    slots: &[Value],
    offset: u16,
    shape: FieldShape,
) -> Result<Value, String> {
    match shape {
        FieldShape::Slot => slots
            .get(usize::from(offset))
            .cloned()
            .ok_or_else(|| "vm: field offset out of range".into()),
        FieldShape::Spliced(child) => {
            let width = layouts
                .get(child as usize)
                .ok_or("vm: spliced field of an unknown layout")?
                .width;
            let start = usize::from(offset);
            let span = slots.get(start..start + usize::from(width)).ok_or_else(|| {
                format!(
                    "vm: spliced field out of range (child layout {child} width {width} at offset {start}, container has {} slots)",
                    slots.len(),
                )
            })?;
            Ok(Value::Agg(child, Rc::new(span.to_vec())))
        }
    }
}

/// Resolve a logical field index against a flat aggregate's descriptor:
/// products index their field list, sums read the live tag from slot 0
/// and index that variant's payload.
fn field_site(
    layouts: &[LayoutDesc],
    layout: u32,
    slots: &[Value],
    index: u16,
) -> Result<(u16, FieldShape), String> {
    let desc = layouts
        .get(layout as usize)
        .ok_or("vm: field read of an unknown layout")?;
    let field = match &desc.body {
        LayoutBody::Product(fields) => fields.get(usize::from(index)),
        LayoutBody::Sum(variants) => {
            let Some(Value::I64(tag)) = slots.first() else {
                return Err("vm: flat sum without a tag".into());
            };
            let variant = usize::try_from(*tag).map_err(|_| "vm: flat sum tag out of range")?;
            variants
                .get(variant)
                .ok_or("vm: flat sum tag out of range")?
                .get(usize::from(index))
        }
        LayoutBody::Unshaped => return Err("vm: field read of an unshaped layout".into()),
    };
    field
        .copied()
        .ok_or_else(|| "vm: field index out of range".into())
}

fn escape_string(text: &str) -> String {
    let mut out = String::with_capacity(text.len());
    for ch in text.chars() {
        match ch {
            '\\' => out.push_str("\\\\"),
            '"' => out.push_str("\\\""),
            '\n' => out.push_str("\\n"),
            '\t' => out.push_str("\\t"),
            '\r' => out.push_str("\\r"),
            other => out.push(other),
        }
    }
    out
}

/// Machine state outside the frames: the cell arena, byte memory, and the
/// IO boundary.
struct Machine<'io> {
    slots: Vec<Value>,
    mem: Vec<u8>,
    static_len: u32,
    /// The module's published layout table, kept on the machine so
    /// rendering can read flat aggregates after the run (the module
    /// reference itself does not outlive `run_loop`).
    layouts: Vec<LayoutDesc>,
    /// Complete immutable String values, interned on first execution.
    /// Their slot vectors are shared by every evaluation of an equal
    /// `(offset, length, layout)` literal.
    static_strings: FxHashMap<(u32, u32, u32), Value>,
    allocations: Allocations,
    /// Aggregates stored in raw memory live here; the memory cell holds an
    /// 8-byte index into this arena (Leroy, POPL 1992's mixed
    /// representation — scalars unboxed, aggregates behind a handle).
    boxed: Vec<Value>,
    /// Region-allocated `'heap` objects (see `objects.rs`).
    objects: Objects<Value>,
    /// Spawned tasks by handle (ADR 0058). On thread-capable hosts a
    /// slot holds the worker's join handle; on single-threaded hosts
    /// (wasm32) the task ran at the spawn site and the slot holds its
    /// output. A join empties the slot exactly once.
    tasks: Vec<TaskSlot>,
    /// The module wrapped for sharing with worker threads, created on
    /// the first spawn (one clone per spawning program; workers then
    /// share it by reference).
    shared_module: Option<std::sync::Arc<Module>>,
    /// Channel handles THIS worker holds a live external-wake
    /// registration on (pending receives per ADR 0059, pending bounded
    /// sends per ADR 0062; `true` marks a send-wait): the executor may
    /// park only while this is nonempty — otherwise a poll round that
    /// wakes nothing is a real deadlock — and a park sleeps only after
    /// confirming, under the registry lock, that no registration is
    /// already satisfiable (no lost wakes). A receive-wait is satisfied
    /// by a value or a close; a send-wait by room or receiver death.
    external: Vec<(i64, bool)>,
    /// Absolute monotonic-ms deadlines THIS worker's sleeping futures
    /// registered (ADR 0063): each is a reason to park, and the park
    /// waits only until the earliest of them.
    deadlines: Vec<i64>,
    io: &'io mut dyn IO,
}

fn record_id(pointer: Pointer) -> Result<u32, String> {
    pointer
        .transfer_id()
        .ok_or_else(|| "vm: a static pointer has no allocation record".into())
}

/// One channel's cross-worker state (ADR 0059). The registry is
/// process-global — channels are the one object that outlives a single
/// machine, carrying transfer packets between isolated workers. A slot
/// frees when both sides are gone; handles are runtime-minted and a
/// stale handle finds an empty slot, never another live channel's
/// state, within one program run.
struct VmChannel {
    /// 0 = unbounded; otherwise queued + reserved never exceeds it.
    capacity: usize,
    /// Send slots claimed by an in-flight `SendFuture` poll (ADR 0062).
    /// Reserve and send happen inside one poll body, so a reservation
    /// never outlives a poll — but racing reservers must see each
    /// other's claims, which is what makes the bound hard.
    reserved: usize,
    queue: std::collections::VecDeque<Transfer>,
    senders: u32,
    receiver_live: bool,
}

/// Monotonic milliseconds from an arbitrary per-process anchor
/// (ADR 0063). Wall-clock time is host-effect territory; deadlines only
/// care about deltas.
fn now_ms() -> i64 {
    #[cfg(not(target_arch = "wasm32"))]
    {
        static START: std::sync::OnceLock<std::time::Instant> = std::sync::OnceLock::new();
        let start = START.get_or_init(std::time::Instant::now);
        i64::try_from(start.elapsed().as_millis()).unwrap_or(i64::MAX)
    }
    #[cfg(target_arch = "wasm32")]
    {
        js_sys::Date::now() as i64
    }
}

fn channels() -> &'static (
    std::sync::Mutex<Vec<Option<VmChannel>>>,
    std::sync::Condvar,
) {
    static CHANNELS: std::sync::OnceLock<(
        std::sync::Mutex<Vec<Option<VmChannel>>>,
        std::sync::Condvar,
    )> = std::sync::OnceLock::new();
    CHANNELS.get_or_init(|| (std::sync::Mutex::new(Vec::new()), std::sync::Condvar::new()))
}

fn channels_locked()
-> std::sync::MutexGuard<'static, Vec<Option<VmChannel>>> {
    match channels().0.lock() {
        Ok(guard) => guard,
        Err(poisoned) => poisoned.into_inner(),
    }
}

/// Scalar channel/park control (ADR 0059). Ops: 0 status (0 value
/// ready, 1 empty and open, 2 closed and drained), 1 retain sender,
/// 2 drop sender, 3 drop receiver, 4 register an external wait,
/// 5 unregister, 6 park, 7 create (the handle operand carries the
/// capacity; 0 = unbounded), 8 count this worker's external waits,
/// 9 whether the receiver is still live, 10 atomically reserve a send
/// slot (1 on success), 11 register a send-wait, 12 unregister one,
/// 13 monotonic now (ms), 14 register a deadline (the handle operand,
/// absolute ms), 15 unregister one, 17 non-reserving send-room probe.
fn chan_ctl(machine: &mut Machine, handle: i64, op: i64) -> Result<i64, String> {
    let slot_index = usize::try_from(handle).ok();
    match op {
        0 => {
            let mut registry = channels_locked();
            let slot = slot_index
                .and_then(|slot| registry.get_mut(slot))
                .and_then(Option::as_mut)
                .ok_or("vm: status of an invalid channel handle")?;
            Ok(if !slot.queue.is_empty() {
                0
            } else if slot.senders == 0 {
                2
            } else {
                1
            })
        }
        1 | 2 | 3 => {
            let mut registry = channels_locked();
            let index =
                slot_index.ok_or("vm: side change on an invalid channel handle")?;
            let slot = registry
                .get_mut(index)
                .and_then(Option::as_mut)
                .ok_or("vm: side change on an invalid channel handle")?;
            match op {
                1 => slot.senders += 1,
                2 => slot.senders = slot.senders.saturating_sub(1),
                _ => slot.receiver_live = false,
            }
            let closed = slot.senders == 0;
            let dead = closed && !slot.receiver_live;
            if dead {
                registry[index] = None;
            }
            drop(registry);
            if closed {
                // The last sender's departure is a wake: parked
                // receivers must observe the close.
                channels().1.notify_all();
            }
            Ok(0)
        }
        4 | 11 => {
            machine.external.push((handle, op == 11));
            Ok(0)
        }
        5 | 12 => {
            let is_send = op == 12;
            if let Some(found) = machine
                .external
                .iter()
                .position(|&entry| entry == (handle, is_send))
            {
                machine.external.swap_remove(found);
            }
            Ok(0)
        }
        6 => {
            if machine.external.is_empty() && machine.deadlines.is_empty() {
                return Ok(0);
            }
            #[cfg(any(not(target_arch = "wasm32"), target_feature = "atomics"))]
            {
                // Check-then-park under the registry lock: a send or
                // close that raced the caller's status poll already
                // made a registered channel ready, so sleeping would
                // lose that wake. Only a confirmed not-ready state may
                // wait; spurious wakes are fine — the executor re-polls
                // and re-parks.
                let guard = channels_locked();
                let ready = machine.external.iter().any(|&(entry, is_send)| {
                    match usize::try_from(entry)
                        .ok()
                        .and_then(|slot| guard.get(slot))
                    {
                        Some(Some(slot)) if is_send => {
                            !slot.receiver_live
                                || slot.queue.len() + slot.reserved
                                    < slot.capacity
                        }
                        Some(Some(slot)) => {
                            !slot.queue.is_empty() || slot.senders == 0
                        }
                        _ => true,
                    }
                });
                if !ready {
                    // A registered deadline bounds the sleep: the wake
                    // for a timer IS the timeout elapsing.
                    match machine.deadlines.iter().min() {
                        Some(&earliest) => {
                            let wait = earliest.saturating_sub(now_ms());
                            if wait > 0 {
                                let _guard = match channels().1.wait_timeout(
                                    guard,
                                    std::time::Duration::from_millis(wait as u64),
                                ) {
                                    Ok(woken) => woken.0,
                                    Err(poisoned) => poisoned.into_inner().0,
                                };
                            }
                        }
                        None => {
                            let _guard = match channels().1.wait(guard) {
                                Ok(guard) => guard,
                                Err(poisoned) => poisoned.into_inner(),
                            };
                        }
                    }
                }
                Ok(0)
            }
            #[cfg(all(target_arch = "wasm32", not(target_feature = "atomics")))]
            {
                // A single-threaded host sleeping IS a blocked thread:
                // spin out the earliest deadline. With no deadline
                // nothing can ever wake this park.
                match machine.deadlines.iter().min() {
                    Some(&earliest) => {
                        while now_ms() < earliest {}
                        Ok(0)
                    }
                    None => Err(
                        "vm: parked with no thread able to wake this task (deadlock)"
                            .into(),
                    ),
                }
            }
        }
        8 => Ok((machine.external.len() + machine.deadlines.len()) as i64),
        13 => Ok(now_ms()),
        14 => {
            machine.deadlines.push(handle);
            Ok(0)
        }
        15 => {
            if let Some(found) =
                machine.deadlines.iter().position(|&entry| entry == handle)
            {
                machine.deadlines.swap_remove(found);
            }
            Ok(0)
        }
        9 => {
            let mut registry = channels_locked();
            let slot = slot_index
                .and_then(|slot| registry.get_mut(slot))
                .and_then(Option::as_mut)
                .ok_or("vm: liveness of an invalid channel handle")?;
            Ok(i64::from(slot.receiver_live))
        }
        10 => {
            let mut registry = channels_locked();
            let slot = slot_index
                .and_then(|slot| registry.get_mut(slot))
                .and_then(Option::as_mut)
                .ok_or("vm: reserve on an invalid channel handle")?;
            if slot.capacity == 0 {
                return Ok(1);
            }
            if slot.queue.len() + slot.reserved < slot.capacity {
                slot.reserved += 1;
                Ok(1)
            } else {
                Ok(0)
            }
        }
        17 => {
            // Non-reserving room probe (ADR 0067): would a parked
            // sender wake? The resumed send claims its own reservation.
            let mut registry = channels_locked();
            let slot = slot_index
                .and_then(|slot| registry.get_mut(slot))
                .and_then(Option::as_mut)
                .ok_or("vm: probe on an invalid channel handle")?;
            let ready = !slot.receiver_live
                || slot.capacity == 0
                || slot.queue.len() + slot.reserved < slot.capacity;
            Ok(i64::from(ready))
        }
        7 => {
            let mut registry = channels_locked();
            let fresh = VmChannel {
                capacity: usize::try_from(handle).unwrap_or(0),
                reserved: 0,
                queue: std::collections::VecDeque::new(),
                senders: 1,
                receiver_live: true,
            };
            if let Some(free) = registry.iter().position(Option::is_none) {
                registry[free] = Some(fresh);
                Ok(free as i64)
            } else {
                registry.push(Some(fresh));
                Ok((registry.len() - 1) as i64)
            }
        }
        _ => Err("vm: unknown channel control operation".into()),
    }
}

/// One spawned task's state in `Machine::tasks`.
enum TaskSlot {
    /// A worker thread is (or may still be) running the task.
    #[cfg(any(not(target_arch = "wasm32"), target_feature = "atomics"))]
    Running(thread::JoinHandle<Result<(Transfer, Vec<u8>, Vec<u8>), String>>),
    /// Awaiting the spawn-site task frame's return (single-threaded
    /// reference executor; never constructed on thread-capable hosts).
    #[cfg_attr(any(not(target_arch = "wasm32"), target_feature = "atomics"), allow(dead_code))]
    Pending,
    /// The output, ready for its join.
    Done(Value),
    /// Already joined.
    Joined,
}

/// A machine-independent image of a `Send`-checked value crossing a
/// worker boundary (ADR 0058): plain owned data — `Send` even though VM
/// values are not — with buffers deduplicated through a table so storage
/// shared WITHIN the transferred value stays shared (and balanced) on
/// the other side.
#[derive(Debug)]
struct Transfer {
    root: Packet,
    buffers: Vec<BufferImage>,
}

#[derive(Debug)]
enum Packet {
    I64(i64),
    F64(f64),
    Bool(bool),
    Byte(u8),
    Void,
    Agg(u32, Vec<Packet>),
    Existential(Box<Packet>, Vec<Packet>),
    Closure(u32, Vec<Packet>),
    /// A pointer into static memory: identical in every machine sharing
    /// the module.
    StaticPtr(u32),
    /// A pointer into buffer `table`, `offset` bytes past its base.
    Buffer { table: usize, offset: u32 },
}

/// One buffer's contents, interpreted through the element kind its
/// typed stores recorded (a `Storage<Element>` buffer is uniform).
#[derive(Debug)]
enum BufferImage {
    /// Scalar elements (or a never-stored buffer): verbatim bytes.
    Bytes(Vec<u8>),
    /// `MemKind::Ptr` elements: nonzero words, sparse by word index.
    Ptrs { len: usize, words: Vec<(usize, Packet)> },
    /// `MemKind::Boxed` elements: the referenced boxed values, sparse
    /// by word index.
    Boxed { len: usize, words: Vec<(usize, Packet)> },
}

/// Serialization state: buffers already imaged (by allocation id) and
/// the in-flight set that turns a cyclic buffer graph into a clean
/// error (Send-checked values are acyclic; bytecode is not trusted).
#[derive(Default)]
struct TransferOut {
    buffers: Vec<BufferImage>,
    by_id: rustc_hash::FxHashMap<u32, usize>,
    in_flight: rustc_hash::FxHashSet<u32>,
}

impl Machine<'_> {
    /// The exit balance for a finished run's result value.
    /// Image a `Send`-checked value for a worker boundary (ADR 0058).
    /// Buffer interiors are interpreted through the element kind their
    /// typed stores recorded; a buffer with conflicting stores, or a
    /// value kind that cannot leave its machine (cells, `'heap` objects,
    /// continuations), refuses cleanly — the type system prevents these,
    /// and untrusted bytecode gets an error, never a wrong transfer.
    fn serialize_transfer(&self, value: &Value) -> Result<Transfer, String> {
        let mut out = TransferOut::default();
        let root = self.serialize_value(value, &mut out)?;
        Ok(Transfer {
            root,
            buffers: out.buffers,
        })
    }

    fn serialize_value(&self, value: &Value, out: &mut TransferOut) -> Result<Packet, String> {
        Ok(match value {
            Value::I64(v) => Packet::I64(*v),
            Value::F64(v) => Packet::F64(*v),
            Value::Bool(v) => Packet::Bool(*v),
            Value::Byte(v) => Packet::Byte(*v),
            Value::Void => Packet::Void,
            Value::Agg(layout, items) => {
                let mut packed = Vec::with_capacity(items.len());
                for item in items.iter() {
                    packed.push(self.serialize_value(item, out)?);
                }
                Packet::Agg(*layout, packed)
            }
            Value::Existential(payload, witnesses) => {
                let payload = self.serialize_value(payload, out)?;
                let mut packed = Vec::with_capacity(witnesses.len());
                for witness in witnesses.iter() {
                    packed.push(self.serialize_value(witness, out)?);
                }
                Packet::Existential(Box::new(payload), packed)
            }
            Value::Closure(chunk, env) => {
                let mut packed = Vec::with_capacity(env.len());
                for captured in env.iter() {
                    packed.push(self.serialize_value(captured, out)?);
                }
                Packet::Closure(*chunk, packed)
            }
            Value::Ptr(pointer) => {
                if pointer.is_static() {
                    return Ok(Packet::StaticPtr(pointer.address()));
                }
                let record = self
                    .allocations
                    .live_record(*pointer)
                    .ok_or("vm: a dangling buffer reached a task boundary")?;
                let id = record_id(*pointer)?;
                let offset = pointer.address() - record.start;
                if let Some(&table) = out.by_id.get(&id) {
                    return Ok(Packet::Buffer {
                        table,
                        offset,
                    });
                }
                if !out.in_flight.insert(id) {
                    return Err("vm: a cyclic buffer graph cannot cross a task boundary".into());
                }
                let record = record.clone();
                let image = self.serialize_buffer(&record, out)?;
                out.in_flight.remove(&id);
                let table = out.buffers.len();
                out.buffers.push(image);
                out.by_id.insert(id, table);
                Packet::Buffer { table, offset }
            }
            Value::Cell(_) | Value::Object(_) | Value::Cont(..) => {
                return Err(
                    "vm: a value of this kind cannot cross a task boundary".into(),
                );
            }
        })
    }

    fn serialize_buffer(
        &self,
        record: &crate::memory::AllocationRecord,
        out: &mut TransferOut,
    ) -> Result<BufferImage, String> {
        if record.mixed {
            return Err(
                "vm: a buffer with mixed element kinds cannot cross a task boundary".into(),
            );
        }
        let start = record.start as usize;
        let bytes = self
            .mem
            .get(start..start + record.len)
            .ok_or("vm: buffer out of bounds at a task boundary")?;
        match record.stored {
            None
            | Some(MemKind::Byte)
            | Some(MemKind::I64)
            | Some(MemKind::F64)
            | Some(MemKind::Bool) => Ok(BufferImage::Bytes(bytes.to_vec())),
            Some(MemKind::Ptr) => {
                let mut words = Vec::new();
                for (index, chunk) in bytes.chunks_exact(8).enumerate() {
                    let word = u64::from_le_bytes(chunk.try_into().expect("8-byte chunk"));
                    if word == 0 {
                        continue;
                    }
                    let value = Value::Ptr(Pointer::decode(word));
                    words.push((index, self.serialize_value(&value, out)?));
                }
                Ok(BufferImage::Ptrs {
                    len: record.len,
                    words,
                })
            }
            Some(MemKind::Boxed) => {
                let mut words = Vec::new();
                for (index, chunk) in bytes.chunks_exact(8).enumerate() {
                    let word = u64::from_le_bytes(chunk.try_into().expect("8-byte chunk")) as usize;
                    if word == 0 {
                        continue;
                    }
                    let boxed = self
                        .boxed
                        .get(word)
                        .ok_or("vm: a buffer references a missing boxed value")?;
                    words.push((index, self.serialize_value(boxed, out)?));
                }
                Ok(BufferImage::Boxed {
                    len: record.len,
                    words,
                })
            }
        }
    }

    /// Release the parent's copy of a transferred value: the worker owns
    /// the image now, so every buffer reference the value tree held is
    /// freed here — the walk mirrors the serializer, and when a buffer's
    /// last owner goes, its interior references release too (the same
    /// element-wise release the program's drop glue would have done).
    fn release_transferred(&mut self, value: &Value) -> Result<(), String> {
        match value {
            Value::I64(_) | Value::F64(_) | Value::Bool(_) | Value::Byte(_) | Value::Void => Ok(()),
            Value::Agg(_, items) => {
                for item in items.iter() {
                    self.release_transferred(item)?;
                }
                Ok(())
            }
            Value::Existential(payload, witnesses) => {
                self.release_transferred(payload)?;
                for witness in witnesses.iter() {
                    self.release_transferred(witness)?;
                }
                Ok(())
            }
            Value::Closure(_, env) => {
                for captured in env.iter() {
                    self.release_transferred(captured)?;
                }
                Ok(())
            }
            Value::Ptr(pointer) => {
                if pointer.is_static() {
                    return Ok(());
                }
                let Some(record) = self.allocations.live_record(*pointer) else {
                    return Err("vm: a dangling buffer reached a task boundary".into());
                };
                // Collect the interior references BEFORE the free: the
                // span may be recycled the moment the record dies.
                let mut interior: Vec<Value> = Vec::new();
                if record.rc == 1 && !record.mixed {
                    let start = record.start as usize;
                    let len = record.len;
                    match record.stored {
                        Some(MemKind::Ptr) => {
                            for chunk in self.mem[start..start + len].chunks_exact(8) {
                                let word =
                                    u64::from_le_bytes(chunk.try_into().expect("8-byte chunk"));
                                if word != 0 {
                                    interior.push(Value::Ptr(Pointer::decode(word)));
                                }
                            }
                        }
                        Some(MemKind::Boxed) => {
                            for chunk in self.mem[start..start + len].chunks_exact(8) {
                                let word = u64::from_le_bytes(
                                    chunk.try_into().expect("8-byte chunk"),
                                ) as usize;
                                if word != 0
                                    && let Some(boxed) = self.boxed.get(word)
                                {
                                    interior.push(boxed.clone());
                                }
                            }
                        }
                        _ => {}
                    }
                }
                self.allocations
                    .free(self.static_len, *pointer)
                    .map_err(|error| format!("vm: releasing a transferred buffer: {error:?}"))?;
                for value in interior {
                    self.release_transferred(&value)?;
                }
                Ok(())
            }
            Value::Cell(_) | Value::Object(_) | Value::Cont(..) => {
                Err("vm: a value of this kind cannot cross a task boundary".into())
            }
        }
    }

    /// Rebuild a transferred value in THIS machine: buffers materialize
    /// once and later references retain, so sharing and balance inside
    /// the transferred tree survive the crossing.
    fn deserialize_transfer(&mut self, transfer: &Transfer) -> Result<Value, String> {
        let mut bases: Vec<Option<Pointer>> = vec![None; transfer.buffers.len()];
        self.deserialize_packet(&transfer.root, &transfer.buffers, &mut bases)
    }

    fn deserialize_packet(
        &mut self,
        packet: &Packet,
        buffers: &[BufferImage],
        bases: &mut Vec<Option<Pointer>>,
    ) -> Result<Value, String> {
        Ok(match packet {
            Packet::I64(v) => Value::I64(*v),
            Packet::F64(v) => Value::F64(*v),
            Packet::Bool(v) => Value::Bool(*v),
            Packet::Byte(v) => Value::Byte(*v),
            Packet::Void => Value::Void,
            Packet::Agg(layout, items) => {
                let mut values = Vec::with_capacity(items.len());
                for item in items {
                    values.push(self.deserialize_packet(item, buffers, bases)?);
                }
                Value::Agg(*layout, Rc::new(values))
            }
            Packet::Existential(payload, witnesses) => {
                let payload = self.deserialize_packet(payload, buffers, bases)?;
                let mut values = Vec::with_capacity(witnesses.len());
                for witness in witnesses {
                    values.push(self.deserialize_packet(witness, buffers, bases)?);
                }
                Value::Existential(Rc::new(payload), Rc::new(values))
            }
            Packet::Closure(chunk, env) => {
                let mut values = Vec::with_capacity(env.len());
                for captured in env {
                    values.push(self.deserialize_packet(captured, buffers, bases)?);
                }
                Value::Closure(*chunk, Rc::new(values))
            }
            Packet::StaticPtr(address) => Value::Ptr(Pointer::static_at(*address)),
            Packet::Buffer { table, offset } => {
                let base = match bases.get(*table).copied().flatten() {
                    Some(base) => {
                        // Every reference past the first is another owner.
                        self.allocations
                            .retain(self.static_len, base)
                            .map_err(|error| format!("vm: retaining a transferred buffer: {error:?}"))?;
                        base
                    }
                    None => self.materialize_buffer(*table, buffers, bases)?,
                };
                let pointer = base
                    .checked_add(*offset as usize)
                    .ok_or("vm: transferred pointer offset overflow")?;
                Value::Ptr(pointer)
            }
        })
    }

    fn materialize_buffer(
        &mut self,
        table: usize,
        buffers: &[BufferImage],
        bases: &mut Vec<Option<Pointer>>,
    ) -> Result<Pointer, String> {
        let image = buffers
            .get(table)
            .ok_or("vm: transferred buffer index out of range")?;
        let len = match image {
            BufferImage::Bytes(bytes) => bytes.len(),
            BufferImage::Ptrs { len, .. } | BufferImage::Boxed { len, .. } => *len,
        };
        let base = self
            .allocations
            .allocate(&mut self.mem, len)
            .map_err(|error| format!("vm: allocating a transferred buffer: {error:?}"))?;
        bases[table] = Some(base);
        let start = base.address() as usize;
        // A recycled span carries stale bytes; the image is authoritative.
        self.mem[start..start + len].fill(0);
        match image {
            BufferImage::Bytes(bytes) => {
                self.mem[start..start + len].copy_from_slice(bytes);
            }
            BufferImage::Ptrs { words, .. } => {
                for (index, packet) in words {
                    let value = self.deserialize_packet(packet, buffers, bases)?;
                    let Value::Ptr(pointer) = value else {
                        return Err("vm: a pointer buffer image holds a non-pointer".into());
                    };
                    let slot = start + index * 8;
                    self.mem[slot..slot + 8].copy_from_slice(&pointer.encode().to_le_bytes());
                }
                if let Some(record) = self.allocations.transfer_record_mut(base) {
                    record.stored = Some(MemKind::Ptr);
                }
            }
            BufferImage::Boxed { words, .. } => {
                for (index, packet) in words {
                    let value = self.deserialize_packet(packet, buffers, bases)?;
                    self.boxed.push(value);
                    let handle = (self.boxed.len() - 1) as u64;
                    let slot = start + index * 8;
                    self.mem[slot..slot + 8].copy_from_slice(&handle.to_le_bytes());
                }
                if let Some(record) = self.allocations.transfer_record_mut(base) {
                    record.stored = Some(MemKind::Boxed);
                }
            }
        }
        Ok(base)
    }

    fn balance(&self, value: &Value) -> RunBalance {
        let (result_allocations, result_objects, result_exact) = self.result_footprint(value);
        RunBalance {
            live_allocations: self.allocations.live_count(),
            live_objects: self.objects.live_objects(),
            result_allocations,
            result_objects,
            result_exact,
        }
    }

    /// (allocation records, `'heap` objects, exactness) the program's
    /// result value legitimately holds at exit: interior pointers resolve
    /// to their owning records; a held object handle keeps its whole
    /// region live. Buffer interiors are read through the element kind
    /// their typed stores recorded (ADR 0058): scalar bytes own nothing,
    /// pointer words and boxed handles recurse. Only a buffer whose
    /// stores conflicted stays opaque and flips exactness off (see
    /// [`RunBalance::result_exact`]).
    fn result_footprint(&self, value: &Value) -> (usize, usize, bool) {
        use std::collections::BTreeSet;
        let mut bases: BTreeSet<u32> = BTreeSet::new();
        let mut objects: BTreeSet<u32> = BTreeSet::new();
        let mut cells: BTreeSet<usize> = BTreeSet::new();
        let mut exact = true;
        let mut stack: Vec<Value> = vec![value.clone()];
        while let Some(value) = stack.pop() {
            match value {
                Value::Ptr(pointer) => {
                    if let Some(record) = self.allocations.live_record(pointer)
                        && bases.insert(record.start)
                    {
                        // The element kind its typed stores recorded (ADR
                        // 0058) makes the interior walkable: scalar bytes
                        // own nothing further, pointer words and boxed
                        // handles recurse. Only a buffer with conflicting
                        // stores stays opaque.
                        if record.mixed {
                            exact = false;
                            continue;
                        }
                        let start = record.start as usize;
                        let Some(bytes) = self.mem.get(start..start + record.len) else {
                            exact = false;
                            continue;
                        };
                        match record.stored {
                            None
                            | Some(MemKind::Byte)
                            | Some(MemKind::I64)
                            | Some(MemKind::F64)
                            | Some(MemKind::Bool) => {}
                            Some(MemKind::Ptr) => {
                                for chunk in bytes.chunks_exact(8) {
                                    let word = u64::from_le_bytes(
                                        chunk.try_into().expect("8-byte chunk"),
                                    );
                                    if word != 0 {
                                        stack.push(Value::Ptr(Pointer::decode(word)));
                                    }
                                }
                            }
                            Some(MemKind::Boxed) => {
                                for chunk in bytes.chunks_exact(8) {
                                    let word = u64::from_le_bytes(
                                        chunk.try_into().expect("8-byte chunk"),
                                    ) as usize;
                                    if word != 0
                                        && let Some(boxed) = self.boxed.get(word)
                                    {
                                        stack.push(boxed.clone());
                                    }
                                }
                            }
                        }
                    }
                }
                Value::Agg(_, items) => {
                    stack.extend(items.iter().cloned());
                }
                Value::Existential(payload, witnesses) => {
                    stack.push((*payload).clone());
                    stack.extend(witnesses.iter().cloned());
                }
                Value::Closure(_, env) => stack.extend(env.iter().cloned()),
                Value::Cell(index) => {
                    if cells.insert(index)
                        && let Some(slot) = self.slots.get(index)
                    {
                        stack.push(slot.clone());
                    }
                }
                Value::Object(handle) => {
                    for member in self.objects.region_live_members(handle) {
                        if objects.insert(member)
                            && let Some(record) = self.objects.records.get(&member)
                        {
                            stack.extend(record.fields.iter().cloned());
                            if let Some(finalizer) = &record.finalizer {
                                stack.push(finalizer.clone());
                            }
                        }
                    }
                }
                Value::I64(_)
                | Value::F64(_)
                | Value::Bool(_)
                | Value::Byte(_)
                | Value::Void
                | Value::Cont(..) => {}
            }
        }
        (bases.len(), objects.len(), exact)
    }

    fn read_word(&self, pointer: Pointer) -> Result<u64, String> {
        self.check_access(pointer, 8, "load")?;
        let start = pointer.address() as usize;
        let bytes = self
            .mem
            .get(start..start + 8)
            .ok_or("vm: load out of bounds")?;
        let mut buf = [0u8; 8];
        buf.copy_from_slice(bytes);
        Ok(u64::from_le_bytes(buf))
    }

    fn load_value(&self, pointer: Pointer, kind: MemKind) -> Result<Value, String> {
        match kind {
            MemKind::Byte => Ok(Value::Byte({
                self.check_access(pointer, 1, "load")?;
                self.mem
                    .get(pointer.address() as usize)
                    .copied()
                    .ok_or("vm: load out of bounds")?
            })),
            MemKind::I64 => Ok(Value::I64(self.read_word(pointer)? as i64)),
            MemKind::F64 => Ok(Value::F64(f64::from_bits(self.read_word(pointer)?))),
            MemKind::Bool => Ok(Value::Bool(self.read_word(pointer)? != 0)),
            MemKind::Ptr => Ok(Value::Ptr(Pointer::decode(self.read_word(pointer)?))),
            MemKind::Boxed => {
                let handle = self.read_word(pointer)? as usize;
                if handle == 0 {
                    return Err("vm: load of a bad arena handle".into());
                }
                self.boxed
                    .get(handle)
                    .cloned()
                    .ok_or_else(|| "vm: load of a bad arena handle".into())
            }
        }
    }

    fn write_word(&mut self, pointer: Pointer, word: u64) -> Result<(), String> {
        self.check_access(pointer, 8, "store")?;
        let start = pointer.address() as usize;
        let slot = self
            .mem
            .get_mut(start..start + 8)
            .ok_or("vm: store out of bounds")?;
        slot.copy_from_slice(&word.to_le_bytes());
        Ok(())
    }

    fn swap_memory(&mut self, a: Pointer, b: Pointer, len: usize) -> Result<(), String> {
        self.check_access(a, len, "swap")?;
        self.check_access(b, len, "swap")?;
        if a == b {
            return Ok(());
        }
        if len > 8 {
            return Err("vm: swap width too large".into());
        }

        let a = a.address() as usize;
        let b = b.address() as usize;
        let mut left = [0u8; 8];
        let mut right = [0u8; 8];
        left[..len].copy_from_slice(self.mem.get(a..a + len).ok_or("vm: swap out of bounds")?);
        right[..len].copy_from_slice(self.mem.get(b..b + len).ok_or("vm: swap out of bounds")?);
        self.mem
            .get_mut(a..a + len)
            .ok_or("vm: swap out of bounds")?
            .copy_from_slice(&right[..len]);
        self.mem
            .get_mut(b..b + len)
            .ok_or("vm: swap out of bounds")?
            .copy_from_slice(&left[..len]);
        Ok(())
    }

    fn free(&mut self, pointer: Pointer) -> Result<(), String> {
        if trace_mem() {
            eprintln!("MEM free {}", pointer.address());
        }
        self.allocations
            .free(self.static_len, pointer)
            .map_err(|error| format!("{} (ptr {})", vm_memory_error(error), pointer.address()))
    }

    fn check_access(&self, pointer: Pointer, len: usize, op: &str) -> Result<(), String> {
        self.allocations
            .check_access(self.mem.len(), self.static_len, pointer, len, op)
            .map_err(vm_memory_error)
    }

    fn c_string_tail(&self, pointer: Pointer) -> Result<&[u8], String> {
        let start = pointer.address() as usize;
        let end = self
            .allocations
            .accessible_tail_end(self.mem.len(), self.static_len, pointer, "io")
            .map_err(vm_io_memory_error)?;
        self.mem
            .get(start..end)
            .ok_or_else(|| "vm: io open out of bounds".to_string())
    }

    fn string_display_bytes(&self, pointer: Pointer, len: i64) -> Result<&[u8], String> {
        let len = usize::try_from(len)
            .map_err(|_| "vm: display string has invalid length".to_string())?;
        self.check_access(pointer, len, "display")?;
        let start = pointer.address() as usize;
        let end = start
            .checked_add(len)
            .ok_or_else(|| "vm: display out of bounds".to_string())?;
        self.mem
            .get(start..end)
            .ok_or_else(|| "vm: display out of bounds".to_string())
    }
}

fn vm_memory_error(error: MemoryError) -> String {
    match error {
        MemoryError::AddressOutOfRange => "vm: memory address out of range".to_string(),
        MemoryError::AllocationTooLarge => "vm: alloc count out of range".to_string(),
        MemoryError::InvalidFree => "vm: free of invalid pointer".to_string(),
        MemoryError::DoubleFree => "vm: double free".to_string(),
        MemoryError::OutOfBounds { op } => format!("vm: {op} out of bounds"),
        MemoryError::InvalidPointer { op } => format!("vm: {op} through invalid pointer"),
    }
}

fn vm_io_memory_error(error: MemoryError) -> String {
    match error {
        MemoryError::InvalidPointer { .. } | MemoryError::InvalidFree | MemoryError::DoubleFree => {
            "vm: io through invalid pointer".to_string()
        }
        MemoryError::AddressOutOfRange
        | MemoryError::AllocationTooLarge
        | MemoryError::OutOfBounds { .. } => "vm: io open out of bounds".to_string(),
    }
}

/// One io operation: extract the register operands, marshal pointer
/// operands against byte memory (read fills it, open scans a
/// NUL-terminated path, poll round-trips 8-byte pollfd records), and
/// call through the IO boundary. POSIX return conventions throughout.
fn run_io(
    machine: &mut Machine,
    frame: &Frame<'_>,
    op: crate::IoOp,
    a: u16,
    b: u16,
    c: u16,
) -> Result<i64, String> {
    use crate::IoOp;
    let int = |reg: u16| -> Result<i64, String> {
        match frame.regs[reg as usize] {
            Value::I64(v) => Ok(v),
            ref other => Err(format!("vm: io integer operand, got {other:?}")),
        }
    };
    let ptr = |reg: u16| -> Result<Pointer, String> {
        match frame.regs[reg as usize] {
            Value::Ptr(pointer) => Ok(pointer),
            ref other => Err(format!("vm: io pointer operand, got {other:?}")),
        }
    };
    Ok(match op {
        IoOp::Write => {
            let (fd, count) = (int(a)?, int(c)?);
            // A negative count passes through untouched: callers feed a
            // failed read's errno straight into the next write (the chat
            // client's read/echo loop).
            if count < 0 {
                return Ok(count);
            }
            let (pointer, len) = (ptr(b)?, count as usize);
            machine.check_access(pointer, len, "io")?;
            let start = pointer.address() as usize;
            let bytes = machine
                .mem
                .get(start..start + len)
                .ok_or("vm: io write out of bounds")?;
            machine.io.write(fd, bytes)
        }
        IoOp::Read => {
            let (fd, count) = (int(a)?, int(c)?);
            if count < 0 {
                return Ok(count);
            }
            let (pointer, len) = (ptr(b)?, count as usize);
            machine.check_access(pointer, len, "io")?;
            let start = pointer.address() as usize;
            let buf = machine
                .mem
                .get_mut(start..start + len)
                .ok_or("vm: io read out of bounds")?;
            machine.io.read(fd, buf)
        }
        IoOp::Open => {
            let tail = machine.c_string_tail(ptr(a)?)?;
            let len = tail
                .iter()
                .position(|&byte| byte == 0)
                .unwrap_or(tail.len());
            let path = tail[..len].to_vec();
            machine.io.open(&path, int(b)?, int(c)?)
        }
        IoOp::Close => machine.io.close(int(a)?),
        IoOp::Sleep => machine.io.sleep(int(a)?),
        IoOp::Ctl => machine.io.ctl(int(a)?, int(b)?, int(c)?),
        IoOp::Poll => {
            let (pointer, count, timeout) = (ptr(a)?, int(b)?, int(c)?);
            if count < 0 {
                return Err("vm: io poll negative count".into());
            }
            let count = usize::try_from(count).map_err(|_| "vm: io poll count out of range")?;
            let len = count
                .checked_mul(8)
                .ok_or("vm: io poll count out of range")?;
            machine.check_access(pointer, len, "io")?;
            let start = pointer.address() as usize;
            let records = machine
                .mem
                .get(start..start + len)
                .ok_or("vm: io poll out of bounds")?;
            let mut fds: Vec<(i32, i16, i16)> = records
                .chunks_exact(8)
                .map(|r| {
                    (
                        i32::from_le_bytes([r[0], r[1], r[2], r[3]]),
                        i16::from_le_bytes([r[4], r[5]]),
                        i16::from_le_bytes([r[6], r[7]]),
                    )
                })
                .collect();
            let result = machine.io.poll(&mut fds, timeout);
            for (index, (_, _, revents)) in fds.iter().enumerate() {
                let offset = index * 8 + 6;
                let at = pointer
                    .checked_add(offset)
                    .ok_or("vm: io poll out of bounds")?;
                machine.check_access(at, 2, "io")?;
                let at = at.address() as usize;
                let slot = machine
                    .mem
                    .get_mut(at..at + 2)
                    .ok_or("vm: io poll out of bounds")?;
                slot.copy_from_slice(&revents.to_le_bytes());
            }
            result
        }
        IoOp::Socket => machine.io.socket(int(a)?, int(b)?, int(c)?),
        IoOp::Bind => machine.io.bind(int(a)?, int(b)?, int(c)?),
        IoOp::Listen => machine.io.listen(int(a)?, int(b)?),
        IoOp::Connect => machine.io.connect(int(a)?, int(b)?, int(c)?),
        IoOp::Accept => machine.io.accept(int(a)?),
        IoOp::CwdLen => machine.io.cwd_len(),
        IoOp::CwdCopy => {
            let len = machine.io.cwd_len();
            if len < 0 {
                return Ok(len);
            }
            let pointer = ptr(a)?;
            machine.check_access(pointer, len as usize, "io")?;
            let start = pointer.address() as usize;
            let buf = machine
                .mem
                .get_mut(start..start + len as usize)
                .ok_or("vm: io cwd out of bounds")?;
            machine.io.cwd_copy(buf)
        }
        IoOp::GetenvLen => {
            let (pointer, len) = (ptr(a)?, int(b)?);
            if len < 0 {
                return Ok(len);
            }
            machine.check_access(pointer, len as usize, "io")?;
            let start = pointer.address() as usize;
            let name = machine
                .mem
                .get(start..start + len as usize)
                .ok_or("vm: io getenv name out of bounds")?;
            machine.io.getenv_len(name)
        }
        IoOp::GetenvCopy => {
            let (name_pointer, name_len, dest_pointer) = (ptr(a)?, int(b)?, ptr(c)?);
            if name_len < 0 {
                return Ok(name_len);
            }
            machine.check_access(name_pointer, name_len as usize, "io")?;
            let name_start = name_pointer.address() as usize;
            let name = machine
                .mem
                .get(name_start..name_start + name_len as usize)
                .ok_or("vm: io getenv name out of bounds")?
                .to_vec();
            let len = machine.io.getenv_len(&name);
            if len < 0 {
                return Ok(len);
            }
            machine.check_access(dest_pointer, len as usize, "io")?;
            let dest = dest_pointer.address() as usize;
            let buf = machine
                .mem
                .get_mut(dest..dest + len as usize)
                .ok_or("vm: io getenv out of bounds")?;
            machine.io.getenv_copy(&name, buf)
        }
        IoOp::Argc => machine.io.argc(),
        IoOp::ArgLen => machine.io.arg_len(int(a)?),
        IoOp::ArgCopy => {
            let (index, pointer) = (int(a)?, ptr(b)?);
            let len = machine.io.arg_len(index);
            if len < 0 {
                return Ok(len);
            }
            machine.check_access(pointer, len as usize, "io")?;
            let dest = pointer.address() as usize;
            let buf = machine
                .mem
                .get_mut(dest..dest + len as usize)
                .ok_or("vm: io arg out of bounds")?;
            machine.io.arg_copy(index, buf)
        }
        IoOp::DirCount => {
            let tail = machine.c_string_tail(ptr(a)?)?;
            let len = tail
                .iter()
                .position(|&byte| byte == 0)
                .unwrap_or(tail.len());
            let path = tail[..len].to_vec();
            machine.io.dir_count(&path)
        }
        IoOp::DirEntryKind => {
            let tail = machine.c_string_tail(ptr(a)?)?;
            let len = tail
                .iter()
                .position(|&byte| byte == 0)
                .unwrap_or(tail.len());
            let path = tail[..len].to_vec();
            machine.io.dir_entry_kind(&path, int(b)?)
        }
        IoOp::DirEntryLen => {
            let tail = machine.c_string_tail(ptr(a)?)?;
            let len = tail
                .iter()
                .position(|&byte| byte == 0)
                .unwrap_or(tail.len());
            let path = tail[..len].to_vec();
            machine.io.dir_entry_len(&path, int(b)?)
        }
        IoOp::DirEntryCopy => {
            let tail = machine.c_string_tail(ptr(a)?)?;
            let len = tail
                .iter()
                .position(|&byte| byte == 0)
                .unwrap_or(tail.len());
            let path = tail[..len].to_vec();
            let index = int(b)?;
            let entry_len = machine.io.dir_entry_len(&path, index);
            if entry_len < 0 {
                return Ok(entry_len);
            }
            let pointer = ptr(c)?;
            machine.check_access(pointer, entry_len as usize, "io")?;
            let dest = pointer.address() as usize;
            let buf = machine
                .mem
                .get_mut(dest..dest + entry_len as usize)
                .ok_or("vm: io dir entry out of bounds")?;
            machine.io.dir_entry_copy(&path, index, buf)
        }
        IoOp::RealpathLen => {
            let tail = machine.c_string_tail(ptr(a)?)?;
            let len = tail
                .iter()
                .position(|&byte| byte == 0)
                .unwrap_or(tail.len());
            let path = tail[..len].to_vec();
            machine.io.realpath_len(&path)
        }
        IoOp::RealpathCopy => {
            let tail = machine.c_string_tail(ptr(a)?)?;
            let len = tail
                .iter()
                .position(|&byte| byte == 0)
                .unwrap_or(tail.len());
            let path = tail[..len].to_vec();
            let resolved_len = machine.io.realpath_len(&path);
            if resolved_len < 0 {
                return Ok(resolved_len);
            }
            let pointer = ptr(b)?;
            machine.check_access(pointer, resolved_len as usize, "io")?;
            let dest = pointer.address() as usize;
            let buf = machine
                .mem
                .get_mut(dest..dest + resolved_len as usize)
                .ok_or("vm: io realpath out of bounds")?;
            machine.io.realpath_copy(&path, buf)
        }
        IoOp::Seek => machine.io.seek(int(a)?, int(b)?, int(c)?),
        IoOp::FileSize => machine.io.file_size(int(a)?),
        // Terminal for every host. `StdioIO` never comes back from
        // `process::exit`, so Core types its exit tails with an idle
        // `loop {}` (`Host.tlk`'s panic fallback, `IO.tlk`'s `_io_exit`).
        // A capturing host does return, and handing control back would
        // drop the VM into that loop - so the run ends here instead.
        IoOp::Exit => {
            let code = machine.io.exit(int(a)?);
            return Err(format!("vm: program exited with code {code}"));
        }
    })
}

/// Instructions that touch only the current frame (and the machine state).
fn exec_local(
    module: &Module,
    frame: &mut Frame<'_>,
    machine: &mut Machine,
    insn: Insn,
    budgets: &Budgets,
) -> Result<(), String> {
    match insn {
        Insn::Const { dest, k } => {
            let value = module
                .consts
                .get(k as usize)
                .copied()
                .map(Value::from)
                .ok_or_else(|| format!("vm: bad constant index {k}"))?;
            frame.regs[dest as usize] = value;
        }
        Insn::Move { dest, src } => frame.regs[dest as usize] = frame.regs[src as usize].clone(),
        Insn::Add { dest, a, b } => {
            frame.regs[dest as usize] = arith(
                ArithOp::Add,
                rk(module, frame, a)?,
                rk(module, frame, b)?,
                i64::wrapping_add,
                |x, y| x + y,
            )?
        }
        Insn::Sub { dest, a, b } => {
            frame.regs[dest as usize] = arith(
                ArithOp::Sub,
                rk(module, frame, a)?,
                rk(module, frame, b)?,
                i64::wrapping_sub,
                |x, y| x - y,
            )?
        }
        Insn::Mul { dest, a, b } => {
            frame.regs[dest as usize] = arith(
                ArithOp::Mul,
                rk(module, frame, a)?,
                rk(module, frame, b)?,
                i64::wrapping_mul,
                |x, y| x * y,
            )?
        }
        Insn::Div { dest, a, b } => {
            let (a, b) = (rk(module, frame, a)?, rk(module, frame, b)?);
            frame.regs[dest as usize] = match (a, b) {
                (OperandValue::I64(_), OperandValue::I64(0)) => {
                    return Err("vm: division by zero".into());
                }
                (OperandValue::I64(x), OperandValue::I64(y)) => Value::I64(x.wrapping_div(y)),
                (OperandValue::F64(x), OperandValue::F64(y)) => Value::F64(x / y),
                _ => return Err(format!("vm: div on {a:?} and {b:?}")),
            };
        }
        Insn::And { dest, a, b } => {
            frame.regs[dest as usize] = bitwise(
                "and",
                rk(module, frame, a)?,
                rk(module, frame, b)?,
                |x, y| x & y,
                |x, y| x & y,
            )?
        }
        Insn::Or { dest, a, b } => {
            frame.regs[dest as usize] = bitwise(
                "or",
                rk(module, frame, a)?,
                rk(module, frame, b)?,
                |x, y| x | y,
                |x, y| x | y,
            )?
        }
        Insn::Xor { dest, a, b } => {
            frame.regs[dest as usize] = bitwise(
                "xor",
                rk(module, frame, a)?,
                rk(module, frame, b)?,
                |x, y| x ^ y,
                |x, y| x ^ y,
            )?
        }
        Insn::Shl { dest, a, b } => {
            frame.regs[dest as usize] = shift(
                "shl",
                rk(module, frame, a)?,
                rk(module, frame, b)?,
                i64::wrapping_shl,
                u8::wrapping_shl,
            )?
        }
        Insn::Shr { dest, a, b } => {
            frame.regs[dest as usize] = shift(
                "shr",
                rk(module, frame, a)?,
                rk(module, frame, b)?,
                i64::wrapping_shr,
                u8::wrapping_shr,
            )?
        }
        Insn::Not { dest, src } => {
            frame.regs[dest as usize] = match &frame.regs[src as usize] {
                Value::I64(x) => Value::I64(!x),
                Value::Byte(x) => Value::Byte(!x),
                value => return Err(format!("vm: not on {value:?}")),
            };
        }
        Insn::Cmp { dest, a, b, op } => {
            let result = compare(rk(module, frame, a)?, rk(module, frame, b)?, op)?;
            frame.regs[dest as usize] = Value::Bool(result);
        }
        Insn::Trunc { dest, src } => {
            let Value::F64(v) = frame.regs[src as usize] else {
                return Err("vm: trunc of a non-float".into());
            };
            frame.regs[dest as usize] = Value::I64(v as i64);
        }
        Insn::IToF { dest, src } => {
            let Value::I64(v) = frame.regs[src as usize] else {
                return Err("vm: itof of a non-int".into());
            };
            frame.regs[dest as usize] = Value::F64(v as f64);
        }
        Insn::BToI { dest, src } => {
            let Value::Byte(v) = frame.regs[src as usize] else {
                return Err("vm: btoi of a non-byte".into());
            };
            frame.regs[dest as usize] = Value::I64(v as i64);
        }
        Insn::IToB { dest, src } => {
            let Value::I64(v) = frame.regs[src as usize] else {
                return Err("vm: itob of a non-int".into());
            };
            let Ok(b) = u8::try_from(v) else {
                return Err("vm: itob of a value outside 0..=255".into());
            };
            frame.regs[dest as usize] = Value::Byte(b);
        }
        Insn::CellNew { dest, init } => {
            machine.slots.push(frame.regs[init as usize].clone());
            frame.regs[dest as usize] = Value::Cell(machine.slots.len() - 1);
        }
        Insn::CellGet { dest, cell } => {
            let Value::Cell(index) = frame.regs[cell as usize] else {
                return Err("vm: cell_get of a non-cell".into());
            };
            frame.regs[dest as usize] = machine.slots[index].clone();
        }
        Insn::CellSet { cell, src } => {
            let Value::Cell(index) = frame.regs[cell as usize] else {
                return Err("vm: cell_set of a non-cell".into());
            };
            machine.slots[index] = frame.regs[src as usize].clone();
        }
        Insn::AggNew {
            dest,
            layout,
            tag,
            args_start,
            args_len,
        } => {
            let args = arg_values(module, frame, args_start, args_len)?;
            frame.regs[dest as usize] = build_agg(&module.layouts, layout, tag, args)?;
        }
        Insn::StringLit {
            dest,
            offset,
            len,
            layout,
        } => {
            let value = machine
                .static_strings
                .entry((offset, len, layout))
                .or_insert_with(|| {
                    let len = i64::from(len);
                    Value::Agg(
                        layout,
                        Rc::new(vec![
                            Value::Ptr(Pointer::static_at(offset)),
                            Value::I64(len),
                            Value::I64(len),
                        ]),
                    )
                })
                .clone();
            frame.regs[dest as usize] = value;
        }
        Insn::Field {
            dest,
            src,
            offset,
            layout,
        } => {
            let Value::Agg(_, slots) = &frame.regs[src as usize] else {
                return Err("vm: field read on a non-flat aggregate".into());
            };
            let shape = crate::member_shape(layout);
            frame.regs[dest as usize] = read_slots(&module.layouts, slots, offset, shape)?;
        }
        Insn::FieldIndex { dest, src, index } => {
            let Value::Agg(layout, slots) = &frame.regs[src as usize] else {
                return Err("vm: field read on a non-aggregate".into());
            };
            let (offset, shape) = field_site(&module.layouts, *layout, slots, index)?;
            frame.regs[dest as usize] = read_slots(&module.layouts, slots, offset, shape)?;
        }
        Insn::GetElement {
            dest,
            rec,
            index,
            element,
        } => {
            let Value::I64(index) = frame.regs[index as usize] else {
                return Err("vm: inline_get index is not an Int".into());
            };
            let index = u16::try_from(index).map_err(|_| "vm: inline_get index out of range")?;
            let Value::Agg(_, slots) = &frame.regs[rec as usize] else {
                return Err("vm: inline_get on a non-flat aggregate".into());
            };
            let shape = crate::member_shape(element);
            let stride = match shape {
                FieldShape::Slot => 1,
                FieldShape::Spliced(child) => {
                    module
                        .layouts
                        .get(child as usize)
                        .ok_or("vm: inline_get with an unknown element layout")?
                        .width
                }
            };
            let offset = index
                .checked_mul(stride)
                .ok_or("vm: inline_get index out of range")?;
            frame.regs[dest as usize] = read_slots(&module.layouts, slots, offset, shape)?;
        }
        Insn::GetTag { dest, src } => {
            let Value::Agg(_, slots) = &frame.regs[src as usize] else {
                return Err("vm: get_tag on a non-variant".into());
            };
            let Some(Value::I64(tag)) = slots.first() else {
                return Err("vm: get_tag on a non-variant".into());
            };
            frame.regs[dest as usize] = Value::I64(*tag);
        }
        Insn::ExistentialPack {
            dest,
            args_start,
            args_len,
        } => {
            let mut values = arg_values(module, frame, args_start, args_len)?;
            if values.is_empty() {
                return Err("vm: existential_pack without a payload".into());
            }
            let payload = values.remove(0);
            frame.regs[dest as usize] = Value::Existential(Rc::new(payload), Rc::new(values));
        }
        Insn::ExistentialWitness { dest, src, index } => {
            let Value::Existential(_, witnesses) = &frame.regs[src as usize] else {
                return Err("vm: existential_witness on a non-existential".into());
            };
            let witness = witnesses
                .get(index as usize)
                .cloned()
                .ok_or("vm: existential witness index out of range")?;
            frame.regs[dest as usize] = witness;
        }
        Insn::ExistentialPayload { dest, src } => {
            let Value::Existential(payload, _) = &frame.regs[src as usize] else {
                return Err("vm: existential_payload on a non-existential".into());
            };
            frame.regs[dest as usize] = (**payload).clone();
        }
        Insn::MakeClosure {
            dest,
            chunk,
            args_start,
            args_len,
        } => {
            let env = arg_values(module, frame, args_start, args_len)?;
            frame.regs[dest as usize] = Value::Closure(chunk, Rc::new(env));
        }
        Insn::EnvGet { dest, index } => {
            let value = frame
                .env
                .get(index as usize)
                .cloned()
                .ok_or("vm: environment index out of range")?;
            frame.regs[dest as usize] = value;
        }
        Insn::SetField {
            dest,
            rec,
            src,
            offset,
            layout,
        } => {
            let value = frame.regs[src as usize].clone();
            let Value::Agg(id, slots) = &frame.regs[rec as usize] else {
                return Err("vm: field write on a non-flat aggregate".into());
            };
            // CoW: clone the Rc, mutate the (now possibly unshared) copy.
            let (id, mut slots) = (*id, slots.clone());
            let shape = crate::member_shape(layout);
            write_slots(
                &module.layouts,
                Rc::make_mut(&mut slots).as_mut_slice(),
                offset,
                shape,
                value,
            )?;
            frame.regs[dest as usize] = Value::Agg(id, slots);
        }
        Insn::SetFieldIndex {
            dest,
            rec,
            src,
            index,
        } => {
            let value = frame.regs[src as usize].clone();
            let Value::Agg(layout, slots) = &frame.regs[rec as usize] else {
                return Err("vm: set_field on a non-record".into());
            };
            // CoW: clone the Rc, mutate the (now possibly unshared) copy.
            let (layout, mut slots) = (*layout, slots.clone());
            let (offset, shape) = field_site(&module.layouts, layout, &slots, index)?;
            write_slots(
                &module.layouts,
                Rc::make_mut(&mut slots).as_mut_slice(),
                offset,
                shape,
                value,
            )?;
            frame.regs[dest as usize] = Value::Agg(layout, slots);
        }
        Insn::Alloc { dest, count } => {
            let Value::I64(count) = frame.regs[count as usize] else {
                return Err("vm: alloc of a non-int count".into());
            };
            if count < 0 {
                return Err("vm: alloc of a negative count".into());
            }
            let count = usize::try_from(count).map_err(|_| "vm: alloc count out of range")?;
            // Against the length the allocation would actually leave
            // behind: reusing a freed span holds no more memory, and
            // budgeting on `len + count` would fail an allocate/free
            // loop that never grows.
            if machine.allocations.projected_len(machine.mem.len(), count) > budgets.memory_bytes {
                return Err("vm: memory budget exhausted".into());
            }
            let pointer = machine
                .allocations
                .allocate(&mut machine.mem, count)
                .map_err(vm_memory_error)?;
            if trace_mem() {
                eprintln!("MEM alloc ptr={} count={count}", pointer.address());
            }
            frame.regs[dest as usize] = Value::Ptr(pointer);
        }
        Insn::Free { dest, ptr } => {
            let Value::Ptr(ptr) = frame.regs[ptr as usize] else {
                return Err("vm: free of a non-pointer".into());
            };
            machine.free(ptr)?;
            frame.regs[dest as usize] = Value::Void;
        }
        Insn::Retain { dest, ptr } => {
            let Value::Ptr(pointer) = frame.regs[ptr as usize] else {
                return Err("vm: retain of a non-pointer".into());
            };
            if trace_mem() {
                eprintln!("MEM retain ptr={}", pointer.address());
            }
            machine
                .allocations
                .retain(machine.static_len, pointer)
                .map_err(vm_memory_error)?;
            frame.regs[dest as usize] = Value::Void;
        }
        Insn::IsUnique { dest, ptr } => {
            let Value::Ptr(ptr) = frame.regs[ptr as usize] else {
                return Err("vm: is_unique of a non-pointer".into());
            };
            let unique = machine
                .allocations
                .is_unique(machine.static_len, ptr)
                .map_err(vm_memory_error)?;
            frame.regs[dest as usize] = Value::Bool(unique);
        }
        Insn::ObjectNew {
            dest,
            args_start,
            args_len,
        } => {
            let fields = arg_values(module, frame, args_start, args_len)?;
            let object = machine.objects.allocate(fields).map_err(vm_object_error)?;
            frame.regs[dest as usize] = Value::Object(object);
        }
        Insn::SetFinalizer { obj, closure } => {
            let Value::Object(object) = frame.regs[obj as usize] else {
                return Err("vm: set_finalizer of a non-object".into());
            };
            let thunk = frame.regs[closure as usize].clone();
            if !matches!(thunk, Value::Closure(..)) {
                return Err("vm: finalizer is not a function value".into());
            }
            machine
                .objects
                .set_finalizer(object, thunk)
                .map_err(vm_object_error)?;
        }
        Insn::ObjectGet { dest, obj, index } => {
            let Value::Object(object) = frame.regs[obj as usize] else {
                return Err("vm: object_get of a non-object".into());
            };
            frame.regs[dest as usize] = machine
                .objects
                .get_field(object, index)
                .map_err(vm_object_error)?;
        }
        Insn::ObjectSet { obj, src, index } => {
            let Value::Object(object) = frame.regs[obj as usize] else {
                return Err("vm: object_set of a non-object".into());
            };
            let value = frame.regs[src as usize].clone();
            let mut handles = vec![];
            scan_handles(&value, &mut handles);
            machine
                .objects
                .set_field(object, index, value, &handles)
                .map_err(vm_object_error)?;
        }
        Insn::RegionAcquire { dest, src } => {
            let mut handles = vec![];
            scan_handles(&frame.regs[src as usize], &mut handles);
            machine.objects.acquire(&handles).map_err(vm_object_error)?;
            frame.regs[dest as usize] = Value::Void;
        }
        Insn::RegionRelease { dest, src } => {
            let mut handles = vec![];
            scan_handles(&frame.regs[src as usize], &mut handles);
            machine.objects.release(&handles).map_err(vm_object_error)?;
            frame.regs[dest as usize] = Value::Void;
        }
        Insn::Load { dest, ptr, kind } => {
            let Value::Ptr(addr) = frame.regs[ptr as usize] else {
                return Err("vm: load of a non-pointer".into());
            };
            frame.regs[dest as usize] = machine.load_value(addr, kind)?;
        }
        Insn::CheckedIndexedLoad {
            dest,
            base,
            index,
            length,
            kind,
            failure_target,
        } => {
            let (Value::I64(index), Value::I64(length)) =
                (&frame.regs[index as usize], &frame.regs[length as usize])
            else {
                return Err("vm: checked indexed load bounds operands".into());
            };
            if *index < 0 || *index >= *length {
                frame.pc = failure_target as usize;
                return Ok(());
            }
            let Value::Ptr(base) = frame.regs[base as usize] else {
                return Err("vm: checked indexed load of a non-pointer".into());
            };
            let width = match kind {
                MemKind::Byte => 1,
                MemKind::I64 | MemKind::F64 | MemKind::Bool | MemKind::Ptr | MemKind::Boxed => 8,
            };
            let pointer = base.wrapping_offset(index.wrapping_mul(width));
            frame.regs[dest as usize] = machine.load_value(pointer, kind)?;
        }
        Insn::Store { ptr, src, kind } => {
            let Value::Ptr(pointer) = frame.regs[ptr as usize] else {
                return Err("vm: store to a non-pointer".into());
            };
            let value = frame.regs[src as usize].clone();
            match (kind, value) {
                (MemKind::Byte, Value::Byte(byte)) => {
                    machine.check_access(pointer, 1, "store")?;
                    let slot = machine
                        .mem
                        .get_mut(pointer.address() as usize)
                        .ok_or("vm: store out of bounds")?;
                    *slot = byte;
                }
                (MemKind::I64, Value::I64(v)) => machine.write_word(pointer, v as u64)?,
                (MemKind::F64, Value::F64(v)) => machine.write_word(pointer, v.to_bits())?,
                (MemKind::Bool, Value::Bool(v)) => machine.write_word(pointer, v as u64)?,
                (MemKind::Ptr, Value::Ptr(value)) => machine.write_word(pointer, value.encode())?,
                (MemKind::Boxed, value) => {
                    // The bump allocator never reuses addresses and fresh
                    // memory is zeroed, so a nonzero word here can only be
                    // this cell's own handle (slot 0 is the reserved
                    // placeholder): overwrite its slot instead of growing
                    // the arena on every store.
                    let existing = machine.read_word(pointer)? as usize;
                    if existing != 0 && existing < machine.boxed.len() {
                        machine.boxed[existing] = value;
                    } else {
                        machine.boxed.push(value);
                        machine.write_word(pointer, (machine.boxed.len() - 1) as u64)?;
                    }
                }
                (kind, value) => {
                    return Err(format!("vm: store kind {kind:?} got {value:?}"));
                }
            }
            // The transfer copier interprets buffers through the element
            // kind their typed stores wrote (ADR 0058).
            machine.allocations.note_store(pointer, kind);
        }
        Insn::Copy { from, to, len } => {
            let (Value::Ptr(from), Value::Ptr(to), Value::I64(len)) = (
                &frame.regs[from as usize],
                &frame.regs[to as usize],
                &frame.regs[len as usize],
            ) else {
                return Err("vm: copy operands".into());
            };
            if *len < 0 {
                return Err("vm: copy negative length".into());
            }
            machine.check_access(*from, *len as usize, "copy")?;
            machine.check_access(*to, *len as usize, "copy")?;
            // A raw byte copy moves typed content without a typed store:
            // carry the source's observed element kind to the target so
            // the transfer copier keeps seeing through it (ADR 0058).
            machine.allocations.propagate_kind(*from, *to);
            let (from, to, len) = (
                from.address() as usize,
                to.address() as usize,
                *len as usize,
            );
            machine.mem.copy_within(from..from + len, to);
        }
        Insn::Swap { a, b, kind } => {
            let (Value::Ptr(a), Value::Ptr(b)) = (&frame.regs[a as usize], &frame.regs[b as usize])
            else {
                return Err("vm: swap operands".into());
            };
            let len = match kind {
                MemKind::Byte => 1,
                MemKind::I64 | MemKind::F64 | MemKind::Bool | MemKind::Ptr | MemKind::Boxed => 8,
            };
            machine.swap_memory(*a, *b, len)?;
        }
        Insn::TaskJoin { dest, handle } => {
            let Some(Value::I64(handle)) = frame.regs.get(handle as usize).cloned() else {
                return Err("vm: task join handle must be an Int".into());
            };
            let slot = usize::try_from(handle)
                .ok()
                .filter(|slot| *slot < machine.tasks.len())
                .ok_or("vm: task join on an invalid or already-joined handle")?;
            let taken = std::mem::replace(&mut machine.tasks[slot], TaskSlot::Joined);
            let value = match taken {
                #[cfg(any(not(target_arch = "wasm32"), target_feature = "atomics"))]
                TaskSlot::Running(worker) => {
                    // The join is the synchronization edge; the worker's
                    // buffered output replays into this machine's sink in
                    // join order.
                    let (transfer, out, err) = worker
                        .join()
                        .map_err(|_| "vm: a task worker panicked")??;
                    if !out.is_empty() {
                        machine.io.write(1, &out);
                    }
                    if !err.is_empty() {
                        machine.io.write(2, &err);
                    }
                    machine.deserialize_transfer(&transfer)?
                }
                TaskSlot::Done(value) => value,
                TaskSlot::Pending | TaskSlot::Joined => {
                    return Err("vm: task join on an invalid or already-joined handle".into());
                }
            };
            frame.regs[dest as usize] = value;
        }
        Insn::TaskWidth { dest } => {
            let width = std::thread::available_parallelism()
                .map(|n| n.get() as i64)
                .unwrap_or(1);
            frame.regs[dest as usize] = Value::I64(width);
        }
        Insn::ChanSend { handle, value } => {
            let Some(Value::I64(handle)) = frame.regs.get(handle as usize).cloned() else {
                return Err("vm: channel handle must be an Int".into());
            };
            let Some(value) = frame.regs.get(value as usize).cloned() else {
                return Err("vm: channel value register out of range".into());
            };
            // The value crosses workers as a transfer packet; this
            // machine's copy releases, exactly as at a spawn boundary.
            let packet = machine.serialize_transfer(&value)?;
            machine.release_transferred(&value)?;
            let mut registry = channels_locked();
            let slot = usize::try_from(handle)
                .ok()
                .and_then(|slot| registry.get_mut(slot))
                .and_then(Option::as_mut)
                .ok_or("vm: send on an invalid channel handle")?;
            slot.queue.push_back(packet);
            // A bounded send consumes the reservation its poll claimed.
            slot.reserved = slot.reserved.saturating_sub(1);
            drop(registry);
            channels().1.notify_all();
        }
        Insn::ChanTake { dest, handle } => {
            let Some(Value::I64(handle)) = frame.regs.get(handle as usize).cloned() else {
                return Err("vm: channel handle must be an Int".into());
            };
            let packet = {
                let mut registry = channels_locked();
                let slot = usize::try_from(handle)
                    .ok()
                    .and_then(|slot| registry.get_mut(slot))
                    .and_then(Option::as_mut)
                    .ok_or("vm: take on an invalid channel handle")?;
                slot.queue
                    .pop_front()
                    .ok_or("vm: take on an empty channel")?
            };
            // Room opened: parked bounded senders must observe it.
            channels().1.notify_all();
            let value = machine.deserialize_transfer(&packet)?;
            frame.regs[dest as usize] = value;
        }
        Insn::ChanCtl { dest, handle, op } => {
            let Some(Value::I64(handle)) = frame.regs.get(handle as usize).cloned() else {
                return Err("vm: channel handle must be an Int".into());
            };
            let Some(Value::I64(op)) = frame.regs.get(op as usize).cloned() else {
                return Err("vm: channel op must be an Int".into());
            };
            let result = chan_ctl(machine, handle, op)?;
            frame.regs[dest as usize] = Value::I64(result);
        }
        Insn::Io { dest, op, a, b, c } => {
            let result = run_io(machine, frame, op, a, b, c)?;
            frame.regs[dest as usize] = Value::I64(result);
        }
        Insn::Jump { target } => frame.pc = target as usize,
        Insn::Branch {
            cond,
            then_target,
            else_target,
        } => {
            let Value::Bool(cond) = frame.regs[cond as usize] else {
                return Err("vm: branch on a non-bool".into());
            };
            frame.pc = if cond { then_target } else { else_target } as usize;
        }
        Insn::Switch {
            tag,
            targets_start,
            targets_len,
        } => {
            let Value::I64(tag) = frame.regs[tag as usize] else {
                return Err("vm: switch on a non-int tag".into());
            };
            let start = targets_start as usize;
            let end = start + targets_len as usize;
            let targets = module
                .switch_pool
                .get(start..end)
                .ok_or("vm: bad switch pool range")?;
            let (&default, arms) = targets.split_last().ok_or("vm: empty switch")?;
            // A tag outside the arm range takes the default — the same
            // rule as the reference evaluator's Op::Switch.
            let target = usize::try_from(tag)
                .ok()
                .and_then(|t| arms.get(t).copied())
                .unwrap_or(default);
            frame.pc = target as usize;
        }
        Insn::Call { .. }
        | Insn::CallIndirect { .. }
        | Insn::TaskSpawn { .. }
        | Insn::Ret { .. }
        | Insn::Trap { .. }
        | Insn::MakeCont { .. }
        | Insn::CallCont { .. }
        | Insn::UnwindRet
        | Insn::PushHandler { .. }
        | Insn::FindHandler { .. }
        | Insn::GetFloor { .. }
        | Insn::SetFloor { .. }
        | Insn::Suspend { .. }
        | Insn::Resume { .. }
        | Insn::Cancel { .. } => {
            return Err("vm: non-local instruction in exec_local".into());
        }
    }
    Ok(())
}

fn chunk(module: &Module, index: u32) -> Result<&Chunk, String> {
    module
        .chunks
        .get(index as usize)
        .ok_or_else(|| format!("vm: bad chunk index {index}"))
}

fn check_call_shape(target: &Chunk, args_len: u16) -> Result<(), String> {
    if args_len != target.arity {
        return Err(format!(
            "vm: call to {} expected {} arguments, got {}",
            target.name, target.arity, args_len
        ));
    }
    if args_len > target.n_regs {
        return Err("vm: call argument count exceeds callee frame".into());
    }
    Ok(())
}

/// Every object handle reachable in a value — the region ledger's scan.
/// Cells are frame-local machine state and are not descended (the binding
/// that owns the cell accounts for its contents).
fn scan_handles(value: &Value, out: &mut Vec<u32>) {
    match value {
        Value::Object(object) => out.push(*object),
        Value::Agg(_, fields) => {
            for field in fields.iter() {
                scan_handles(field, out);
            }
        }
        Value::Existential(payload, witnesses) => {
            scan_handles(payload, out);
            for witness in witnesses.iter() {
                scan_handles(witness, out);
            }
        }
        Value::Closure(_, env) => {
            for captured in env.iter() {
                scan_handles(captured, out);
            }
        }
        Value::I64(_)
        | Value::F64(_)
        | Value::Bool(_)
        | Value::Byte(_)
        | Value::Void
        | Value::Ptr(_)
        | Value::Cell(_)
        | Value::Cont(..) => {}
    }
}

fn vm_object_error(error: ObjectError) -> String {
    format!("vm: {}", error.message())
}

/// A callee frame's registers in one allocation: argument registers
/// cloned from the caller into the low slots, the rest Void. The
/// two-step version (collect the arguments, allocate a zeroed frame,
/// move them in) was two allocations and a drop on every call — the
/// interpreter's hottest edge.
/// Unwrap the Talk-level `Resumption` value (a linear one-field core
/// struct) to its worker-local slot (ADR 0064).
fn resumption_slot(value: &Value) -> Result<usize, String> {
    let slot = match value {
        Value::Agg(_, fields) => match fields.first() {
            Some(Value::I64(slot)) => *slot,
            _ => return Err("vm: malformed resumption value".into()),
        },
        Value::I64(slot) => *slot,
        _ => return Err("vm: malformed resumption value".into()),
    };
    usize::try_from(slot).map_err(|_| "vm: malformed resumption value".into())
}

fn call_regs(
    module: &Module,
    frame: &Frame<'_>,
    args_start: u32,
    args_len: u16,
    n_regs: u16,
    pool: &mut Vec<Vec<Value>>,
) -> Result<Vec<Value>, String> {
    let start = usize::try_from(args_start).map_err(|_| "vm: bad argument pool range")?;
    let end = start
        .checked_add(usize::from(args_len))
        .ok_or("vm: bad argument pool range")?;
    let arg_regs = module
        .arg_pool
        .get(start..end)
        .ok_or("vm: bad argument pool range")?;
    if args_len > n_regs {
        return Err("vm: call argument count exceeds callee frame".into());
    }
    let mut regs = pool.pop().unwrap_or_default();
    regs.reserve(usize::from(n_regs));
    for &src in arg_regs {
        regs.push(rk_value(module, frame, src)?);
    }
    regs.resize(usize::from(n_regs), Value::Void);
    Ok(regs)
}

fn arg_values(
    module: &Module,
    frame: &Frame<'_>,
    args_start: u32,
    args_len: u16,
) -> Result<Vec<Value>, String> {
    let start = usize::try_from(args_start).map_err(|_| "vm: bad argument pool range")?;
    let end = start
        .checked_add(usize::from(args_len))
        .ok_or("vm: bad argument pool range")?;
    let arg_regs = module
        .arg_pool
        .get(start..end)
        .ok_or("vm: bad argument pool range")?;
    let mut values = Vec::with_capacity(arg_regs.len());
    for &src in arg_regs {
        values.push(rk_value(module, frame, src)?);
    }
    Ok(values)
}

/// Read a register-or-constant operand as an owned VM value.
#[inline]
fn rk_value(module: &Module, frame: &Frame<'_>, field: u16) -> Result<Value, String> {
    if field & crate::RK_CONST != 0 {
        module
            .consts
            .get(usize::from(field & crate::RK_INDEX))
            .copied()
            .map(Value::from)
            .ok_or_else(|| format!("vm: bad constant operand {}", field & crate::RK_INDEX))
    } else {
        frame
            .regs
            .get(usize::from(field))
            .cloned()
            .ok_or_else(|| format!("vm: operand register r{field} out of range"))
    }
}

/// Read a register-or-constant operand field (RK encoding — see
/// `RK_CONST` in the crate root).
#[inline]
fn rk<'a>(
    module: &'a Module,
    frame: &'a Frame<'_>,
    field: u16,
) -> Result<OperandValue<'a>, String> {
    if field & crate::RK_CONST != 0 {
        module
            .consts
            .get(usize::from(field & crate::RK_INDEX))
            .copied()
            .map(OperandValue::from)
            .ok_or_else(|| format!("vm: bad constant operand {}", field & crate::RK_INDEX))
    } else {
        frame
            .regs
            .get(usize::from(field))
            .map(OperandValue::from_value)
            .ok_or_else(|| format!("vm: operand register r{field} out of range"))
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum ArithOp {
    Add,
    Sub,
    Mul,
}

fn arith(
    op: ArithOp,
    a: OperandValue<'_>,
    b: OperandValue<'_>,
    ints: fn(i64, i64) -> i64,
    floats: fn(f64, f64) -> f64,
) -> Result<Value, String> {
    match (a, b) {
        (OperandValue::I64(x), OperandValue::I64(y)) => Ok(Value::I64(ints(x, y))),
        (OperandValue::F64(x), OperandValue::F64(y)) => Ok(Value::F64(floats(x, y))),
        // Pointer arithmetic (`add RawPtr p offset`).
        (OperandValue::Ptr(pointer), OperandValue::I64(offset)) if op == ArithOp::Add => {
            Ok(Value::Ptr(pointer.wrapping_offset(offset)))
        }
        (OperandValue::Ptr(pointer), OperandValue::I64(offset)) if op == ArithOp::Sub => {
            Ok(Value::Ptr(pointer.wrapping_offset(offset.wrapping_neg())))
        }
        _ => Err(format!("vm: arithmetic on {a:?} and {b:?}")),
    }
}

fn bitwise(
    name: &str,
    a: OperandValue<'_>,
    b: OperandValue<'_>,
    ints: fn(i64, i64) -> i64,
    bytes: fn(u8, u8) -> u8,
) -> Result<Value, String> {
    match (a, b) {
        (OperandValue::I64(x), OperandValue::I64(y)) => Ok(Value::I64(ints(x, y))),
        (OperandValue::Byte(x), OperandValue::Byte(y)) => Ok(Value::Byte(bytes(x, y))),
        _ => Err(format!("vm: {name} on {a:?} and {b:?}")),
    }
}

/// Shifts mask the shift amount to the operand's bit width via
/// `wrapping_sh*`: Int masks to 6 bits and Byte masks to 3 bits.
fn shift(
    name: &str,
    a: OperandValue<'_>,
    b: OperandValue<'_>,
    ints: fn(i64, u32) -> i64,
    bytes: fn(u8, u32) -> u8,
) -> Result<Value, String> {
    match (a, b) {
        (OperandValue::I64(x), OperandValue::I64(y)) => Ok(Value::I64(ints(x, y as u32))),
        (OperandValue::Byte(x), OperandValue::I64(y)) => Ok(Value::Byte(bytes(x, y as u32))),
        (OperandValue::Byte(x), OperandValue::Byte(y)) => Ok(Value::Byte(bytes(x, u32::from(y)))),
        _ => Err(format!("vm: {name} on {a:?} and {b:?}")),
    }
}

fn compare(a: OperandValue<'_>, b: OperandValue<'_>, op: CmpOp) -> Result<bool, String> {
    use CmpOp::*;
    match (a, b) {
        (OperandValue::I64(x), OperandValue::I64(y)) => Ok(match op {
            Eq => x == y,
            Ne => x != y,
            Lt => x < y,
            Le => x <= y,
            Gt => x > y,
            Ge => x >= y,
        }),
        (OperandValue::F64(x), OperandValue::F64(y)) => Ok(match op {
            Eq => x == y,
            Ne => x != y,
            Lt => x < y,
            Le => x <= y,
            Gt => x > y,
            Ge => x >= y,
        }),
        (OperandValue::Byte(x), OperandValue::Byte(y)) => Ok(match op {
            Eq => x == y,
            Ne => x != y,
            Lt => x < y,
            Le => x <= y,
            Gt => x > y,
            Ge => x >= y,
        }),
        (OperandValue::Bool(x), OperandValue::Bool(y)) => match op {
            Eq => Ok(x == y),
            Ne => Ok(x != y),
            _ => Err("vm: ordering comparison on bools".into()),
        },
        (OperandValue::Ptr(x), OperandValue::Ptr(y)) => match op {
            Eq => Ok(x == y),
            Ne => Ok(x != y),
            _ => Err("vm: ordering comparison on pointers".into()),
        },
        _ => Err(format!("vm: comparison on {a:?} and {b:?}")),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::NO_LAYOUT;
    use crate::io::CaptureIO;
    use crate::{Chunk, Module};

    fn run_with_machine(module: &Module) -> (Value, usize, usize) {
        let mut io = CaptureIO::default();
        let (value, machine) = run_machine(module, &mut io).expect("vm run");
        (value, machine.objects.live_objects(), io.out.len())
    }

    fn itob_module(k: Constant) -> Module {
        Module {
            chunks: vec![Chunk {
                name: "main".into(),
                code: vec![
                    Insn::Const { dest: 0, k: 0 },
                    Insn::IToB { dest: 1, src: 0 },
                    Insn::Ret { src: 1 },
                ],
                arity: 0,
                n_regs: 2,
                unwind: vec![],
            }],
            consts: vec![k],
            arg_pool: vec![],
            switch_pool: vec![],
            traps: vec![],
            statics: vec![],
            layouts: vec![],
            entry: 0,
            exports: vec![],
        }
    }

    /// The String record symbol export tests fabricate host strings under;
    /// the storage child's symbol is `export_sym(2)` by convention.
    fn export_shape() -> Symbol {
        export_sym(1)
    }

    fn export_sym(id: u32) -> Symbol {
        Symbol::Struct(crate::symbol::ModuleSymbolId::new(
            crate::symbol::ModuleId(1),
            id,
        ))
    }

    fn export_module(chunk: Chunk, name: &str) -> Module {
        Module {
            chunks: vec![chunk],
            exports: vec![(name.into(), 0)],
            ..Module::default()
        }
    }

    #[test]
    fn instruction_budget_halts_an_infinite_loop() {
        let module = export_module(
            Chunk {
                name: "spin".into(),
                code: vec![Insn::Jump { target: 0 }],
                arity: 0,
                n_regs: 1,
                unwind: vec![],
            },
            "spin",
        );
        let mut io = CaptureIO::default();
        let budgets = Budgets {
            instructions: 1_000,
            ..Budgets::default()
        };
        let err = run_export(&module, "spin", &[], export_shape(), budgets, &mut io)
            .err()
            .expect("the loop must exhaust its budget");
        assert!(err.contains("instruction budget"), "{err}");
    }

    #[test]
    fn frame_budget_bounds_recursion() {
        let module = export_module(
            Chunk {
                name: "rec".into(),
                code: vec![
                    Insn::Call {
                        dest: 0,
                        chunk: 0,
                        args_start: 0,
                        args_len: 0,
                    },
                    Insn::Ret { src: 0 },
                ],
                arity: 0,
                n_regs: 1,
                unwind: vec![],
            },
            "rec",
        );
        let mut io = CaptureIO::default();
        let budgets = Budgets {
            frames: 16,
            ..Budgets::default()
        };
        let err = run_export(&module, "rec", &[], export_shape(), budgets, &mut io)
            .err()
            .expect("recursion must exhaust the frame budget");
        assert!(err.contains("call stack overflow"), "{err}");
    }

    #[test]
    fn checked_indexed_load_loads_or_takes_the_failure_target() {
        let module = |index| Module {
            chunks: vec![Chunk {
                name: "checked_load".into(),
                code: vec![
                    Insn::Const { dest: 0, k: 0 },
                    Insn::Const { dest: 1, k: 1 },
                    Insn::Const { dest: 2, k: 2 },
                    Insn::CheckedIndexedLoad {
                        dest: 3,
                        base: 0,
                        index: 1,
                        length: 2,
                        kind: MemKind::I64,
                        failure_target: 5,
                    },
                    Insn::Ret { src: 3 },
                    Insn::Const { dest: 3, k: 3 },
                    Insn::Ret { src: 3 },
                ],
                arity: 0,
                n_regs: 4,
                unwind: vec![],
            }],
            consts: vec![
                Constant::Ptr(0),
                Constant::I64(index),
                Constant::I64(1),
                Constant::I64(-1),
            ],
            statics: 42i64.to_le_bytes().to_vec(),
            ..Module::default()
        };

        assert_eq!(run_with_machine(&module(0)).0, Value::I64(42));
        assert_eq!(run_with_machine(&module(1)).0, Value::I64(-1));
        assert_eq!(run_with_machine(&module(-1)).0, Value::I64(-1));
    }

    #[test]
    fn pointer_load_store_preserves_allocation_provenance() {
        let module = Module {
            chunks: vec![Chunk {
                name: "pointer_round_trip".into(),
                code: vec![
                    Insn::Const { dest: 0, k: 0 },
                    Insn::Alloc { dest: 1, count: 0 },
                    Insn::Const { dest: 2, k: 1 },
                    Insn::Alloc { dest: 3, count: 2 },
                    Insn::Store {
                        ptr: 1,
                        src: 3,
                        kind: MemKind::Ptr,
                    },
                    Insn::Load {
                        dest: 4,
                        ptr: 1,
                        kind: MemKind::Ptr,
                    },
                    Insn::Free { dest: 5, ptr: 4 },
                    Insn::Free { dest: 5, ptr: 1 },
                    Insn::Const { dest: 5, k: 2 },
                    Insn::Ret { src: 5 },
                ],
                arity: 0,
                n_regs: 6,
                unwind: vec![],
            }],
            consts: vec![Constant::I64(8), Constant::I64(1), Constant::Void],
            ..Module::default()
        };
        let mut io = CaptureIO::default();
        let (value, machine) = run_machine(&module, &mut io).expect("run");
        assert_eq!(value, Value::Void);
        assert_eq!(machine.allocations.live_count(), 0);
    }

    #[test]
    fn memory_budget_rejects_an_oversized_allocation() {
        let module = Module {
            chunks: vec![Chunk {
                name: "grab".into(),
                code: vec![
                    Insn::Const { dest: 0, k: 0 },
                    Insn::Alloc { dest: 1, count: 0 },
                    Insn::Ret { src: 1 },
                ],
                arity: 0,
                n_regs: 2,
                unwind: vec![],
            }],
            consts: vec![Constant::I64(1 << 40)],
            exports: vec![("grab".into(), 0)],
            ..Module::default()
        };
        let mut io = CaptureIO::default();
        let budgets = Budgets {
            memory_bytes: 1024,
            ..Budgets::default()
        };
        let err = run_export(&module, "grab", &[], export_shape(), budgets, &mut io)
            .err()
            .expect("the allocation must exceed the memory budget");
        assert!(err.contains("memory budget"), "{err}");
    }

    #[test]
    fn run_export_passes_scalar_args() {
        let module = export_module(
            Chunk {
                name: "add".into(),
                code: vec![
                    Insn::Add {
                        dest: 2,
                        a: 0,
                        b: 1,
                    },
                    Insn::Ret { src: 2 },
                ],
                arity: 2,
                n_regs: 3,
                unwind: vec![],
            },
            "add",
        );
        let mut io = CaptureIO::default();
        let outcome = run_export(
            &module,
            "add",
            &[HostValue::Int(40), HostValue::Int(2)],
            export_shape(),
            Budgets::default(),
            &mut io,
        )
        .expect("run");
        assert_eq!(outcome.value, Value::I64(42));
    }

    #[test]
    fn run_export_with_stats_reports_emitted_and_executed_instructions() {
        let module = export_module(
            Chunk {
                name: "add".into(),
                code: vec![
                    Insn::Add {
                        dest: 2,
                        a: 0,
                        b: 1,
                    },
                    Insn::Ret { src: 2 },
                ],
                arity: 2,
                n_regs: 3,
                unwind: vec![],
            },
            "add",
        );
        let mut io = CaptureIO::default();
        let mut stats = VmStats::for_module(&module);
        let outcome = run_export_with_stats(
            &module,
            "add",
            &[HostValue::Int(40), HostValue::Int(2)],
            export_shape(),
            Budgets::default(),
            &mut io,
            &mut stats,
        )
        .expect("run");

        assert_eq!(outcome.value, Value::I64(42));
        assert_eq!(stats.runs(), 1);
        assert_eq!(stats.emitted_instructions(), 2);
        assert_eq!(stats.executed_instructions(), 2);
        assert_eq!(stats.chunks()[0].instruction_executions(), &[1, 1]);
        assert_eq!(
            stats
                .opcode_stats()
                .into_iter()
                .map(|opcode| (opcode.opcode, opcode.emitted, opcode.executed))
                .collect::<Vec<_>>(),
            vec![("Add", 1, 1), ("Ret", 1, 1)]
        );
        assert!(stats.render().contains("hottest instruction sites"));
    }

    #[test]
    fn run_export_with_stats_keeps_counts_after_a_trap() {
        let module = export_module(
            Chunk {
                name: "spin".into(),
                code: vec![Insn::Jump { target: 0 }],
                arity: 0,
                n_regs: 1,
                unwind: vec![],
            },
            "spin",
        );
        let mut io = CaptureIO::default();
        let mut stats = VmStats::default();
        let budgets = Budgets {
            instructions: 10,
            ..Budgets::default()
        };
        let err = run_export_with_stats(
            &module,
            "spin",
            &[],
            export_shape(),
            budgets,
            &mut io,
            &mut stats,
        )
        .err()
        .expect("the loop must exhaust its budget");

        assert!(err.contains("instruction budget"), "{err}");
        assert_eq!(stats.runs(), 1);
        assert_eq!(stats.emitted_instructions(), 1);
        assert_eq!(stats.executed_instructions(), 10);
        assert_eq!(stats.chunks()[0].instruction_executions(), &[10]);
    }

    #[test]
    fn run_export_round_trips_string_arg() {
        // Host strings need the module's published String layout; a
        // module without one fails closed rather than fabricating a
        // representation the callee cannot read.
        let strings = export_shape();
        let chunk = Chunk {
            name: "id".into(),
            code: vec![Insn::Ret { src: 0 }],
            arity: 1,
            n_regs: 1,
            unwind: vec![],
        };
        let bare = export_module(chunk, "id");
        let mut io = CaptureIO::default();
        let err = run_export(
            &bare,
            "id",
            &[HostValue::String(b"hello".to_vec())],
            strings,
            Budgets::default(),
            &mut io,
        )
        .err()
        .expect("no published String layout");
        assert!(err.contains("String layout"), "{err}");

        let mut module = bare;
        module.layouts = vec![
            LayoutDesc {
                symbol: Some(export_sym(2)),
                width: 1,
                body: LayoutBody::Product(vec![(0, FieldShape::Slot)]),
            },
            LayoutDesc {
                symbol: Some(strings),
                width: 3,
                body: LayoutBody::Product(vec![
                    (0, FieldShape::Spliced(0)),
                    (1, FieldShape::Slot),
                    (2, FieldShape::Slot),
                ]),
            },
        ];
        let mut io = CaptureIO::default();
        let outcome = run_export(
            &module,
            "id",
            &[HostValue::String(b"hello".to_vec())],
            strings,
            Budgets::default(),
            &mut io,
        )
        .expect("run");
        assert_eq!(
            outcome.string_bytes(&outcome.value).expect("string"),
            b"hello"
        );
    }

    #[test]
    fn run_export_rejects_unknown_name_and_bad_arity() {
        let module = export_module(
            Chunk {
                name: "id".into(),
                code: vec![Insn::Ret { src: 0 }],
                arity: 1,
                n_regs: 1,
                unwind: vec![],
            },
            "id",
        );
        let mut io = CaptureIO::default();
        let unknown = run_export(
            &module,
            "nope",
            &[],
            export_shape(),
            Budgets::default(),
            &mut io,
        )
        .err()
        .expect("unknown export should error");
        assert!(unknown.contains("no exported function"), "{unknown}");

        let mut io = CaptureIO::default();
        let arity = run_export(
            &module,
            "id",
            &[],
            export_shape(),
            Budgets::default(),
            &mut io,
        )
        .err()
        .expect("arity mismatch should error");
        assert!(arity.contains("takes 1 arguments"), "{arity}");
    }

    #[test]
    fn itob_converts_in_range_int() {
        let mut io = CaptureIO::default();
        let (value, _machine) =
            run_machine(&itob_module(Constant::I64(65)), &mut io).expect("vm run");
        assert_eq!(value, Value::Byte(65));
    }

    #[test]
    fn itob_rejects_out_of_range_int() {
        for out_of_range in [-1, 256] {
            let mut io = CaptureIO::default();
            let err = run_machine(&itob_module(Constant::I64(out_of_range)), &mut io)
                .err()
                .expect("expected an itob range error");
            assert!(err.contains("itob"), "unexpected error: {err}");
        }
    }

    /// main: build two objects, link them into a cycle, mutate through one
    /// alias, read through the other, release both. Finalizers (chunk 1)
    /// write a byte to fd 1 so the walk is observable.
    fn object_module(with_finalizers: bool) -> Module {
        let mut code = vec![
            Insn::Const { dest: 0, k: 0 }, // 10
            Insn::ObjectNew {
                dest: 1,
                args_start: 0,
                args_len: 1,
            }, // a = { 10 }
            Insn::ObjectNew {
                dest: 2,
                args_start: 0,
                args_len: 1,
            }, // b = { 10 }
        ];
        if with_finalizers {
            code.push(Insn::MakeClosure {
                dest: 7,
                chunk: 1,
                args_start: 1,
                args_len: 0,
            });
            code.push(Insn::SetFinalizer { obj: 1, closure: 7 });
            code.push(Insn::SetFinalizer { obj: 2, closure: 7 });
        }
        code.extend([
            // a.f = b; b.f = a — cycle, regions merge.
            Insn::ObjectSet {
                obj: 1,
                src: 2,
                index: 0,
            },
            Insn::ObjectSet {
                obj: 2,
                src: 1,
                index: 0,
            },
            // Mutation visible through the alias: (a.f).f is a — set a's
            // payload via b: b.f = a, so object_get b[0] aliases a.
            Insn::ObjectGet {
                dest: 3,
                obj: 2,
                index: 0,
            }, // r3 = a (via b)
            Insn::Const { dest: 4, k: 1 }, // 42… but store into a fresh field slot
            // Release both rvalue owners; region should stay alive only
            // while owned.
            Insn::RegionRelease { dest: 5, src: 1 },
            Insn::RegionRelease { dest: 5, src: 2 },
            Insn::Const { dest: 6, k: 1 },
            Insn::Ret { src: 6 },
        ]);
        Module {
            chunks: vec![
                Chunk {
                    name: "main".into(),
                    code,
                    arity: 0,
                    n_regs: 8,
                    unwind: vec![],
                },
                // Finalizer: λ(self) — read a field (memory must still be
                // live mid-walk), write one byte, return void.
                Chunk {
                    name: "fin".into(),
                    code: vec![
                        Insn::ObjectGet {
                            dest: 5,
                            obj: 0,
                            index: 0,
                        },
                        Insn::Const { dest: 1, k: 2 }, // fd 1
                        Insn::Const { dest: 2, k: 3 }, // static offset 0
                        Insn::Const { dest: 3, k: 2 }, // len 1
                        Insn::Io {
                            dest: 4,
                            op: crate::IoOp::Write,
                            a: 1,
                            b: 2,
                            c: 3,
                        },
                        Insn::Ret { src: 4 },
                    ],
                    arity: 1,
                    n_regs: 6,
                    unwind: vec![],
                },
            ],
            consts: vec![
                Constant::I64(10),
                Constant::I64(42),
                Constant::I64(1),
                Constant::Ptr(0),
            ],
            arg_pool: vec![0],
            switch_pool: vec![],
            traps: vec![],
            statics: vec![b'x'],
            layouts: vec![],
            entry: 0,
            exports: vec![],
        }
    }

    /// The exit op ends the run under every host. `StdioIO` never returns
    /// from `process::exit`, so Core follows its exit requests with an idle
    /// `loop {}` to type the tail as `Never` (`Host.tlk`'s panic fallback,
    /// `IO.tlk`'s `_io_exit`). A host that returned a value instead would
    /// drop the VM into that loop and spin forever.
    #[test]
    fn the_exit_op_ends_the_run_under_a_capturing_host() {
        let module = Module {
            chunks: vec![Chunk {
                name: "main".into(),
                code: vec![
                    Insn::Const { dest: 0, k: 0 }, // exit code 3
                    Insn::Io {
                        dest: 1,
                        op: crate::IoOp::Exit,
                        a: 0,
                        b: 0,
                        c: 0,
                    },
                    // Stands in for Core's `loop {}`: reached only if the
                    // exit op hands control back.
                    Insn::Jump { target: 1 },
                ],
                arity: 0,
                n_regs: 2,
                unwind: vec![],
            }],
            consts: vec![Constant::I64(3)],
            arg_pool: vec![],
            switch_pool: vec![],
            traps: vec![],
            statics: vec![],
            layouts: vec![],
            entry: 0,
            exports: vec![],
        };

        let mut io = CaptureIO::default();
        let Err(error) = run_machine(&module, &mut io) else {
            panic!("exit handed control back to the VM");
        };
        assert!(error.contains("exited with code 3"), "{error}");
    }

    #[test]
    fn cycle_frees_at_last_release() {
        let (value, live, _) = run_with_machine(&object_module(false));
        assert_eq!(value, Value::I64(42));
        assert_eq!(live, 0, "cyclic region freed when both owners released");
    }

    #[test]
    fn finalizers_pump_as_frames_before_free() {
        let (value, live, out_len) = run_with_machine(&object_module(true));
        assert_eq!(value, Value::I64(42));
        assert_eq!(live, 0);
        assert_eq!(out_len, 2, "one finalizer write per object");
    }

    #[test]
    fn boxed_store_reuses_the_cell_slot() {
        // Overwriting a boxed cell must not grow the arena: a loop that
        // stores into the same element would otherwise leak one slot per
        // iteration for the machine's lifetime.
        let module = Module {
            chunks: vec![Chunk {
                name: "main".into(),
                code: vec![
                    Insn::Const { dest: 0, k: 0 }, // 8 bytes
                    Insn::Alloc { dest: 1, count: 0 },
                    Insn::Const { dest: 2, k: 1 }, // 111
                    Insn::Store {
                        ptr: 1,
                        src: 2,
                        kind: MemKind::Boxed,
                    },
                    Insn::Const { dest: 3, k: 2 }, // 222
                    Insn::Store {
                        ptr: 1,
                        src: 3,
                        kind: MemKind::Boxed,
                    },
                    Insn::Store {
                        ptr: 1,
                        src: 3,
                        kind: MemKind::Boxed,
                    },
                    Insn::Load {
                        dest: 4,
                        ptr: 1,
                        kind: MemKind::Boxed,
                    },
                    Insn::Ret { src: 4 },
                ],
                arity: 0,
                n_regs: 5,
                unwind: vec![],
            }],
            consts: vec![Constant::I64(8), Constant::I64(111), Constant::I64(222)],
            arg_pool: vec![0],
            switch_pool: vec![],
            traps: vec![],
            statics: vec![],
            layouts: vec![],
            entry: 0,
            exports: vec![],
        };
        let mut io = CaptureIO::default();
        let (value, machine) = run_machine(&module, &mut io).expect("vm run");
        assert_eq!(value, Value::I64(222), "load sees the latest store");
        assert!(
            machine.boxed.len() <= 2,
            "three stores to one cell must reuse its slot, arena has {} slots",
            machine.boxed.len()
        );
    }

    #[test]
    fn aliased_mutation_is_visible() {
        // a = {0}; b = a (alias via object handle copy); a.f = 42; read b.f.
        let module = Module {
            chunks: vec![Chunk {
                name: "main".into(),
                code: vec![
                    Insn::Const { dest: 0, k: 0 },
                    Insn::ObjectNew {
                        dest: 1,
                        args_start: 0,
                        args_len: 1,
                    },
                    Insn::Move { dest: 2, src: 1 }, // alias
                    Insn::Const { dest: 3, k: 1 },  // 42
                    Insn::ObjectSet {
                        obj: 1,
                        src: 3,
                        index: 0,
                    },
                    Insn::ObjectGet {
                        dest: 4,
                        obj: 2,
                        index: 0,
                    },
                    Insn::Ret { src: 4 },
                ],
                arity: 0,
                n_regs: 5,
                unwind: vec![],
            }],
            consts: vec![Constant::I64(0), Constant::I64(42)],
            arg_pool: vec![0],
            switch_pool: vec![],
            traps: vec![],
            statics: vec![],
            layouts: vec![],
            entry: 0,
            exports: vec![],
        };
        let (value, _, _) = run_with_machine(&module);
        assert_eq!(
            value,
            Value::I64(42),
            "mutation through one alias visible through the other"
        );
    }

    #[test]
    fn call_cont_on_the_executing_frame_delivers_in_place() {
        // A frame aborting to its own continuation (target == executing
        // frame) returns the value in place, as a Ret would — its drops
        // already ran on the path to the abort, so no unwind entry runs
        // and no walk starts.
        let module = Module {
            chunks: vec![Chunk {
                name: "main".into(),
                code: vec![
                    Insn::MakeCont { dest: 0 },
                    Insn::Const { dest: 1, k: 0 },
                    Insn::CallCont { callee: 0, src: 1 },
                    Insn::Trap { message: 0 },
                ],
                arity: 0,
                n_regs: 2,
                unwind: vec![],
            }],
            consts: vec![Constant::I64(7)],
            arg_pool: vec![0],
            switch_pool: vec![],
            traps: vec!["vm: resumed past a same-frame abort".into()],
            statics: vec![],
            layouts: vec![],
            entry: 0,
            exports: vec![],
        };
        let mut io = CaptureIO::default();
        let value = run(&module, &mut io).expect("same-frame CallCont delivers its value");
        assert_eq!(value, Value::I64(7));
    }

    fn flat_sym(id: u32) -> Symbol {
        Symbol::Struct(crate::symbol::ModuleSymbolId::new(
            crate::symbol::ModuleId(7),
            id,
        ))
    }

    fn flat_module(
        layouts: Vec<LayoutDesc>,
        code: Vec<Insn>,
        consts: Vec<Constant>,
        arg_pool: Vec<u16>,
    ) -> Module {
        Module {
            chunks: vec![Chunk {
                name: "main".into(),
                code,
                arity: 0,
                n_regs: 8,
                unwind: vec![],
            }],
            consts,
            arg_pool,
            layouts,
            ..Module::default()
        }
    }

    fn pair_layout() -> LayoutDesc {
        LayoutDesc {
            symbol: Some(flat_sym(1)),
            width: 2,
            body: LayoutBody::Product(vec![(0, FieldShape::Slot), (1, FieldShape::Slot)]),
        }
    }

    #[test]
    fn flat_constructions_read_by_offset() {
        let module = flat_module(
            vec![pair_layout()],
            vec![
                Insn::Const { dest: 0, k: 0 },
                Insn::Const { dest: 1, k: 1 },
                Insn::AggNew {
                    dest: 2,
                    layout: 0,
                    tag: 0,
                    args_start: 0,
                    args_len: 2,
                },
                Insn::Field {
                    dest: 3,
                    src: 2,
                    offset: 1,
                    layout: NO_LAYOUT,
                },
                Insn::Ret { src: 3 },
            ],
            vec![Constant::I64(4), Constant::I64(9)],
            vec![0, 1],
        );
        let (value, ..) = run_with_machine(&module);
        assert_eq!(value, Value::I64(9));
    }

    #[test]
    fn spliced_children_share_the_parents_allocation_and_reconstitute() {
        // Outer { p: Pair, z: Int }: the Pair lives flat inside Outer's
        // slots. A FieldIndex read of the spliced field reconstitutes
        // a Pair aggregate through the descriptor.
        let outer = LayoutDesc {
            symbol: Some(flat_sym(2)),
            width: 3,
            body: LayoutBody::Product(vec![(0, FieldShape::Spliced(0)), (2, FieldShape::Slot)]),
        };
        let module = flat_module(
            vec![pair_layout(), outer],
            vec![
                Insn::Const { dest: 0, k: 0 },
                Insn::Const { dest: 1, k: 1 },
                Insn::Const { dest: 2, k: 2 },
                Insn::AggNew {
                    dest: 3,
                    layout: 0,
                    tag: 0,
                    args_start: 0,
                    args_len: 2,
                },
                Insn::AggNew {
                    dest: 4,
                    layout: 1,
                    tag: 0,
                    args_start: 2,
                    args_len: 2,
                },
                Insn::Ret { src: 4 },
            ],
            vec![Constant::I64(1), Constant::I64(2), Constant::I64(3)],
            vec![0, 1, 3, 2],
        );
        let (value, ..) = run_with_machine(&module);
        assert_eq!(
            value,
            Value::Agg(
                1,
                Rc::new(vec![Value::I64(1), Value::I64(2), Value::I64(3)])
            )
        );
    }

    #[test]
    fn index_reads_translate_through_the_descriptor() {
        let outer = LayoutDesc {
            symbol: Some(flat_sym(2)),
            width: 3,
            body: LayoutBody::Product(vec![(0, FieldShape::Spliced(0)), (2, FieldShape::Slot)]),
        };
        let module = flat_module(
            vec![pair_layout(), outer],
            vec![
                Insn::Const { dest: 0, k: 0 },
                Insn::Const { dest: 1, k: 1 },
                Insn::Const { dest: 2, k: 2 },
                Insn::AggNew {
                    dest: 3,
                    layout: 0,
                    tag: 0,
                    args_start: 0,
                    args_len: 2,
                },
                Insn::AggNew {
                    dest: 4,
                    layout: 1,
                    tag: 0,
                    args_start: 2,
                    args_len: 2,
                },
                // Logical index 0 is the spliced Pair; its own field 1
                // reads by offset out of the reconstituted child.
                Insn::FieldIndex {
                    dest: 5,
                    src: 4,
                    index: 0,
                },
                Insn::Field {
                    dest: 6,
                    src: 5,
                    offset: 1,
                    layout: NO_LAYOUT,
                },
                Insn::Ret { src: 6 },
            ],
            vec![Constant::I64(1), Constant::I64(2), Constant::I64(3)],
            vec![0, 1, 3, 2],
        );
        let (value, ..) = run_with_machine(&module);
        assert_eq!(value, Value::I64(2));
    }

    #[test]
    fn flat_sums_stamp_their_tag_and_translate_payload_reads() {
        // Opt: none | some(Int). Tag at slot 0, payload at slot 1.
        let opt = LayoutDesc {
            symbol: Some(flat_sym(3)),
            width: 2,
            body: LayoutBody::Sum(vec![vec![], vec![(1, FieldShape::Slot)]]),
        };
        let module = flat_module(
            vec![opt],
            vec![
                Insn::Const { dest: 0, k: 0 },
                Insn::AggNew {
                    dest: 1,
                    layout: 0,
                    tag: 1,
                    args_start: 0,
                    args_len: 1,
                },
                Insn::GetTag { dest: 2, src: 1 },
                Insn::Field {
                    dest: 3,
                    src: 1,
                    offset: 1,
                    layout: NO_LAYOUT,
                },
                Insn::Add {
                    dest: 4,
                    a: 2,
                    b: 3,
                },
                Insn::Ret { src: 4 },
            ],
            vec![Constant::I64(41)],
            vec![0],
        );
        let (value, ..) = run_with_machine(&module);
        assert_eq!(value, Value::I64(42));
    }

    #[test]
    fn blank_receivers_stay_flat_and_set_field_fills_them() {
        // An init receiver: every field Unit until assigned. The spliced
        // Storage-like child starts as a blank span and a FieldIndex
        // `SetField` fills it copy-on-write.
        let storage = LayoutDesc {
            symbol: Some(flat_sym(4)),
            width: 1,
            body: LayoutBody::Product(vec![(0, FieldShape::Slot)]),
        };
        let outer = LayoutDesc {
            symbol: Some(flat_sym(5)),
            width: 2,
            body: LayoutBody::Product(vec![(0, FieldShape::Spliced(0)), (1, FieldShape::Slot)]),
        };
        let unit = crate::RK_CONST | 0;
        let module = flat_module(
            vec![storage, outer],
            vec![
                // The blank cell: unit constants in both fields.
                Insn::AggNew {
                    dest: 0,
                    layout: 1,
                    tag: 0,
                    args_start: 0,
                    args_len: 2,
                },
                Insn::Const { dest: 1, k: 1 },
                Insn::AggNew {
                    dest: 2,
                    layout: 0,
                    tag: 0,
                    args_start: 2,
                    args_len: 1,
                },
                Insn::SetField {
                    dest: 0,
                    rec: 0,
                    src: 2,
                    offset: 0,
                    layout: 0,
                },
                Insn::SetField {
                    dest: 0,
                    rec: 0,
                    src: 1,
                    offset: 1,
                    layout: NO_LAYOUT,
                },
                Insn::Field {
                    dest: 3,
                    src: 0,
                    offset: 1,
                    layout: NO_LAYOUT,
                },
                Insn::Field {
                    dest: 4,
                    src: 0,
                    offset: 0,
                    layout: 0,
                },
                Insn::Field {
                    dest: 5,
                    src: 4,
                    offset: 0,
                    layout: NO_LAYOUT,
                },
                Insn::Add {
                    dest: 6,
                    a: 3,
                    b: 5,
                },
                Insn::Ret { src: 6 },
            ],
            vec![Constant::Void, Constant::I64(5), Constant::I64(7)],
            vec![unit, unit, crate::RK_CONST | 2],
        );
        let (value, ..) = run_with_machine(&module);
        assert_eq!(value, Value::I64(12));
    }

    #[test]
    fn flat_aggregates_render_through_their_layouts() {
        let outer = LayoutDesc {
            symbol: Some(flat_sym(2)),
            width: 3,
            body: LayoutBody::Product(vec![(0, FieldShape::Spliced(0)), (2, FieldShape::Slot)]),
        };
        let opt = LayoutDesc {
            symbol: Some(flat_sym(3)),
            width: 3,
            body: LayoutBody::Sum(vec![vec![], vec![(1, FieldShape::Spliced(0))]]),
        };
        let module = flat_module(
            vec![pair_layout(), outer, opt],
            vec![
                Insn::Const { dest: 0, k: 0 },
                Insn::Const { dest: 1, k: 1 },
                Insn::AggNew {
                    dest: 2,
                    layout: 0,
                    tag: 0,
                    args_start: 0,
                    args_len: 2,
                },
                Insn::AggNew {
                    dest: 3,
                    layout: 2,
                    tag: 1,
                    args_start: 2,
                    args_len: 1,
                },
                Insn::Ret { src: 3 },
            ],
            vec![Constant::I64(4), Constant::I64(9)],
            vec![0, 1, 2],
        );
        let mut names = ValueNames::default();
        names.types.insert(flat_sym(1), "Pair".into());
        names
            .fields
            .insert(flat_sym(1), vec!["x".into(), "y".into()]);
        names.types.insert(flat_sym(3), "Opt".into());
        names
            .cases
            .insert(flat_sym(3), vec!["none".into(), "some".into()]);
        let mut io = CaptureIO::default();
        let (_, rendered) = run_displayed(&module, &mut io, &names).expect("vm run");
        assert_eq!(rendered, "Opt.some(Pair(x: 4, y: 9))");
    }

    #[test]
    fn host_string_arguments_arrive_flat_when_the_module_publishes_layouts() {
        let strings = export_shape();
        let storage = LayoutDesc {
            symbol: Some(export_sym(2)),
            width: 1,
            body: LayoutBody::Product(vec![(0, FieldShape::Slot)]),
        };
        let string = LayoutDesc {
            symbol: Some(strings),
            width: 3,
            body: LayoutBody::Product(vec![
                (0, FieldShape::Spliced(0)),
                (1, FieldShape::Slot),
                (2, FieldShape::Slot),
            ]),
        };
        let module = Module {
            chunks: vec![Chunk {
                name: "echo".into(),
                code: vec![Insn::Ret { src: 0 }],
                arity: 1,
                n_regs: 1,
                unwind: vec![],
            }],
            layouts: vec![storage, string],
            exports: vec![("echo".into(), 0)],
            ..Module::default()
        };
        let mut io = CaptureIO::default();
        let outcome = run_export(
            &module,
            "echo",
            &[HostValue::String(b"hi".to_vec())],
            strings,
            Budgets::default(),
            &mut io,
        )
        .expect("export run");
        assert!(
            matches!(outcome.value, Value::Agg(1, _)),
            "{:?}",
            outcome.value
        );
        assert_eq!(outcome.string_bytes(&outcome.value).expect("string"), b"hi");
    }
}
