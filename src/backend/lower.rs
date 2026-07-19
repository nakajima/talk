//! MIR to runtime-bytecode lowering.
//!
//! Target mechanics only: MIR locals map one-to-one onto frame registers,
//! constants materialize through a deduplicated pool, and blocks linearize
//! with jump patching. Semantic decisions all happened in MIR.

use rustc_hash::FxHashMap;
use talk_runtime::{Chunk, CmpOp, Insn, IoOp, MemKind, Module, interp::Value};

use super::BackendError;
use super::mir::{
    BlockData, CmpKind, Constant, Function, Inst, MemTy, Operand, Program, ScalarOp, Term,
};
use crate::name_resolution::symbol::Symbol as CompilerSymbol;

fn mem_kind(kind: MemTy) -> MemKind {
    match kind {
        MemTy::Byte => MemKind::Byte,
        MemTy::I64 => MemKind::I64,
        MemTy::F64 => MemKind::F64,
        MemTy::Bool => MemKind::Bool,
        MemTy::Ptr => MemKind::Ptr,
        MemTy::Boxed => MemKind::Boxed,
    }
}
use crate::parsing::span::Span;

/// Compiler symbols carried into runtime values (variant/record identity
/// and display) use the runtime's own symbol type; identities map
/// one-to-one.
pub(crate) fn runtime_symbol(
    symbol: crate::name_resolution::symbol::Symbol,
) -> talk_runtime::symbol::Symbol {
    use crate::name_resolution::symbol::Symbol as C;
    use talk_runtime::symbol::{LocalSymbolId, ModuleId, ModuleSymbolId, Symbol as R};
    let module = |id: crate::compiling::module::ModuleId| ModuleId(id.0);
    match symbol {
        C::Struct(id) => R::Struct(ModuleSymbolId::new(module(id.module_id), id.local_id)),
        C::Enum(id) => R::Enum(ModuleSymbolId::new(module(id.module_id), id.local_id)),
        C::Builtin(id) => R::Builtin(ModuleSymbolId::new(module(id.module_id), id.local_id)),
        C::Variant(id) => R::Variant(ModuleSymbolId::new(module(id.module_id), id.local_id)),
        C::Global(id) => R::Global(ModuleSymbolId::new(module(id.module_id), id.local_id)),
        C::Protocol(id) => R::Protocol(ModuleSymbolId::new(module(id.module_id), id.local_id)),
        C::DeclaredLocal(id) => R::DeclaredLocal(LocalSymbolId(id.0)),
        _ => R::Library,
    }
}

pub(crate) fn lower(program: &Program) -> Result<Module, BackendError> {
    let mut module = Module {
        entry: u32::try_from(program.entry).unwrap_or_default(),
        ..Module::default()
    };
    let mut consts = ConstPool::default();
    let mut traps = TrapPool::default();
    let mut statics = StaticsPool::default();
    let mut effects = EffectPool::default();
    // Program globals occupy the front of static memory, one 8-byte Boxed
    // slot each (reads before initialization trap on the reserved
    // placeholder handle).
    module.statics.resize(
        usize::try_from(program.global_slots).unwrap_or_default() * 8,
        0,
    );

    for function in &program.functions {
        let chunk = lower_function(
            function,
            &mut module,
            &mut consts,
            &mut traps,
            &mut statics,
            &mut effects,
        )?;
        module.chunks.push(chunk);
    }
    module.consts = consts.values;
    module.traps = traps.messages;
    Ok(module)
}

#[derive(Default)]
struct ConstPool {
    values: Vec<Value>,
    ids: FxHashMap<ConstKey, u32>,
}

/// Constants dedup by bit pattern so `f64` keys stay `Eq`.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
enum ConstKey {
    Unit,
    Bool(bool),
    Int(i64),
    Float(u64),
    Ptr(u32),
}

impl ConstPool {
    fn intern(&mut self, constant: Constant) -> u32 {
        let (key, value) = match constant {
            Constant::Unit => (ConstKey::Unit, Value::Void),
            Constant::Bool(value) => (ConstKey::Bool(value), Value::Bool(value)),
            Constant::Int(value) => (ConstKey::Int(value), Value::I64(value)),
            Constant::Float(value) => (ConstKey::Float(value.to_bits()), Value::F64(value)),
        };
        self.intern_pair(key, value)
    }

    fn intern_ptr(&mut self, address: u32) -> u32 {
        self.intern_pair(ConstKey::Ptr(address), Value::Ptr(address))
    }

    fn intern_pair(&mut self, key: ConstKey, value: Value) -> u32 {
        *self.ids.entry(key).or_insert_with(|| {
            self.values.push(value);
            u32::try_from(self.values.len() - 1).unwrap_or_default()
        })
    }
}

/// Immortal static byte data (string literal text), deduplicated.
#[derive(Default)]
struct StaticsPool {
    offsets: FxHashMap<Vec<u8>, u32>,
}

impl StaticsPool {
    fn intern(&mut self, module: &mut Module, bytes: &[u8]) -> u32 {
        if let Some(offset) = self.offsets.get(bytes) {
            return *offset;
        }
        let offset = u32::try_from(module.statics.len()).unwrap_or_default();
        module.statics.extend_from_slice(bytes);
        self.offsets.insert(bytes.to_vec(), offset);
        offset
    }
}

/// Effect symbols interned to runtime effect ids.
#[derive(Default)]
struct EffectPool {
    ids: FxHashMap<CompilerSymbol, u32>,
}

impl EffectPool {
    fn intern(&mut self, effect: CompilerSymbol) -> u32 {
        let next = u32::try_from(self.ids.len()).unwrap_or_default();
        *self.ids.entry(effect).or_insert(next)
    }
}

#[derive(Default)]
struct TrapPool {
    messages: Vec<String>,
    ids: FxHashMap<&'static str, u32>,
}

impl TrapPool {
    fn intern(&mut self, message: &'static str) -> u32 {
        *self.ids.entry(message).or_insert_with(|| {
            self.messages.push(message.into());
            u32::try_from(self.messages.len() - 1).unwrap_or_default()
        })
    }
}

fn lower_function(
    function: &Function,
    module: &mut Module,
    consts: &mut ConstPool,
    traps: &mut TrapPool,
    statics: &mut StaticsPool,
    effects: &mut EffectPool,
) -> Result<Chunk, BackendError> {
    let mut lowering = Lowering {
        code: Vec::new(),
        next_reg: function.n_locals,
        scratch_floor: function.n_locals,
        function_floor: function.n_locals,
        block_consts: FxHashMap::default(),
        max_reg: function.n_locals,
        consts,
        traps,
        statics,
        effects,
        module,
        block_params: function
            .blocks
            .iter()
            .map(|block| block.params.clone())
            .collect(),
        block_starts: vec![0; function.blocks.len()],
        patches: Vec::new(),
        unwind_sites: Vec::new(),
    };

    for (block_id, block) in function.blocks.iter().enumerate() {
        lowering.block_starts[block_id] = lowering.pc();
        lowering.lower_block(block)?;
    }
    lowering.patch();

    // Suspension pc -> cleanup entry pc, sorted by suspension (the
    // decoder's unwind-table shape).
    let mut unwind: Vec<(u32, u32)> = lowering
        .unwind_sites
        .iter()
        .map(|(pc, block)| (*pc, lowering.block_starts[*block]))
        .collect();
    thread_and_compact(&mut lowering.code, &mut unwind);
    unwind.sort_unstable_by_key(|(suspension, _)| *suspension);

    let n_regs = lowering.max_reg.max(function.arity).max(1);
    Ok(Chunk {
        name: function.name.clone(),
        code: lowering.code,
        arity: function.arity,
        n_regs,
        unwind,
    })
}

/// Jump threading and fallthrough compaction: every control target
/// chases through chains of bare jumps (the residue of empty blocks
/// and inline splices), and a jump to the immediately following pc is
/// deleted, with every surviving target and unwind entry renumbered.
fn thread_and_compact(code: &mut Vec<Insn>, unwind: &mut [(u32, u32)]) {
    // Removing a jump can turn another jump into a fallthrough; a few
    // rounds reach the fixpoint.
    for _ in 0..8 {
        let before = code.len();
        thread_and_compact_once(code, unwind);
        if code.len() == before {
            break;
        }
    }
}

fn thread_and_compact_once(code: &mut Vec<Insn>, unwind: &mut [(u32, u32)]) {
    let chase = |code: &[Insn], start: u32| -> u32 {
        let mut target = start;
        // A hop cap guards degenerate jump cycles (`loop {}`).
        for _ in 0..64 {
            match code.get(target as usize) {
                Some(Insn::Jump { target: next }) => target = *next,
                _ => break,
            }
        }
        target
    };
    for pc in 0..code.len() {
        let threaded = match &code[pc] {
            Insn::Jump { target } => Some((chase(code, *target), 0, false)),
            Insn::Branch {
                then_target,
                else_target,
                ..
            } => Some((chase(code, *then_target), chase(code, *else_target), true)),
            _ => None,
        };
        match (threaded, &mut code[pc]) {
            (Some((target, _, false)), Insn::Jump { target: slot }) => *slot = target,
            (
                Some((then_threaded, else_threaded, true)),
                Insn::Branch {
                    then_target,
                    else_target,
                    ..
                },
            ) => {
                *then_target = then_threaded;
                *else_target = else_threaded;
            }
            _ => {}
        }
    }
    for (_, cleanup) in unwind.iter_mut() {
        *cleanup = chase(code, *cleanup);
    }
    // Compact away jumps to the next pc.
    let mut new_pc: Vec<u32> = Vec::with_capacity(code.len());
    let mut kept: u32 = 0;
    for (pc, insn) in code.iter().enumerate() {
        new_pc.push(kept);
        let falls_through = matches!(
            insn,
            Insn::Jump { target } if *target as usize == pc + 1
        );
        if !falls_through {
            kept += 1;
        }
    }
    // The one-past-the-end position maps too (an unwind suspension pc
    // can point past a chunk-final call).
    new_pc.push(kept);
    let remap = |pc: u32, new_pc: &[u32]| new_pc[pc as usize];
    let mut index = 0usize;
    code.retain(|insn| {
        let keep = !matches!(insn, Insn::Jump { target } if *target as usize == index + 1);
        index += 1;
        keep
    });
    for insn in code.iter_mut() {
        match insn {
            Insn::Jump { target } => *target = remap(*target, &new_pc),
            Insn::Branch {
                then_target,
                else_target,
                ..
            } => {
                *then_target = remap(*then_target, &new_pc);
                *else_target = remap(*else_target, &new_pc);
            }
            _ => {}
        }
    }
    for (suspension, cleanup) in unwind.iter_mut() {
        *suspension = remap(*suspension, &new_pc);
        *cleanup = remap(*cleanup, &new_pc);
    }
}

/// A jump operand waiting for its block's final pc.
enum Patch {
    Jump {
        pc: usize,
        block: usize,
    },
    Branch {
        pc: usize,
        then_block: usize,
        else_block: usize,
    },
}

struct Lowering<'a> {
    code: Vec<Insn>,
    next_reg: u16,
    /// Registers below this are the function's (reuse-renumbered)
    /// locals and the current block's cached constants; above are
    /// per-instruction scratch (address arithmetic, one-shot
    /// materializations). Scratch lives only within one MIR
    /// instruction's lowering, so `next_reg` resets here at each
    /// instruction and the frame keeps its true width.
    scratch_floor: u16,
    /// Registers below this are the function's locals; the band up to
    /// `scratch_floor` holds the current block's cached constants.
    function_floor: u16,
    /// Constant pool id → the register holding it, within the current
    /// block: a constant materializes once per block instead of once
    /// per use (a straight-line slice of lazy code motion — Knoop,
    /// Rüthing & Steffen, PLDI 1992; re-materializing per use is only
    /// ever a register-pressure trade, Briggs, Cooper & Torczon,
    /// PLDI 1992, and frames here are register-unlimited).
    block_consts: FxHashMap<u32, u16>,
    /// High-water mark of every register ever allocated: the chunk's
    /// frame size.
    max_reg: u16,
    consts: &'a mut ConstPool,
    traps: &'a mut TrapPool,
    statics: &'a mut StaticsPool,
    effects: &'a mut EffectPool,
    module: &'a mut Module,
    /// Each block's parameter registers (post-renumbering): `Goto`
    /// lowering emits the edge's parallel copy into these.
    block_params: Vec<Vec<u16>>,
    block_starts: Vec<u32>,
    patches: Vec<Patch>,
    /// (pc after a suspendable call, cleanup block) pairs, resolved into
    /// the chunk's unwind table after layout.
    unwind_sites: Vec<(u32, usize)>,
}

impl Lowering<'_> {
    fn pc(&self) -> u32 {
        u32::try_from(self.code.len()).unwrap_or_default()
    }

    fn reg(&mut self, operand: Operand) -> u16 {
        match operand {
            Operand::Local(local) => local,
            Operand::Const(constant) => {
                let k = self.consts.intern(constant);
                if let Some(&cached) = self.block_consts.get(&k) {
                    return cached;
                }
                let dest = self.fresh_reg();
                self.code.push(Insn::Const { dest, k });
                // The constant's register joins the block-persistent
                // band: later instructions' scratch allocates above it.
                self.scratch_floor = self.scratch_floor.max(dest + 1);
                self.block_consts.insert(k, dest);
                dest
            }
        }
    }

    /// A register-or-constant operand field (RK encoding — Lua 5's
    /// design, Ierusalimschy, de Figueiredo & Celes, J.UCS 2005): a
    /// constant that fits the 15-bit pool index reads the pool
    /// directly and costs no materializing instruction; one that does
    /// not falls back to `reg`.
    fn rk(&mut self, operand: Operand) -> u16 {
        if let Operand::Const(constant) = operand {
            let k = self.consts.intern(constant);
            if let Ok(index) = u16::try_from(k)
                && index <= talk_runtime::RK_INDEX
            {
                return index | talk_runtime::RK_CONST;
            }
        }
        self.reg(operand)
    }

    /// One `Goto` edge's parallel copy: block-parameter registers
    /// receive the edge arguments as if simultaneously. Emission order
    /// never writes a register another pending move still reads, and a
    /// cycle breaks through one scratch register (out-of-SSA edge
    /// sequentialization — Boissinot, Darte, Rastello, de Dinechin &
    /// Guillon, CGO 2009). Coalescing usually erases these moves: an
    /// argument dying at the edge hints its parameter onto the same
    /// register, and identity moves are skipped here.
    fn edge_moves(&mut self, params: &[u16], args: &[Operand]) {
        let mut pending: Vec<(u16, Operand)> = params
            .iter()
            .zip(args)
            .filter(|(dest, arg)| !matches!(arg, Operand::Local(src) if src == *dest))
            .map(|(dest, arg)| (*dest, *arg))
            .collect();
        while !pending.is_empty() {
            if let Some(ready) = pending.iter().position(|(dest, _)| {
                !pending
                    .iter()
                    .any(|(_, src)| matches!(src, Operand::Local(read) if read == dest))
            }) {
                let (dest, src) = pending.swap_remove(ready);
                match src {
                    Operand::Local(src) => self.code.push(Insn::Move { dest, src }),
                    Operand::Const(constant) => {
                        let k = self.consts.intern(constant);
                        self.code.push(Insn::Const { dest, k });
                    }
                }
                continue;
            }
            // Every pending destination is still read by another pending
            // move: a cycle. Save one destination's current value and
            // redirect its readers to the copy.
            let blocked = pending[0].0;
            let scratch = self.fresh_reg();
            self.code.push(Insn::Move {
                dest: scratch,
                src: blocked,
            });
            for (_, src) in &mut pending {
                if matches!(src, Operand::Local(read) if *read == blocked) {
                    *src = Operand::Local(scratch);
                }
            }
        }
    }

    /// A position that only takes a register: materialize an RK
    /// constant field back into one.
    fn demote_rk(&mut self, field: u16) -> u16 {
        if field & talk_runtime::RK_CONST == 0 {
            return field;
        }
        let k = u32::from(field & talk_runtime::RK_INDEX);
        if let Some(&cached) = self.block_consts.get(&k) {
            return cached;
        }
        let dest = self.fresh_reg();
        self.code.push(Insn::Const { dest, k });
        self.scratch_floor = self.scratch_floor.max(dest + 1);
        self.block_consts.insert(k, dest);
        dest
    }

    fn lower_block(&mut self, block: &BlockData) -> Result<(), BackendError> {
        self.block_consts.clear();
        self.scratch_floor = self.function_floor;
        for inst in &block.insts {
            self.next_reg = self.scratch_floor;
            self.lower_inst(inst)?;
        }
        self.next_reg = self.scratch_floor;
        let Some(term) = &block.term else {
            return Err(BackendError::new(
                "backend bug: unterminated block".into(),
                Span::SYNTHESIZED,
            ));
        };
        match term {
            Term::Goto(target, edge_args) => {
                let params = self.block_params[*target].clone();
                self.edge_moves(&params, edge_args);
                self.patches.push(Patch::Jump {
                    pc: self.code.len(),
                    block: *target,
                });
                self.code.push(Insn::Jump { target: 0 });
            }
            Term::Branch {
                cond,
                then_block,
                else_block,
            } => {
                // The builder routes every merged value through a
                // dedicated arm block's `Goto`, so branch targets never
                // declare parameters and branches never carry arguments.
                if !self.block_params[*then_block].is_empty()
                    || !self.block_params[*else_block].is_empty()
                {
                    return Err(BackendError::new(
                        "backend bug: branch edge into a parameterized block".into(),
                        Span::SYNTHESIZED,
                    ));
                }
                let cond = self.reg(*cond);
                self.patches.push(Patch::Branch {
                    pc: self.code.len(),
                    then_block: *then_block,
                    else_block: *else_block,
                });
                self.code.push(Insn::Branch {
                    cond,
                    then_target: 0,
                    else_target: 0,
                });
            }
            Term::Return(value) => {
                let src = self.reg(*value);
                self.code.push(Insn::Ret { src });
            }
            Term::Trap(message) => {
                let message = self.traps.intern(message);
                self.code.push(Insn::Trap { message });
            }
            Term::UnwindRet => {
                self.code.push(Insn::UnwindRet);
            }
        }
        Ok(())
    }

    fn lower_inst(&mut self, inst: &Inst) -> Result<(), BackendError> {
        match inst {
            Inst::Copy { dest, src } => match src {
                Operand::Local(src) => {
                    if src != dest {
                        self.code.push(Insn::Move {
                            dest: *dest,
                            src: *src,
                        });
                    }
                }
                Operand::Const(constant) => {
                    let k = self.consts.intern(*constant);
                    self.code.push(Insn::Const { dest: *dest, k });
                }
            },
            Inst::Scalar { dest, op, a, b } => {
                let a = self.rk(*a);
                let dest = *dest;
                match (op, b) {
                    (ScalarOp::IntAdd | ScalarOp::FloatAdd, Some(b)) => {
                        let b = self.rk(*b);
                        self.code.push(Insn::Add { dest, a, b });
                    }
                    (ScalarOp::IntSub | ScalarOp::FloatSub, Some(b)) => {
                        let b = self.rk(*b);
                        self.code.push(Insn::Sub { dest, a, b });
                    }
                    (ScalarOp::IntMul | ScalarOp::FloatMul, Some(b)) => {
                        let b = self.rk(*b);
                        self.code.push(Insn::Mul { dest, a, b });
                    }
                    (ScalarOp::IntDiv | ScalarOp::FloatDiv, Some(b)) => {
                        let b = self.rk(*b);
                        self.code.push(Insn::Div { dest, a, b });
                    }
                    (ScalarOp::IntAnd | ScalarOp::ByteAnd, Some(b)) => {
                        let b = self.rk(*b);
                        self.code.push(Insn::And { dest, a, b });
                    }
                    (ScalarOp::IntOr | ScalarOp::ByteOr, Some(b)) => {
                        let b = self.rk(*b);
                        self.code.push(Insn::Or { dest, a, b });
                    }
                    (ScalarOp::IntXor | ScalarOp::ByteXor, Some(b)) => {
                        let b = self.rk(*b);
                        self.code.push(Insn::Xor { dest, a, b });
                    }
                    (ScalarOp::IntShl | ScalarOp::ByteShl, Some(b)) => {
                        let b = self.rk(*b);
                        self.code.push(Insn::Shl { dest, a, b });
                    }
                    (ScalarOp::IntShr | ScalarOp::ByteShr, Some(b)) => {
                        let b = self.rk(*b);
                        self.code.push(Insn::Shr { dest, a, b });
                    }
                    (ScalarOp::IntNot | ScalarOp::ByteNot, None) => {
                        let src = self.demote_rk(a);
                        self.code.push(Insn::Not { dest, src });
                    }
                    (
                        ScalarOp::IntCmp(kind)
                        | ScalarOp::FloatCmp(kind)
                        | ScalarOp::ByteCmp(kind)
                        | ScalarOp::BoolCmp(kind),
                        Some(b),
                    ) => {
                        let b = self.rk(*b);
                        let op = match kind {
                            CmpKind::Eq => CmpOp::Eq,
                            CmpKind::Ne => CmpOp::Ne,
                            CmpKind::Lt => CmpOp::Lt,
                            CmpKind::Le => CmpOp::Le,
                            CmpKind::Gt => CmpOp::Gt,
                            CmpKind::Ge => CmpOp::Ge,
                        };
                        self.code.push(Insn::Cmp { dest, a, b, op });
                    }
                    (ScalarOp::FloatToIntTrunc, None) => {
                        let src = self.demote_rk(a);
                        self.code.push(Insn::Trunc { dest, src });
                    }
                    (ScalarOp::IntToFloat, None) => {
                        let src = self.demote_rk(a);
                        self.code.push(Insn::IToF { dest, src });
                    }
                    (ScalarOp::ByteToInt, None) => {
                        let src = self.demote_rk(a);
                        self.code.push(Insn::BToI { dest, src });
                    }
                    _ => {
                        return Err(BackendError::new(
                            "backend bug: malformed scalar operation".into(),
                            Span::SYNTHESIZED,
                        ));
                    }
                }
            }
            Inst::Call {
                dest,
                func,
                args,
                unwind,
            } => {
                let (args_start, args_len) = self.arg_range(args);
                self.code.push(Insn::Call {
                    dest: *dest,
                    chunk: u32::try_from(*func).unwrap_or_default(),
                    args_start,
                    args_len,
                });
                if let Some(block) = unwind {
                    self.unwind_sites.push((self.pc(), *block));
                }
            }
            Inst::Tuple { dest, args } => {
                let (args_start, args_len) = self.arg_range(args);
                self.code.push(Insn::TupleNew {
                    dest: *dest,
                    args_start,
                    args_len,
                });
            }
            Inst::TupleGet { dest, src, index } => {
                let src = self.reg(*src);
                self.code.push(Insn::Extract {
                    dest: *dest,
                    src,
                    index: *index,
                });
            }
            Inst::Variant {
                dest,
                enum_symbol,
                tag,
                args,
            } => {
                let (args_start, args_len) = self.arg_range(args);
                self.code.push(Insn::VariantNew {
                    dest: *dest,
                    symbol: runtime_symbol(*enum_symbol),
                    tag: *tag,
                    args_start,
                    args_len,
                });
            }
            Inst::GetTag { dest, src } => {
                let src = self.reg(*src);
                self.code.push(Insn::GetTag { dest: *dest, src });
            }
            Inst::GetPayload { dest, src, index } => {
                let src = self.reg(*src);
                self.code.push(Insn::GetPayload {
                    dest: *dest,
                    src,
                    index: *index,
                });
            }
            Inst::Record {
                dest,
                struct_symbol,
                args,
            } => {
                let (args_start, args_len) = self.arg_range(args);
                self.code.push(Insn::RecordNew {
                    dest: *dest,
                    symbol: runtime_symbol(*struct_symbol),
                    args_start,
                    args_len,
                });
            }
            Inst::GetField { dest, src, index } => {
                let rec = self.reg(*src);
                self.code.push(Insn::GetField {
                    dest: *dest,
                    rec,
                    index: *index,
                });
            }
            Inst::SetField { rec, src, index } => {
                let src = self.reg(*src);
                self.code.push(Insn::SetField {
                    dest: *rec,
                    rec: *rec,
                    src,
                    index: *index,
                });
            }
            Inst::StringLit { dest, bytes } => {
                // Literal text is immortal static data; the value is the
                // core String struct over it: String { storage:
                // Storage { base }, byte_count, capacity } (layout owned
                // by core/String.tlk; parity tests pin the shape).
                let offset = self.statics.intern(self.module, bytes);
                let base = self.fresh_reg();
                let k = self.consts.intern_ptr(offset);
                self.code.push(Insn::Const { dest: base, k });
                let storage = self.fresh_reg();
                let (args_start, args_len) = self.reg_range(&[base]);
                self.code.push(Insn::RecordNew {
                    dest: storage,
                    symbol: runtime_symbol(CompilerSymbol::Storage),
                    args_start,
                    args_len,
                });
                let len = self.reg(Operand::Const(Constant::Int(
                    i64::try_from(bytes.len()).unwrap_or_default(),
                )));
                let (args_start, args_len) = self.reg_range(&[storage, len, len]);
                self.code.push(Insn::RecordNew {
                    dest: *dest,
                    symbol: runtime_symbol(CompilerSymbol::String),
                    args_start,
                    args_len,
                });
            }
            Inst::BytesLit { dest, bytes } => {
                let offset = self.statics.intern(self.module, bytes);
                let k = self.consts.intern_ptr(offset);
                self.code.push(Insn::Const { dest: *dest, k });
            }
            Inst::Alloc { dest, bytes } => {
                let count = self.reg(*bytes);
                self.code.push(Insn::Alloc { dest: *dest, count });
            }
            Inst::Free { src } => {
                let ptr = self.reg(*src);
                let dest = self.fresh_reg();
                self.code.push(Insn::Free { dest, ptr });
            }
            Inst::RetainPtr { src } => {
                let ptr = self.reg(*src);
                let dest = self.fresh_reg();
                self.code.push(Insn::Retain { dest, ptr });
            }
            Inst::IsUnique { dest, src } => {
                let ptr = self.reg(*src);
                self.code.push(Insn::IsUnique { dest: *dest, ptr });
            }
            Inst::Load { dest, ptr, kind } => {
                let ptr = self.reg(*ptr);
                self.code.push(Insn::Load {
                    dest: *dest,
                    ptr,
                    kind: mem_kind(*kind),
                });
            }
            Inst::Store { ptr, src, kind } => {
                let ptr = self.reg(*ptr);
                let src = self.reg(*src);
                self.code.push(Insn::Store {
                    ptr,
                    src,
                    kind: mem_kind(*kind),
                });
            }
            Inst::MemCopy { from, to, len } => {
                let from = self.reg(*from);
                let to = self.reg(*to);
                let len = self.reg(*len);
                self.code.push(Insn::Copy { from, to, len });
            }
            Inst::PtrAdd {
                dest,
                ptr,
                offset,
                size,
            } => {
                let ptr = self.reg(*ptr);
                let offset = if *size == 1 {
                    self.reg(*offset)
                } else {
                    let offset = self.reg(*offset);
                    let scale = self.reg(Operand::Const(Constant::Int(i64::from(*size))));
                    let scaled = self.fresh_reg();
                    self.code.push(Insn::Mul {
                        dest: scaled,
                        a: offset,
                        b: scale,
                    });
                    scaled
                };
                self.code.push(Insn::Add {
                    dest: *dest,
                    a: ptr,
                    b: offset,
                });
            }
            Inst::MakeClosure { dest, func, env } => {
                let (args_start, args_len) = self.arg_range(env);
                self.code.push(Insn::MakeClosure {
                    dest: *dest,
                    chunk: u32::try_from(*func).unwrap_or_default(),
                    args_start,
                    args_len,
                });
            }
            Inst::CallIndirect {
                dest,
                callee,
                args,
                unwind,
            } => {
                let callee = self.reg(*callee);
                let (args_start, args_len) = self.arg_range(args);
                self.code.push(Insn::CallIndirect {
                    dest: *dest,
                    callee,
                    args_start,
                    args_len,
                });
                if let Some(block) = unwind {
                    self.unwind_sites.push((self.pc(), *block));
                }
            }
            Inst::SetFinalizer { obj, closure } => {
                let obj = self.reg(*obj);
                let closure = self.reg(*closure);
                self.code.push(Insn::SetFinalizer { obj, closure });
            }
            Inst::CellNew { dest, init } => {
                let init = self.reg(*init);
                self.code.push(Insn::CellNew { dest: *dest, init });
            }
            Inst::CellGet { dest, cell } => {
                let cell = self.reg(*cell);
                self.code.push(Insn::CellGet { dest: *dest, cell });
            }
            Inst::CellSet { cell, src } => {
                let cell = self.reg(*cell);
                let src = self.reg(*src);
                self.code.push(Insn::CellSet { cell, src });
            }
            Inst::EnvGet { dest, index } => {
                self.code.push(Insn::EnvGet {
                    dest: *dest,
                    index: *index,
                });
            }
            Inst::MakeCont { dest } => {
                self.code.push(Insn::MakeCont { dest: *dest });
            }
            Inst::PushHandler {
                effect,
                clause,
                cont,
            } => {
                let effect = self.effects.intern(*effect);
                let clause = self.reg(*clause);
                let cont = self.reg(*cont);
                self.code.push(Insn::PushHandler {
                    effect,
                    clause,
                    cont,
                });
            }
            Inst::FindHandler {
                clause,
                cont,
                index,
                effect,
            } => {
                let effect = self.effects.intern(*effect);
                self.code.push(Insn::FindHandler {
                    clause: *clause,
                    cont: *cont,
                    index: *index,
                    effect,
                });
            }
            Inst::GetFloor { dest } => {
                self.code.push(Insn::GetFloor { dest: *dest });
            }
            Inst::SetFloor { src } => {
                let src = self.reg(*src);
                self.code.push(Insn::SetFloor { src });
            }
            Inst::GlobalLoad { dest, global } => {
                let address = self.fresh_reg();
                let k = self.consts.intern_ptr(global * 8);
                self.code.push(Insn::Const { dest: address, k });
                self.code.push(Insn::Load {
                    dest: *dest,
                    ptr: address,
                    kind: MemKind::Boxed,
                });
            }
            Inst::GlobalStore { global, src } => {
                let src = self.reg(*src);
                let address = self.fresh_reg();
                let k = self.consts.intern_ptr(global * 8);
                self.code.push(Insn::Const { dest: address, k });
                self.code.push(Insn::Store {
                    ptr: address,
                    src,
                    kind: MemKind::Boxed,
                });
            }
            Inst::AbortTo { cont, value } => {
                let callee = self.reg(*cont);
                let src = self.reg(*value);
                self.code.push(Insn::CallCont { callee, src });
            }
            Inst::ExistentialPack {
                dest,
                protocol,
                payload,
                witnesses,
            } => {
                let mut regs = vec![self.reg(*payload)];
                regs.extend(witnesses.iter().map(|witness| self.reg(*witness)));
                let (args_start, args_len) = self.reg_range(&regs);
                self.code.push(Insn::ExistentialPack {
                    dest: *dest,
                    protocol: runtime_symbol(*protocol),
                    args_start,
                    args_len,
                });
            }
            Inst::ExistentialWitness { dest, src, index } => {
                let src = self.reg(*src);
                self.code.push(Insn::ExistentialWitness {
                    dest: *dest,
                    src,
                    index: *index,
                });
            }
            Inst::ExistentialPayload { dest, src } => {
                let src = self.reg(*src);
                self.code
                    .push(Insn::ExistentialPayload { dest: *dest, src });
            }
            Inst::ObjectNew { dest, args } => {
                let (args_start, args_len) = self.arg_range(args);
                self.code.push(Insn::ObjectNew {
                    dest: *dest,
                    args_start,
                    args_len,
                });
            }
            Inst::ObjectGet { dest, src, index } => {
                let obj = self.reg(*src);
                self.code.push(Insn::ObjectGet {
                    dest: *dest,
                    obj,
                    index: *index,
                });
            }
            Inst::ObjectSet { obj, src, index } => {
                let obj = self.reg(*obj);
                let src = self.reg(*src);
                self.code.push(Insn::ObjectSet {
                    obj,
                    src,
                    index: *index,
                });
            }
            Inst::RegionAcquire { src } => {
                let src = self.reg(*src);
                let dest = self.fresh_reg();
                self.code.push(Insn::RegionAcquire { dest, src });
            }
            Inst::RegionRelease { src } => {
                let src = self.reg(*src);
                let dest = self.fresh_reg();
                self.code.push(Insn::RegionRelease { dest, src });
            }
            Inst::Io { dest, op, a, b, c } => {
                // Core `IORequest` variant order maps one-to-one onto the
                // runtime operation table.
                const IO_OPS: [IoOp; 24] = [
                    IoOp::Read,
                    IoOp::Write,
                    IoOp::Open,
                    IoOp::Close,
                    IoOp::Sleep,
                    IoOp::Poll,
                    IoOp::Ctl,
                    IoOp::Socket,
                    IoOp::Bind,
                    IoOp::Listen,
                    IoOp::Connect,
                    IoOp::Accept,
                    IoOp::CwdLen,
                    IoOp::CwdCopy,
                    IoOp::GetenvLen,
                    IoOp::GetenvCopy,
                    IoOp::Argc,
                    IoOp::ArgLen,
                    IoOp::ArgCopy,
                    IoOp::DirCount,
                    IoOp::DirEntryKind,
                    IoOp::DirEntryLen,
                    IoOp::DirEntryCopy,
                    IoOp::Exit,
                ];
                let Some(op) = IO_OPS.get(usize::from(*op)).copied() else {
                    return Err(BackendError::new(
                        "backend bug: io operation out of range".into(),
                        Span::SYNTHESIZED,
                    ));
                };
                let a = self.reg(*a);
                let b = self.reg(*b);
                let c = self.reg(*c);
                self.code.push(Insn::Io {
                    dest: *dest,
                    op,
                    a,
                    b,
                    c,
                });
            }
        }
        Ok(())
    }

    fn fresh_reg(&mut self) -> u16 {
        let reg = self.next_reg;
        self.next_reg += 1;
        self.max_reg = self.max_reg.max(self.next_reg);
        reg
    }

    /// Record already-materialized registers in the argument pool.
    fn reg_range(&mut self, regs: &[u16]) -> (u32, u16) {
        let args_start = u32::try_from(self.module.arg_pool.len()).unwrap_or_default();
        let args_len = u16::try_from(regs.len()).unwrap_or_default();
        self.module.arg_pool.extend_from_slice(regs);
        (args_start, args_len)
    }

    /// Record operands in the module's argument pool: registers as
    /// themselves, constants as RK pool references (no materializing
    /// instruction).
    fn arg_range(&mut self, args: &[Operand]) -> (u32, u16) {
        let arg_regs: Vec<u16> = args.iter().map(|arg| self.rk(*arg)).collect();
        let args_start = u32::try_from(self.module.arg_pool.len()).unwrap_or_default();
        let args_len = u16::try_from(arg_regs.len()).unwrap_or_default();
        self.module.arg_pool.extend(arg_regs);
        (args_start, args_len)
    }

    fn patch(&mut self) {
        for patch in &self.patches {
            match patch {
                Patch::Jump { pc, block } => {
                    if let Insn::Jump { target } = &mut self.code[*pc] {
                        *target = self.block_starts[*block];
                    }
                }
                Patch::Branch {
                    pc,
                    then_block,
                    else_block,
                } => {
                    if let Insn::Branch {
                        then_target,
                        else_target,
                        ..
                    } = &mut self.code[*pc]
                    {
                        *then_target = self.block_starts[*then_block];
                        *else_target = self.block_starts[*else_block];
                    }
                }
            }
        }
    }
}
