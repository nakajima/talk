//! The frame-stack register interpreter. Frames are plain data (so M9
//! continuation capture can copy them — Hieb, Dybvig & Bruggeman, PLDI
//! 1990); cells live in a slot arena outside the frames (assignment
//! conversion put them there — Kranz et al., ORBIT, 1986). Dispatch is a
//! plain `match` over the decoded instruction (Ertl & Gregg, JILP 2003).

use crate::lambda_g::expr::{CmpOp, Op};
use crate::name_resolution::symbol::Symbol;
use crate::vm::io::IO;
use crate::vm::{Chunk, Insn, MemKind, Module};
use std::rc::Rc;

#[derive(Clone, Debug, PartialEq)]
pub enum Value {
    I64(i64),
    F64(f64),
    Bool(bool),
    Byte(u8),
    Void,
    /// An address in the VM's byte memory (statics ++ heap).
    Ptr(u32),
    /// A record value: `Rc` makes copies O(1); field update clones the
    /// fields first (CoW — mutable value semantics, Racordon et al., JOT
    /// 2022).
    Record(Symbol, Rc<Vec<Value>>),
    /// A tuple value (inout ret pairs, M4 payloads).
    Tuple(Rc<Vec<Value>>),
    /// A tagged enum value: enum symbol, variant declaration index, and
    /// payloads (pure, like records).
    Variant(Symbol, u16, Rc<Vec<Value>>),
    /// A flat closure: target chunk plus its captured environment
    /// (Cardelli, LFP 1984).
    Closure(u32, Rc<Vec<Value>>),
    /// Index into the VM's slot arena (a mutable cell).
    Cell(usize),
}

struct Frame {
    chunk: u32,
    pc: usize,
    regs: Vec<Value>,
    /// The closure environment this frame runs under (empty for direct
    /// calls).
    env: Rc<Vec<Value>>,
    /// Register in the *caller's* frame that receives this frame's Ret.
    dest: u16,
}

/// Far above any reasonable program, far below host memory: frames are
/// heap data, so this only bounds runaway recursion.
const MAX_FRAMES: usize = 1 << 20;

pub fn run(module: &Module, io: &mut dyn IO) -> Result<Value, String> {
    Ok(run_machine(module, io)?.0)
}

/// Run and render the program value Talk-style while the machine is
/// still alive (strings point into its byte memory).
pub fn run_displayed(
    module: &Module,
    io: &mut dyn IO,
    names: &ValueNames,
) -> Result<(Value, String), String> {
    let (value, machine) = run_machine(module, io)?;
    let display = render_value(&machine, names, &value);
    Ok((value, display))
}

fn run_machine<'io>(
    module: &Module,
    io: &'io mut dyn IO,
) -> Result<(Value, Machine<'io>), String> {
    let entry = chunk(module, module.entry)?;
    let empty_env: Rc<Vec<Value>> = Rc::new(vec![]);
    let mut frames = vec![Frame {
        chunk: module.entry,
        pc: 0,
        regs: vec![Value::Void; entry.n_regs as usize],
        env: empty_env.clone(),
        dest: 0,
    }];
    let mut machine = Machine {
        slots: vec![],
        mem: module.statics.clone(),
        boxed: vec![],
        io,
    };

    loop {
        let frame_index = frames.len() - 1;
        let current_chunk = frames[frame_index].chunk;
        let pc = frames[frame_index].pc;
        let code = &chunk(module, current_chunk)?.code;
        let Some(&insn) = code.get(pc) else {
            return Err(format!(
                "vm: fell off the end of chunk {}",
                chunk(module, current_chunk)?.name
            ));
        };
        frames[frame_index].pc = pc + 1;

        match insn {
            Insn::Call {
                dest,
                chunk: callee,
                args_start,
                args_len,
            } => {
                if frames.len() >= MAX_FRAMES {
                    return Err("vm: call stack overflow".into());
                }
                let target = chunk(module, callee)?;
                let mut regs = vec![Value::Void; target.n_regs as usize];
                let start = args_start as usize;
                let end = start + args_len as usize;
                let arg_regs = module
                    .arg_pool
                    .get(start..end)
                    .ok_or("vm: bad argument pool range")?;
                let caller = &frames[frame_index];
                for (i, &src) in arg_regs.iter().enumerate() {
                    regs[i] = caller.regs[src as usize].clone();
                }
                frames.push(Frame {
                    chunk: callee,
                    pc: 0,
                    regs,
                    env: empty_env.clone(),
                    dest,
                });
            }
            Insn::CallIndirect {
                dest,
                callee,
                args_start,
                args_len,
            } => {
                if frames.len() >= MAX_FRAMES {
                    return Err("vm: call stack overflow".into());
                }
                let Value::Closure(target, env) = frames[frame_index].regs[callee as usize].clone()
                else {
                    return Err("vm: indirect call of a non-closure".into());
                };
                let target_chunk = chunk(module, target)?;
                let mut regs = vec![Value::Void; target_chunk.n_regs as usize];
                let start = args_start as usize;
                let end = start + args_len as usize;
                let arg_regs = module
                    .arg_pool
                    .get(start..end)
                    .ok_or("vm: bad argument pool range")?;
                let caller = &frames[frame_index];
                for (i, &src) in arg_regs.iter().enumerate() {
                    regs[i] = caller.regs[src as usize].clone();
                }
                frames.push(Frame {
                    chunk: target,
                    pc: 0,
                    regs,
                    env,
                    dest,
                });
            }
            Insn::Ret { src } => {
                let value = frames[frame_index].regs[src as usize].clone();
                let dest = frames[frame_index].dest;
                frames.pop();
                match frames.last_mut() {
                    Some(caller) => caller.regs[dest as usize] = value,
                    None => return Ok((value, machine)),
                }
            }
            Insn::Trap { message } => {
                return Err(module
                    .traps
                    .get(message as usize)
                    .cloned()
                    .unwrap_or_else(|| "vm: trap".into()));
            }
            local => exec_local(module, &mut frames[frame_index], &mut machine, local)?,
        }
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
fn render_value(machine: &Machine, names: &ValueNames, value: &Value) -> String {
    match value {
        Value::I64(v) => v.to_string(),
        Value::F64(v) => {
            let rendered = v.to_string();
            if rendered.contains('.') || rendered.contains('e') || !v.is_finite() {
                rendered
            } else {
                format!("{rendered}.0")
            }
        }
        Value::Bool(v) => v.to_string(),
        Value::Byte(v) => v.to_string(),
        Value::Void => "()".to_string(),
        Value::Ptr(addr) => format!("RawPtr({addr})"),
        Value::Tuple(items) => {
            let items: Vec<String> = items
                .iter()
                .map(|item| render_value(machine, names, item))
                .collect();
            format!("({})", items.join(", "))
        }
        Value::Record(symbol, field_values) => {
            if names.string_struct == Some(*symbol)
                && let [Value::Ptr(base), Value::I64(len), ..] = field_values.as_slice()
            {
                let start = *base as usize;
                let end = start + *len as usize;
                if let Some(bytes) = machine.mem.get(start..end) {
                    return format!("\"{}\"", escape_string(&String::from_utf8_lossy(bytes)));
                }
            }
            let name = names
                .types
                .get(symbol)
                .cloned()
                .unwrap_or_else(|| symbol.to_string());
            let field_names = names.fields.get(symbol);
            let rendered: Vec<String> = field_values
                .iter()
                .enumerate()
                .map(|(index, field)| {
                    let value = render_value(machine, names, field);
                    match field_names.and_then(|fields| fields.get(index)) {
                        Some(field_name) => format!("{field_name}: {value}"),
                        None => value,
                    }
                })
                .collect();
            format!("{name}({})", rendered.join(", "))
        }
        Value::Variant(symbol, tag, payloads) => {
            let name = names
                .types
                .get(symbol)
                .cloned()
                .unwrap_or_else(|| symbol.to_string());
            let case = names
                .cases
                .get(symbol)
                .and_then(|cases| cases.get(*tag as usize))
                .cloned()
                .unwrap_or_else(|| format!("case{tag}"));
            if payloads.is_empty() {
                format!("{name}.{case}")
            } else {
                let payloads: Vec<String> = payloads
                    .iter()
                    .map(|payload| render_value(machine, names, payload))
                    .collect();
                format!("{name}.{case}({})", payloads.join(", "))
            }
        }
        Value::Closure(..) => "<func>".to_string(),
        Value::Cell(_) => "<cell>".to_string(),
    }
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
    /// Aggregates stored in raw memory live here; the memory cell holds an
    /// 8-byte index into this arena (Leroy, POPL 1992's mixed
    /// representation — scalars unboxed, aggregates behind a handle).
    boxed: Vec<Value>,
    io: &'io mut dyn IO,
}

impl Machine<'_> {
    fn read_word(&self, addr: u32) -> Result<u64, String> {
        let start = addr as usize;
        let bytes = self
            .mem
            .get(start..start + 8)
            .ok_or("vm: load out of bounds")?;
        let mut buf = [0u8; 8];
        buf.copy_from_slice(bytes);
        Ok(u64::from_le_bytes(buf))
    }

    fn write_word(&mut self, addr: u32, word: u64) -> Result<(), String> {
        let start = addr as usize;
        let slot = self
            .mem
            .get_mut(start..start + 8)
            .ok_or("vm: store out of bounds")?;
        slot.copy_from_slice(&word.to_le_bytes());
        Ok(())
    }
}

/// One io operation: extract the register operands, marshal pointer
/// operands against byte memory (read fills it, open scans a
/// NUL-terminated path, poll round-trips 8-byte pollfd records), and
/// call through the IO boundary. POSIX return conventions throughout.
fn run_io(
    machine: &mut Machine,
    frame: &Frame,
    op: crate::vm::IoOp,
    a: u16,
    b: u16,
    c: u16,
) -> Result<i64, String> {
    use crate::vm::IoOp;
    let int = |reg: u16| -> Result<i64, String> {
        match frame.regs[reg as usize] {
            Value::I64(v) => Ok(v),
            ref other => Err(format!("vm: io integer operand, got {other:?}")),
        }
    };
    let ptr = |reg: u16| -> Result<usize, String> {
        match frame.regs[reg as usize] {
            Value::Ptr(off) => Ok(off as usize),
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
            let (start, len) = (ptr(b)?, count as usize);
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
            let (start, len) = (ptr(b)?, count as usize);
            let buf = machine
                .mem
                .get_mut(start..start + len)
                .ok_or("vm: io read out of bounds")?;
            machine.io.read(fd, buf)
        }
        IoOp::Open => {
            let start = ptr(a)?;
            let tail = machine.mem.get(start..).ok_or("vm: io open out of bounds")?;
            let len = tail.iter().position(|&byte| byte == 0).unwrap_or(tail.len());
            let path = tail[..len].to_vec();
            machine.io.open(&path, int(b)?, int(c)?)
        }
        IoOp::Close => machine.io.close(int(a)?),
        IoOp::Sleep => machine.io.sleep(int(a)?),
        IoOp::Ctl => machine.io.ctl(int(a)?, int(b)?, int(c)?),
        IoOp::Poll => {
            let (start, count, timeout) = (ptr(a)?, int(b)? as usize, int(c)?);
            let records = machine
                .mem
                .get(start..start + count * 8)
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
                let at = start + index * 8 + 6;
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
    })
}

/// Instructions that touch only the current frame (and the machine state).
fn exec_local(
    module: &Module,
    frame: &mut Frame,
    machine: &mut Machine,
    insn: Insn,
) -> Result<(), String> {
    match insn {
        Insn::Const { dest, k } => {
            let value = module
                .consts
                .get(k as usize)
                .cloned()
                .ok_or_else(|| format!("vm: bad constant index {k}"))?;
            frame.regs[dest as usize] = value;
        }
        Insn::Move { dest, src } => frame.regs[dest as usize] = frame.regs[src as usize].clone(),
        Insn::Add { dest, a, b } => {
            frame.regs[dest as usize] = arith(
                Op::Add,
                &frame.regs[a as usize],
                &frame.regs[b as usize],
                i64::wrapping_add,
                |x, y| x + y,
            )?
        }
        Insn::Sub { dest, a, b } => {
            frame.regs[dest as usize] = arith(
                Op::Sub,
                &frame.regs[a as usize],
                &frame.regs[b as usize],
                i64::wrapping_sub,
                |x, y| x - y,
            )?
        }
        Insn::Mul { dest, a, b } => {
            frame.regs[dest as usize] = arith(
                Op::Mul,
                &frame.regs[a as usize],
                &frame.regs[b as usize],
                i64::wrapping_mul,
                |x, y| x * y,
            )?
        }
        Insn::Div { dest, a, b } => {
            let (a, b) = (&frame.regs[a as usize], &frame.regs[b as usize]);
            frame.regs[dest as usize] = match (a, b) {
                (Value::I64(_), Value::I64(0)) => return Err("vm: division by zero".into()),
                (Value::I64(x), Value::I64(y)) => Value::I64(x.wrapping_div(*y)),
                (Value::F64(x), Value::F64(y)) => Value::F64(x / y),
                _ => return Err(format!("vm: div on {a:?} and {b:?}")),
            };
        }
        Insn::Cmp { dest, a, b, op } => {
            let result = compare(&frame.regs[a as usize], &frame.regs[b as usize], op)?;
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
        Insn::RecordNew {
            dest,
            symbol,
            args_start,
            args_len,
        } => {
            let start = args_start as usize;
            let end = start + args_len as usize;
            let arg_regs = module
                .arg_pool
                .get(start..end)
                .ok_or("vm: bad argument pool range")?;
            let fields: Vec<Value> = arg_regs
                .iter()
                .map(|&src| frame.regs[src as usize].clone())
                .collect();
            frame.regs[dest as usize] = Value::Record(symbol, Rc::new(fields));
        }
        Insn::GetField { dest, rec, index } => {
            let Value::Record(_, fields) = &frame.regs[rec as usize] else {
                return Err("vm: get_field on a non-record".into());
            };
            let value = fields
                .get(index as usize)
                .cloned()
                .ok_or("vm: field index out of range")?;
            frame.regs[dest as usize] = value;
        }
        Insn::VariantNew {
            dest,
            symbol,
            tag,
            args_start,
            args_len,
        } => {
            let start = args_start as usize;
            let end = start + args_len as usize;
            let arg_regs = module
                .arg_pool
                .get(start..end)
                .ok_or("vm: bad argument pool range")?;
            let payloads: Vec<Value> = arg_regs
                .iter()
                .map(|&src| frame.regs[src as usize].clone())
                .collect();
            frame.regs[dest as usize] = Value::Variant(symbol, tag, Rc::new(payloads));
        }
        Insn::GetTag { dest, src } => {
            let Value::Variant(_, tag, _) = &frame.regs[src as usize] else {
                return Err("vm: get_tag on a non-variant".into());
            };
            frame.regs[dest as usize] = Value::I64(*tag as i64);
        }
        Insn::GetPayload { dest, src, index } => {
            let Value::Variant(_, _, payloads) = &frame.regs[src as usize] else {
                return Err("vm: get_payload on a non-variant".into());
            };
            let value = payloads
                .get(index as usize)
                .cloned()
                .ok_or("vm: payload index out of range")?;
            frame.regs[dest as usize] = value;
        }
        Insn::MakeClosure {
            dest,
            chunk,
            args_start,
            args_len,
        } => {
            let start = args_start as usize;
            let end = start + args_len as usize;
            let arg_regs = module
                .arg_pool
                .get(start..end)
                .ok_or("vm: bad argument pool range")?;
            let env: Vec<Value> = arg_regs
                .iter()
                .map(|&src| frame.regs[src as usize].clone())
                .collect();
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
        Insn::TupleNew {
            dest,
            args_start,
            args_len,
        } => {
            let start = args_start as usize;
            let end = start + args_len as usize;
            let arg_regs = module
                .arg_pool
                .get(start..end)
                .ok_or("vm: bad argument pool range")?;
            let items: Vec<Value> = arg_regs
                .iter()
                .map(|&src| frame.regs[src as usize].clone())
                .collect();
            frame.regs[dest as usize] = Value::Tuple(Rc::new(items));
        }
        Insn::Extract { dest, src, index } => {
            let Value::Tuple(items) = &frame.regs[src as usize] else {
                return Err("vm: extract from a non-tuple".into());
            };
            let value = items
                .get(index as usize)
                .cloned()
                .ok_or("vm: tuple index out of range")?;
            frame.regs[dest as usize] = value;
        }
        Insn::SetField {
            dest,
            rec,
            src,
            index,
        } => {
            let value = frame.regs[src as usize].clone();
            let Value::Record(symbol, fields) = &frame.regs[rec as usize] else {
                return Err("vm: set_field on a non-record".into());
            };
            // CoW: clone the Rc, mutate the (now possibly unshared) copy.
            let (symbol, mut fields) = (*symbol, fields.clone());
            {
                let fields = Rc::make_mut(&mut fields);
                let slot = fields
                    .get_mut(index as usize)
                    .ok_or("vm: field index out of range")?;
                *slot = value;
            }
            frame.regs[dest as usize] = Value::Record(symbol, fields);
        }
        Insn::Alloc { dest, count } => {
            let Value::I64(count) = frame.regs[count as usize] else {
                return Err("vm: alloc of a non-int count".into());
            };
            if count < 0 {
                return Err("vm: alloc of a negative count".into());
            }
            let addr = machine.mem.len() as u32;
            machine.mem.resize(machine.mem.len() + count as usize, 0);
            frame.regs[dest as usize] = Value::Ptr(addr);
        }
        Insn::Load { dest, ptr, kind } => {
            let Value::Ptr(addr) = frame.regs[ptr as usize] else {
                return Err("vm: load of a non-pointer".into());
            };
            frame.regs[dest as usize] = match kind {
                MemKind::Byte => Value::Byte(
                    machine
                        .mem
                        .get(addr as usize)
                        .copied()
                        .ok_or("vm: load out of bounds")?,
                ),
                MemKind::I64 => Value::I64(machine.read_word(addr)? as i64),
                MemKind::F64 => Value::F64(f64::from_bits(machine.read_word(addr)?)),
                MemKind::Bool => Value::Bool(machine.read_word(addr)? != 0),
                MemKind::Ptr => Value::Ptr(machine.read_word(addr)? as u32),
                MemKind::Boxed => {
                    let handle = machine.read_word(addr)? as usize;
                    machine
                        .boxed
                        .get(handle)
                        .cloned()
                        .ok_or("vm: load of a bad arena handle")?
                }
            };
        }
        Insn::Store { ptr, src, kind } => {
            let Value::Ptr(addr) = frame.regs[ptr as usize] else {
                return Err("vm: store to a non-pointer".into());
            };
            let value = frame.regs[src as usize].clone();
            match (kind, value) {
                (MemKind::Byte, Value::Byte(byte)) => {
                    let slot = machine
                        .mem
                        .get_mut(addr as usize)
                        .ok_or("vm: store out of bounds")?;
                    *slot = byte;
                }
                (MemKind::I64, Value::I64(v)) => machine.write_word(addr, v as u64)?,
                (MemKind::F64, Value::F64(v)) => machine.write_word(addr, v.to_bits())?,
                (MemKind::Bool, Value::Bool(v)) => machine.write_word(addr, v as u64)?,
                (MemKind::Ptr, Value::Ptr(v)) => machine.write_word(addr, v as u64)?,
                (MemKind::Boxed, value) => {
                    machine.boxed.push(value);
                    machine.write_word(addr, (machine.boxed.len() - 1) as u64)?;
                }
                (kind, value) => {
                    return Err(format!("vm: store kind {kind:?} got {value:?}"));
                }
            }
        }
        Insn::Copy { from, to, len } => {
            let (Value::Ptr(from), Value::Ptr(to), Value::I64(len)) = (
                &frame.regs[from as usize],
                &frame.regs[to as usize],
                &frame.regs[len as usize],
            ) else {
                return Err("vm: copy operands".into());
            };
            let (from, to, len) = (*from as usize, *to as usize, *len as usize);
            if from + len > machine.mem.len() || to + len > machine.mem.len() {
                return Err("vm: copy out of bounds".into());
            }
            machine.mem.copy_within(from..from + len, to);
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
        Insn::Call { .. } | Insn::CallIndirect { .. } | Insn::Ret { .. } | Insn::Trap { .. } => {
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

fn arith(
    op: Op,
    a: &Value,
    b: &Value,
    ints: fn(i64, i64) -> i64,
    floats: fn(f64, f64) -> f64,
) -> Result<Value, String> {
    match (a, b) {
        (Value::I64(x), Value::I64(y)) => Ok(Value::I64(ints(*x, *y))),
        (Value::F64(x), Value::F64(y)) => Ok(Value::F64(floats(*x, *y))),
        // Pointer arithmetic (`add RawPtr p offset`).
        (Value::Ptr(p), Value::I64(off)) if op == Op::Add => {
            Ok(Value::Ptr((*p as i64 + off) as u32))
        }
        (Value::Ptr(p), Value::I64(off)) if op == Op::Sub => {
            Ok(Value::Ptr((*p as i64 - off) as u32))
        }
        _ => Err(format!("vm: arithmetic on {a:?} and {b:?}")),
    }
}

fn compare(a: &Value, b: &Value, op: CmpOp) -> Result<bool, String> {
    use CmpOp::*;
    match (a, b) {
        (Value::I64(x), Value::I64(y)) => Ok(match op {
            Eq => x == y,
            Ne => x != y,
            Lt => x < y,
            Le => x <= y,
            Gt => x > y,
            Ge => x >= y,
        }),
        (Value::F64(x), Value::F64(y)) => Ok(match op {
            Eq => x == y,
            Ne => x != y,
            Lt => x < y,
            Le => x <= y,
            Gt => x > y,
            Ge => x >= y,
        }),
        (Value::Byte(x), Value::Byte(y)) => Ok(match op {
            Eq => x == y,
            Ne => x != y,
            Lt => x < y,
            Le => x <= y,
            Gt => x > y,
            Ge => x >= y,
        }),
        (Value::Bool(x), Value::Bool(y)) => match op {
            Eq => Ok(x == y),
            Ne => Ok(x != y),
            _ => Err("vm: ordering comparison on bools".into()),
        },
        _ => Err(format!("vm: comparison on {a:?} and {b:?}")),
    }
}
