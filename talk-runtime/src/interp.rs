//! The frame-stack register interpreter. Frames are plain data (so M9
//! continuation capture can copy them — Hieb, Dybvig & Bruggeman, PLDI
//! 1990); cells live in a slot arena outside the frames (assignment
//! conversion put them there — Kranz et al., ORBIT, 1986). Dispatch is a
//! plain `match` over the decoded instruction (Ertl & Gregg, JILP 2003).

use crate::CmpOp;
use crate::io::IO;
use crate::memory::{Allocations, MemoryError};
use crate::objects::{ObjectError, Objects};
use crate::symbol::Symbol;
use crate::{Chunk, Insn, MemKind, Module};
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
    /// A protocol existential: hidden payload plus erased witness closures.
    Existential(Symbol, Rc<Value>, Rc<Vec<Value>>),
    /// A flat closure: target chunk plus its captured environment
    /// (Cardelli, LFP 1984).
    Closure(u32, Rc<Vec<Value>>),
    /// Index into the VM's slot arena (a mutable cell).
    Cell(usize),
    /// A `'heap` object handle: index into the machine's object arena.
    /// Copies alias; the region, not the handle, owns the storage.
    Object(u32),
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

/// Frame.dest sentinel for finalizer frames: their Ret writes nowhere.
const FINALIZER_DEST: u16 = u16::MAX;

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
    let display = render_value(&machine, names, &value)?;
    Ok((value, display))
}

fn run_machine<'io>(module: &Module, io: &'io mut dyn IO) -> Result<(Value, Machine<'io>), String> {
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
        static_len: module.statics.len() as u32,
        allocations: Allocations::default(),
        boxed: vec![],
        objects: Objects::default(),
        io,
    };

    // Finalizer frames currently on the stack: the teardown walk must not
    // advance (and above all must not bulk-free) while one is running.
    let mut finalizer_frames: usize = 0;
    loop {
        // Region-teardown pump: while a region is finalizing, run its
        // members' finalizer thunks (reverse allocation order) as ordinary
        // frames before executing anything else; the walk's bulk free
        // happens inside `next_finalizer` when members are exhausted.
        if finalizer_frames == 0
            && let Some((thunk, object)) = machine.objects.next_finalizer()
        {
            if frames.len() >= MAX_FRAMES {
                return Err("vm: call stack overflow".into());
            }
            let Value::Closure(fin_chunk, env) = thunk else {
                return Err("vm: finalizer is not a function value".into());
            };
            let target = chunk(module, fin_chunk)?;
            check_call_shape(target, 1)?;
            let mut regs = vec![Value::Void; target.n_regs as usize];
            regs[0] = Value::Object(object);
            frames.push(Frame {
                chunk: fin_chunk,
                pc: 0,
                regs,
                env,
                dest: FINALIZER_DEST,
            });
            finalizer_frames += 1;
            continue;
        }
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
                check_call_shape(target, args_len)?;
                let args = arg_values(module, &frames[frame_index], args_start, args_len)?;
                let mut regs = vec![Value::Void; target.n_regs as usize];
                for (i, value) in args.into_iter().enumerate() {
                    let Some(slot) = regs.get_mut(i) else {
                        return Err("vm: call argument count exceeds callee frame".into());
                    };
                    *slot = value;
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
                let Some(callee_value) = frames[frame_index].regs.get(callee as usize).cloned()
                else {
                    return Err("vm: callee register out of range".into());
                };
                let Value::Closure(target, env) = callee_value else {
                    return Err("vm: indirect call of a non-closure".into());
                };
                let target_chunk = chunk(module, target)?;
                check_call_shape(target_chunk, args_len)?;
                let args = arg_values(module, &frames[frame_index], args_start, args_len)?;
                let mut regs = vec![Value::Void; target_chunk.n_regs as usize];
                for (i, value) in args.into_iter().enumerate() {
                    let Some(slot) = regs.get_mut(i) else {
                        return Err("vm: call argument count exceeds callee frame".into());
                    };
                    *slot = value;
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
                    // A finalizer frame (pushed by the teardown pump) has no
                    // destination: its value is discarded, and the paused
                    // teardown walk may resume.
                    Some(_) if dest == FINALIZER_DEST => {
                        finalizer_frames = finalizer_frames.saturating_sub(1);
                    }
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
        Value::Ptr(addr) => Ok(format!("RawPtr({addr})")),
        Value::Tuple(items) => {
            let items: Vec<String> = items
                .iter()
                .map(|item| render_value(machine, names, item))
                .collect::<Result<_, _>>()?;
            Ok(format!("({})", items.join(", ")))
        }
        Value::Record(symbol, field_values) => {
            if names.string_struct == Some(*symbol)
                && let Some((base, len)) = string_bytes(field_values)
            {
                let bytes = machine.string_display_bytes(base, len)?;
                return Ok(format!(
                    "\"{}\"",
                    escape_string(&String::from_utf8_lossy(bytes))
                ));
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
                    let value = render_value(machine, names, field)?;
                    Ok(match field_names.and_then(|fields| fields.get(index)) {
                        Some(field_name) => format!("{field_name}: {value}"),
                        None => value,
                    })
                })
                .collect::<Result<_, String>>()?;
            Ok(format!("{name}({})", rendered.join(", ")))
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
                Ok(format!("{name}.{case}"))
            } else {
                let payloads: Vec<String> = payloads
                    .iter()
                    .map(|payload| render_value(machine, names, payload))
                    .collect::<Result<_, _>>()?;
                Ok(format!("{name}.{case}({})", payloads.join(", ")))
            }
        }
        Value::Existential(_, payload, _) => render_value(machine, names, payload),
        Value::Closure(..) => Ok("<func>".to_string()),
        Value::Cell(_) => Ok("<cell>".to_string()),
        // Shallow: structural rendering would cycle through the graph.
        Value::Object(object) => Ok(format!("<object #{object}>")),
    }
}

fn string_bytes(field_values: &[Value]) -> Option<(u32, i64)> {
    match field_values {
        [Value::Ptr(base), Value::I64(len), ..] => Some((*base, *len)),
        [storage, Value::I64(len), ..] => storage_base(storage).map(|base| (base, *len)),
        _ => None,
    }
}

fn storage_base(value: &Value) -> Option<u32> {
    match value {
        Value::Ptr(base) => Some(*base),
        Value::Record(_, fields) => match fields.as_slice() {
            [Value::Ptr(base), ..] => Some(*base),
            _ => None,
        },
        _ => None,
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
    static_len: u32,
    allocations: Allocations,
    /// Aggregates stored in raw memory live here; the memory cell holds an
    /// 8-byte index into this arena (Leroy, POPL 1992's mixed
    /// representation — scalars unboxed, aggregates behind a handle).
    boxed: Vec<Value>,
    /// Region-allocated `'heap` objects (see `objects.rs`).
    objects: Objects<Value>,
    io: &'io mut dyn IO,
}

impl Machine<'_> {
    fn read_word(&self, addr: u32) -> Result<u64, String> {
        self.check_access(addr, 8, "load")?;
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
        self.check_access(addr, 8, "store")?;
        let start = addr as usize;
        let slot = self
            .mem
            .get_mut(start..start + 8)
            .ok_or("vm: store out of bounds")?;
        slot.copy_from_slice(&word.to_le_bytes());
        Ok(())
    }

    fn free(&mut self, ptr: u32) -> Result<(), String> {
        self.allocations
            .free(self.static_len, ptr)
            .map_err(vm_memory_error)
    }

    fn check_access(&self, addr: u32, len: usize, op: &str) -> Result<(), String> {
        self.allocations
            .check_access(self.mem.len(), self.static_len, addr, len, op)
            .map_err(vm_memory_error)
    }

    fn c_string_tail(&self, addr: u32) -> Result<&[u8], String> {
        let start = addr as usize;
        let end = self
            .allocations
            .accessible_tail_end(self.mem.len(), self.static_len, addr, "io")
            .map_err(vm_io_memory_error)?;
        self.mem
            .get(start..end)
            .ok_or_else(|| "vm: io open out of bounds".to_string())
    }

    fn string_display_bytes(&self, addr: u32, len: i64) -> Result<&[u8], String> {
        let len = usize::try_from(len)
            .map_err(|_| "vm: display string has invalid length".to_string())?;
        self.check_access(addr, len, "display")?;
        let start = addr as usize;
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
    frame: &Frame,
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
            machine.check_access(start as u32, len, "io")?;
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
            machine.check_access(start as u32, len, "io")?;
            let buf = machine
                .mem
                .get_mut(start..start + len)
                .ok_or("vm: io read out of bounds")?;
            machine.io.read(fd, buf)
        }
        IoOp::Open => {
            let start = ptr(a)?;
            let tail = machine.c_string_tail(start as u32)?;
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
            let (start, count, timeout) = (ptr(a)?, int(b)?, int(c)?);
            if count < 0 {
                return Err("vm: io poll negative count".into());
            }
            let count = usize::try_from(count).map_err(|_| "vm: io poll count out of range")?;
            let len = count
                .checked_mul(8)
                .ok_or("vm: io poll count out of range")?;
            machine.check_access(start as u32, len, "io")?;
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
                let at = start + index * 8 + 6;
                machine.check_access(at as u32, 2, "io")?;
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
            let start = ptr(a)?;
            machine.check_access(start as u32, len as usize, "io")?;
            let buf = machine
                .mem
                .get_mut(start..start + len as usize)
                .ok_or("vm: io cwd out of bounds")?;
            machine.io.cwd_copy(buf)
        }
        IoOp::GetenvLen => {
            let (start, len) = (ptr(a)?, int(b)?);
            if len < 0 {
                return Ok(len);
            }
            machine.check_access(start as u32, len as usize, "io")?;
            let name = machine
                .mem
                .get(start..start + len as usize)
                .ok_or("vm: io getenv name out of bounds")?;
            machine.io.getenv_len(name)
        }
        IoOp::GetenvCopy => {
            let (name_start, name_len, dest) = (ptr(a)?, int(b)?, ptr(c)?);
            if name_len < 0 {
                return Ok(name_len);
            }
            machine.check_access(name_start as u32, name_len as usize, "io")?;
            let name = machine
                .mem
                .get(name_start..name_start + name_len as usize)
                .ok_or("vm: io getenv name out of bounds")?
                .to_vec();
            let len = machine.io.getenv_len(&name);
            if len < 0 {
                return Ok(len);
            }
            machine.check_access(dest as u32, len as usize, "io")?;
            let buf = machine
                .mem
                .get_mut(dest..dest + len as usize)
                .ok_or("vm: io getenv out of bounds")?;
            machine.io.getenv_copy(&name, buf)
        }
        IoOp::Argc => machine.io.argc(),
        IoOp::ArgLen => machine.io.arg_len(int(a)?),
        IoOp::ArgCopy => {
            let (index, dest) = (int(a)?, ptr(b)?);
            let len = machine.io.arg_len(index);
            if len < 0 {
                return Ok(len);
            }
            machine.check_access(dest as u32, len as usize, "io")?;
            let buf = machine
                .mem
                .get_mut(dest..dest + len as usize)
                .ok_or("vm: io arg out of bounds")?;
            machine.io.arg_copy(index, buf)
        }
        IoOp::DirCount => {
            let start = ptr(a)?;
            let tail = machine.c_string_tail(start as u32)?;
            let len = tail
                .iter()
                .position(|&byte| byte == 0)
                .unwrap_or(tail.len());
            let path = tail[..len].to_vec();
            machine.io.dir_count(&path)
        }
        IoOp::DirEntryKind => {
            let start = ptr(a)?;
            let tail = machine.c_string_tail(start as u32)?;
            let len = tail
                .iter()
                .position(|&byte| byte == 0)
                .unwrap_or(tail.len());
            let path = tail[..len].to_vec();
            machine.io.dir_entry_kind(&path, int(b)?)
        }
        IoOp::DirEntryLen => {
            let start = ptr(a)?;
            let tail = machine.c_string_tail(start as u32)?;
            let len = tail
                .iter()
                .position(|&byte| byte == 0)
                .unwrap_or(tail.len());
            let path = tail[..len].to_vec();
            machine.io.dir_entry_len(&path, int(b)?)
        }
        IoOp::DirEntryCopy => {
            let start = ptr(a)?;
            let tail = machine.c_string_tail(start as u32)?;
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
            let dest = ptr(c)?;
            machine.check_access(dest as u32, entry_len as usize, "io")?;
            let buf = machine
                .mem
                .get_mut(dest..dest + entry_len as usize)
                .ok_or("vm: io dir entry out of bounds")?;
            machine.io.dir_entry_copy(&path, index, buf)
        }
        IoOp::Exit => machine.io.exit(int(a)?),
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
                ArithOp::Add,
                &frame.regs[a as usize],
                &frame.regs[b as usize],
                i64::wrapping_add,
                |x, y| x + y,
            )?
        }
        Insn::Sub { dest, a, b } => {
            frame.regs[dest as usize] = arith(
                ArithOp::Sub,
                &frame.regs[a as usize],
                &frame.regs[b as usize],
                i64::wrapping_sub,
                |x, y| x - y,
            )?
        }
        Insn::Mul { dest, a, b } => {
            frame.regs[dest as usize] = arith(
                ArithOp::Mul,
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
            let fields = arg_values(module, frame, args_start, args_len)?;
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
            let payloads = arg_values(module, frame, args_start, args_len)?;
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
        Insn::ExistentialPack {
            dest,
            protocol,
            args_start,
            args_len,
        } => {
            let mut values = arg_values(module, frame, args_start, args_len)?;
            if values.is_empty() {
                return Err("vm: existential_pack without a payload".into());
            }
            let payload = values.remove(0);
            frame.regs[dest as usize] =
                Value::Existential(protocol, Rc::new(payload), Rc::new(values));
        }
        Insn::ExistentialWitness { dest, src, index } => {
            let Value::Existential(_, _, witnesses) = &frame.regs[src as usize] else {
                return Err("vm: existential_witness on a non-existential".into());
            };
            let witness = witnesses
                .get(index as usize)
                .cloned()
                .ok_or("vm: existential witness index out of range")?;
            frame.regs[dest as usize] = witness;
        }
        Insn::ExistentialPayload { dest, src } => {
            let Value::Existential(_, payload, _) = &frame.regs[src as usize] else {
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
        Insn::TupleNew {
            dest,
            args_start,
            args_len,
        } => {
            let items = arg_values(module, frame, args_start, args_len)?;
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
            let count = usize::try_from(count).map_err(|_| "vm: alloc count out of range")?;
            let addr = machine
                .allocations
                .allocate(&mut machine.mem, count)
                .map_err(vm_memory_error)?;
            frame.regs[dest as usize] = Value::Ptr(addr);
        }
        Insn::Free { dest, ptr } => {
            let Value::Ptr(ptr) = frame.regs[ptr as usize] else {
                return Err("vm: free of a non-pointer".into());
            };
            machine.free(ptr)?;
            frame.regs[dest as usize] = Value::Void;
        }
        Insn::Retain { dest, ptr } => {
            let Value::Ptr(ptr) = frame.regs[ptr as usize] else {
                return Err("vm: retain of a non-pointer".into());
            };
            machine
                .allocations
                .retain(machine.static_len, ptr)
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
            let object = machine.objects.allocate(fields);
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
            frame.regs[dest as usize] = match kind {
                MemKind::Byte => Value::Byte({
                    machine.check_access(addr, 1, "load")?;
                    machine
                        .mem
                        .get(addr as usize)
                        .copied()
                        .ok_or("vm: load out of bounds")?
                }),
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
                    machine.check_access(addr, 1, "store")?;
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
            if *len < 0 {
                return Err("vm: copy negative length".into());
            }
            machine.check_access(*from, *len as usize, "copy")?;
            machine.check_access(*to, *len as usize, "copy")?;
            let (from, to, len) = (*from as usize, *to as usize, *len as usize);
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
        Value::Record(_, fields) | Value::Tuple(fields) | Value::Variant(_, _, fields) => {
            for field in fields.iter() {
                scan_handles(field, out);
            }
        }
        Value::Existential(_, payload, witnesses) => {
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
        | Value::Cell(_) => {}
    }
}

fn vm_object_error(error: ObjectError) -> String {
    format!("vm: {}", error.message())
}

fn arg_values(
    module: &Module,
    frame: &Frame,
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
    arg_regs
        .iter()
        .map(|&src| {
            frame
                .regs
                .get(src as usize)
                .cloned()
                .ok_or_else(|| format!("vm: argument register r{src} out of range"))
        })
        .collect()
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum ArithOp {
    Add,
    Sub,
    Mul,
}

fn arith(
    op: ArithOp,
    a: &Value,
    b: &Value,
    ints: fn(i64, i64) -> i64,
    floats: fn(f64, f64) -> f64,
) -> Result<Value, String> {
    match (a, b) {
        (Value::I64(x), Value::I64(y)) => Ok(Value::I64(ints(*x, *y))),
        (Value::F64(x), Value::F64(y)) => Ok(Value::F64(floats(*x, *y))),
        // Pointer arithmetic (`add RawPtr p offset`).
        (Value::Ptr(p), Value::I64(off)) if op == ArithOp::Add => {
            Ok(Value::Ptr((*p as i64 + off) as u32))
        }
        (Value::Ptr(p), Value::I64(off)) if op == ArithOp::Sub => {
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::io::CaptureIO;
    use crate::{Chunk, Module};

    fn run_with_machine(module: &Module) -> (Value, usize, usize) {
        let mut io = CaptureIO::default();
        let (value, machine) = run_machine(module, &mut io).expect("vm run");
        (value, machine.objects.live_objects(), io.out.len())
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
                },
            ],
            consts: vec![
                Value::I64(10),
                Value::I64(42),
                Value::I64(1),
                Value::Ptr(0),
            ],
            arg_pool: vec![0],
            switch_pool: vec![],
            traps: vec![],
            statics: vec![b'x'],
            entry: 0,
        }
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
            }],
            consts: vec![Value::I64(0), Value::I64(42)],
            arg_pool: vec![0],
            switch_pool: vec![],
            traps: vec![],
            statics: vec![],
            entry: 0,
        };
        let (value, _, _) = run_with_machine(&module);
        assert_eq!(value, Value::I64(42), "mutation through one alias visible through the other");
    }
}
