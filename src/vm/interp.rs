//! The frame-stack register interpreter. Frames are plain data (so M9
//! continuation capture can copy them — Hieb, Dybvig & Bruggeman, PLDI
//! 1990); cells live in a slot arena outside the frames (assignment
//! conversion put them there — Kranz et al., ORBIT, 1986). Dispatch is a
//! plain `match` over the decoded instruction (Ertl & Gregg, JILP 2003).

use crate::lambda_g::expr::{CmpOp, Op};
use crate::name_resolution::symbol::Symbol;
use crate::vm::io::IO;
use crate::vm::{Chunk, Insn, Module};
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
    /// Index into the VM's slot arena (a mutable cell).
    Cell(usize),
}

struct Frame {
    chunk: u32,
    pc: usize,
    regs: Vec<Value>,
    /// Register in the *caller's* frame that receives this frame's Ret.
    dest: u16,
}

/// Far above any reasonable program, far below host memory: frames are
/// heap data, so this only bounds runaway recursion.
const MAX_FRAMES: usize = 1 << 20;

pub fn run(module: &Module, io: &mut dyn IO) -> Result<Value, String> {
    let entry = chunk(module, module.entry)?;
    let mut frames = vec![Frame {
        chunk: module.entry,
        pc: 0,
        regs: vec![Value::Void; entry.n_regs as usize],
        dest: 0,
    }];
    let mut machine = Machine {
        slots: vec![],
        mem: module.statics.clone(),
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
                    dest,
                });
            }
            Insn::Ret { src } => {
                let value = frames[frame_index].regs[src as usize].clone();
                let dest = frames[frame_index].dest;
                frames.pop();
                match frames.last_mut() {
                    Some(caller) => caller.regs[dest as usize] = value,
                    None => return Ok(value),
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

/// Machine state outside the frames: the cell arena, byte memory, and the
/// IO boundary.
struct Machine<'io> {
    slots: Vec<Value>,
    mem: Vec<u8>,
    io: &'io mut dyn IO,
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
        Insn::LoadByte { dest, ptr } => {
            let Value::Ptr(addr) = frame.regs[ptr as usize] else {
                return Err("vm: load of a non-pointer".into());
            };
            let byte = machine
                .mem
                .get(addr as usize)
                .copied()
                .ok_or("vm: load out of bounds")?;
            frame.regs[dest as usize] = Value::Byte(byte);
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
        Insn::IoWrite { dest, fd, ptr, len } => {
            let (Value::I64(fd), Value::Ptr(off), Value::I64(len)) = (
                &frame.regs[fd as usize],
                &frame.regs[ptr as usize],
                &frame.regs[len as usize],
            ) else {
                return Err("vm: io_write operands".into());
            };
            let start = *off as usize;
            let end = start + *len as usize;
            let bytes = machine
                .mem
                .get(start..end)
                .ok_or("vm: io_write out of bounds")?;
            let result = machine.io.write(*fd, bytes);
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
        Insn::Call { .. } | Insn::Ret { .. } | Insn::Trap { .. } => {
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
