//! The reference evaluator: a definitional interpreter (Reynolds 1972) for
//! the paper's strict, left-to-right small-step semantics (Leißa & Griebler
//! §3.4, rules V-Fun/V-Const/E-App1/E-App2/E-β), implemented big-step over
//! the same Program so E-β is literally `beta_reduce`. It is the executable
//! spec the bytecode VM is differentially tested against. Machine state
//! (cells, byte memory, io) lives in the Evaluator; the term language sees
//! only constants (`Slot`, `StaticPtr`) — values stay a sub-grammar of
//! expressions, as the paper's semantics requires.
//!
//! Records are pure values: `RecordNew`/`GetField`/`SetField` are
//! functional (mutable value semantics — Racordon et al., JOT 2022 —
//! reaches the machine only through cells), so a record value reifies as a
//! `RecordNew` of reified fields.

use crate::lambda_g::expr::{CmpOp, Const, ExprId, ExprKind, Op, TyKind};
use crate::lambda_g::program::{Label, Program};
use crate::name_resolution::symbol::Symbol;
use crate::vm::io::IO;

#[derive(Debug, Clone, PartialEq)]
pub enum EvalValue {
    I64(i64),
    F64(f64),
    Bool(bool),
    Byte(u8),
    Void,
    /// An address in program memory (statics ++ heap).
    Ptr(u32),
    Tuple(Vec<EvalValue>),
    Func(Label),
    Record(Symbol, Vec<EvalValue>),
    /// A tagged enum value: the enum symbol, the variant's declaration
    /// index, and its payloads (pure, like records).
    Variant(Symbol, u16, Vec<EvalValue>),
    /// Index into the evaluator's slot store (a mutable cell).
    Cell(usize),
}

enum Step {
    Done(EvalValue),
    Continue(ExprId),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum EvalError {
    UnboundVariable(String),
    NotAFunction,
    UnsetBody(String),
    DivisionByZero,
    Unsupported(String),
    StepLimit,
}

pub struct Evaluator {
    /// The reference evaluator always runs against the captured IO —
    /// the same simulated-descriptor semantics the VM's two-engine
    /// tests use, so the engines agree on io by construction.
    pub io: crate::vm::io::CaptureIO,
    steps: u64,
    limit: u64,
    /// Program memory: statics at the base, bump-allocated heap above
    /// (Leroy, POPL 1992 — scalars live unboxed in raw bytes; no free
    /// here, allocation is append).
    mem: Vec<u8>,
    /// Mutable cell store (assignment-converted locals). Cells are machine
    /// state; the term language sees only `Const::Slot` handles.
    slots: Vec<EvalValue>,
    slot_tys: Vec<crate::lambda_g::expr::TyId>,
    /// Aggregates stored in raw memory live here; the memory cell holds an
    /// 8-byte index into this arena (records stay boxed values — Leroy,
    /// POPL 1992's mixed representation).
    boxed: Vec<EvalValue>,
    /// The machine's initial continuation: applying it ends evaluation with
    /// its argument as the program value (the standard top-level
    /// continuation of a CPS machine).
    halt: Option<Label>,
}

impl Default for Evaluator {
    fn default() -> Self {
        Self::new()
    }
}

impl Evaluator {
    pub fn new() -> Self {
        Evaluator {
            io: crate::vm::io::CaptureIO::default(),
            steps: 0,
            limit: 50_000_000,
            mem: vec![],
            slots: vec![],
            slot_tys: vec![],
            boxed: vec![],
            halt: None,
        }
    }

    /// Run a CPS `main : [Fn(R, ⊥)] → ⊥`: apply it to the halt continuation
    /// and evaluate; the value passed to halt is the program's value.
    pub fn run_main(
        &mut self,
        p: &mut Program,
        main: Label,
        result_ty: crate::lambda_g::expr::TyId,
    ) -> Result<EvalValue, EvalError> {
        let bot = p.ty_bot();
        let halt_ty_dom = result_ty;
        let halt = p.func("halt", halt_ty_dom, bot);
        let _ = bot;
        self.mem = p.static_mem.clone();
        self.halt = Some(halt);
        let halt_ref = p.func_ref(halt);
        let main_ref = p.func_ref(main);
        let args = p.tuple(&[halt_ref]);
        let call = p.app(main_ref, args);
        self.eval(p, call)
    }

    /// Evaluate with a tail-stepping trampoline: a CPS program's spine is
    /// one long chain of ⊥-typed applications, so tail applications update
    /// the current redex iteratively instead of recursing (host stack depth
    /// stays bounded by *expression* nesting, not execution length).
    pub fn eval(&mut self, p: &mut Program, e: ExprId) -> Result<EvalValue, EvalError> {
        let mut current = e;
        loop {
            self.steps += 1;
            if self.steps > self.limit {
                return Err(EvalError::StepLimit);
            }
            match p.expr(current).kind.clone() {
                ExprKind::App(f, a) => {
                    let vf = self.eval_sub(p, f)?;
                    let va = self.eval_sub(p, a)?;
                    match self.step(p, vf, va)? {
                        Step::Done(value) => return Ok(value),
                        Step::Continue(next) => current = next,
                    }
                }
                ExprKind::PrimOp(Op::Br, args, _) => {
                    let cond = self.eval_sub(p, args[0])?;
                    let chosen = if cond == EvalValue::Bool(true) {
                        args[1]
                    } else {
                        args[2]
                    };
                    let thunk = self.eval_sub(p, chosen)?;
                    let unit = self.unit_for(p, chosen);
                    match self.step(p, thunk, unit)? {
                        Step::Done(value) => return Ok(value),
                        Step::Continue(next) => current = next,
                    }
                }
                ExprKind::PrimOp(Op::Switch, args, _) => {
                    let EvalValue::I64(tag) = self.eval_sub(p, args[0])? else {
                        return Err(EvalError::Unsupported("switch on non-int".into()));
                    };
                    let arms = &args[1..args.len() - 1];
                    let chosen = arms
                        .get(tag as usize)
                        .copied()
                        .unwrap_or(args[args.len() - 1]);
                    let thunk = self.eval_sub(p, chosen)?;
                    let unit = self.unit_for(p, chosen);
                    match self.step(p, thunk, unit)? {
                        Step::Done(value) => return Ok(value),
                        Step::Continue(next) => current = next,
                    }
                }
                _ => return self.eval_sub(p, current),
            }
        }
    }

    /// One application step: halt completes; otherwise E-β yields the next
    /// redex for the trampoline.
    fn step(&mut self, p: &mut Program, f: EvalValue, a: EvalValue) -> Result<Step, EvalError> {
        let EvalValue::Func(label) = f else {
            return Err(EvalError::NotAFunction);
        };
        if self.halt == Some(label) {
            return Ok(Step::Done(a));
        }
        if p.body(label).is_none() {
            return Err(EvalError::UnsetBody(p.name(label)));
        }
        let arg = self.reify(p, &a);
        let reduced = p.beta_reduce(label, arg);
        Ok(Step::Continue(reduced))
    }

    /// Recursive evaluation for non-tail positions (arguments, direct-style
    /// programs); depth is bounded by expression nesting.
    fn eval_sub(&mut self, p: &mut Program, e: ExprId) -> Result<EvalValue, EvalError> {
        self.steps += 1;
        if self.steps > self.limit {
            return Err(EvalError::StepLimit);
        }
        match p.expr(e).kind.clone() {
            ExprKind::Const(c) => Ok(match c {
                Const::I64(v) => EvalValue::I64(v),
                Const::F64(bits) => EvalValue::F64(f64::from_bits(bits)),
                Const::Bool(v) => EvalValue::Bool(v),
                Const::Byte(v) => EvalValue::Byte(v),
                Const::Void => EvalValue::Void,
                Const::StaticPtr(off) => EvalValue::Ptr(off),
                Const::Slot(index) => EvalValue::Cell(index as usize),
            }),
            // V-Fun: a label is a value.
            ExprKind::Func(l) => Ok(EvalValue::Func(l)),
            // A free variable in a closed evaluation is a lowering bug.
            ExprKind::Var(l) => Err(EvalError::UnboundVariable(p.name(l))),
            // E-App1 / E-App2 / E-β (non-tail position: recurse, but the
            // applied body re-enters the trampoline).
            ExprKind::App(f, a) => {
                let vf = self.eval_sub(p, f)?;
                let va = self.eval_sub(p, a)?;
                self.apply(p, vf, va)
            }
            ExprKind::Tuple(items) => {
                let mut values = Vec::with_capacity(items.len());
                for item in items.iter() {
                    values.push(self.eval_sub(p, *item)?);
                }
                Ok(EvalValue::Tuple(values))
            }
            ExprKind::Extract(inner, index) => match self.eval_sub(p, inner)? {
                EvalValue::Tuple(items) => Ok(items[index as usize].clone()),
                _ => Err(EvalError::Unsupported("extract from non-tuple".into())),
            },
            ExprKind::PrimOp(op, args, ty) => self.primop(p, op, &args, ty),
        }
    }

    fn apply(
        &mut self,
        p: &mut Program,
        f: EvalValue,
        a: EvalValue,
    ) -> Result<EvalValue, EvalError> {
        let EvalValue::Func(label) = f else {
            return Err(EvalError::NotAFunction);
        };
        if self.halt == Some(label) {
            // The top-level continuation: evaluation is complete.
            return Ok(a);
        }
        if p.body(label).is_none() {
            return Err(EvalError::UnsetBody(p.name(label)));
        }
        // E-β: substitute the argument value (reified back into the term
        // language — values are a sub-grammar of expressions) and continue.
        let arg = self.reify(p, &a);
        let reduced = p.beta_reduce(label, arg);
        // Re-enter the trampoline so CPS spines don't grow the host stack.
        self.eval(p, reduced)
    }

    /// Values are expressions (paper: val ℓ, val c, tuples of values).
    /// Records reify as `RecordNew` of reified fields — a value form, like
    /// tuples.
    fn reify(&mut self, p: &mut Program, v: &EvalValue) -> ExprId {
        match v {
            EvalValue::I64(x) => p.int(*x),
            EvalValue::F64(x) => p.float(*x),
            EvalValue::Bool(x) => p.bool(*x),
            EvalValue::Byte(x) => {
                let ty = p.ty(TyKind::Byte);
                p.constant(Const::Byte(*x), ty)
            }
            EvalValue::Void => p.void(),
            EvalValue::Ptr(addr) => {
                let ty = p.ty_ptr();
                p.constant(Const::StaticPtr(*addr), ty)
            }
            EvalValue::Func(l) => p.func_ref(*l),
            EvalValue::Tuple(items) => {
                let reified: Vec<ExprId> = items.iter().map(|i| self.reify(p, i)).collect();
                p.tuple(&reified)
            }
            EvalValue::Record(symbol, fields) => {
                let reified: Vec<ExprId> = fields.iter().map(|f| self.reify(p, f)).collect();
                let ty = p.ty(TyKind::Boxed(*symbol));
                p.primop(Op::RecordNew(*symbol), &reified, ty)
            }
            // Variants reify like records: `VariantNew` of reified
            // payloads is a value form.
            EvalValue::Variant(symbol, tag, payloads) => {
                let reified: Vec<ExprId> = payloads.iter().map(|f| self.reify(p, f)).collect();
                let ty = p.ty(TyKind::Variant(*symbol));
                p.primop(Op::VariantNew(*symbol, *tag), &reified, ty)
            }
            EvalValue::Cell(index) => {
                let ty = self.slot_tys[*index];
                p.constant(Const::Slot(*index as u32), ty)
            }
        }
    }

    fn primop(
        &mut self,
        p: &mut Program,
        op: Op,
        args: &[ExprId],
        result_ty: crate::lambda_g::expr::TyId,
    ) -> Result<EvalValue, EvalError> {
        match op {
            // br(cond, t, f): select a thunk and apply it to () (§2.2).
            Op::Br => {
                let cond = self.eval_sub(p, args[0])?;
                let chosen = if cond == EvalValue::Bool(true) {
                    args[1]
                } else {
                    args[2]
                };
                let thunk = self.eval_sub(p, chosen)?;
                let unit = self.unit_for(p, chosen);
                self.apply(p, thunk, unit)
            }
            Op::Switch => {
                let EvalValue::I64(tag) = self.eval_sub(p, args[0])? else {
                    return Err(EvalError::Unsupported("switch on non-int".into()));
                };
                let arms = &args[1..args.len() - 1];
                let chosen = arms
                    .get(tag as usize)
                    .copied()
                    .unwrap_or(args[args.len() - 1]);
                let thunk = self.eval_sub(p, chosen)?;
                let unit = self.unit_for(p, chosen);
                self.apply(p, thunk, unit)
            }
            Op::Add | Op::Sub | Op::Mul | Op::Div => {
                let a = self.eval_sub(p, args[0])?;
                let b = self.eval_sub(p, args[1])?;
                self.arith(op, a, b)
            }
            Op::Cmp(cmp) => {
                let a = self.eval_sub(p, args[0])?;
                let b = self.eval_sub(p, args[1])?;
                self.compare(cmp, a, b)
            }
            Op::Trunc => match self.eval_sub(p, args[0])? {
                EvalValue::F64(x) => Ok(EvalValue::I64(x.trunc() as i64)),
                _ => Err(EvalError::Unsupported("trunc on non-float".into())),
            },
            Op::IToF => match self.eval_sub(p, args[0])? {
                EvalValue::I64(x) => Ok(EvalValue::F64(x as f64)),
                _ => Err(EvalError::Unsupported("itof on non-int".into())),
            },
            Op::CellNew => {
                let init = self.eval_sub(p, args[0])?;
                let init_ty = p.expr(args[0]).ty;
                let ty = p.ty_cell(init_ty);
                self.slots.push(init);
                self.slot_tys.push(ty);
                Ok(EvalValue::Cell(self.slots.len() - 1))
            }
            Op::CellGet => match self.eval_sub(p, args[0])? {
                EvalValue::Cell(index) => Ok(self.slots[index].clone()),
                _ => Err(EvalError::Unsupported("cell_get on non-cell".into())),
            },
            Op::CellSet => {
                let cell = self.eval_sub(p, args[0])?;
                let value = self.eval_sub(p, args[1])?;
                match cell {
                    EvalValue::Cell(index) => {
                        self.slots[index] = value;
                        Ok(EvalValue::Void)
                    }
                    _ => Err(EvalError::Unsupported("cell_set on non-cell".into())),
                }
            }
            // Records are functional values; field update copies (mutable
            // value semantics — Racordon et al., JOT 2022 §3, value
            // independence).
            Op::RecordNew(symbol) => {
                let mut fields = Vec::with_capacity(args.len());
                for arg in args {
                    fields.push(self.eval_sub(p, *arg)?);
                }
                Ok(EvalValue::Record(symbol, fields))
            }
            Op::GetField(index) => match self.eval_sub(p, args[0])? {
                EvalValue::Record(_, fields) => fields
                    .get(index as usize)
                    .cloned()
                    .ok_or_else(|| EvalError::Unsupported("field index out of range".into())),
                _ => Err(EvalError::Unsupported("get_field on non-record".into())),
            },
            // Variants mirror records: pure construction and projection;
            // GetTag feeds Switch (the decision-tree dispatch — Maranget,
            // ML 2008).
            Op::VariantNew(symbol, tag) => {
                let mut payloads = Vec::with_capacity(args.len());
                for arg in args {
                    payloads.push(self.eval_sub(p, *arg)?);
                }
                Ok(EvalValue::Variant(symbol, tag, payloads))
            }
            Op::GetTag => match self.eval_sub(p, args[0])? {
                EvalValue::Variant(_, tag, _) => Ok(EvalValue::I64(tag as i64)),
                _ => Err(EvalError::Unsupported("get_tag on non-variant".into())),
            },
            Op::GetPayload(index) => match self.eval_sub(p, args[0])? {
                EvalValue::Variant(_, _, payloads) => payloads
                    .get(index as usize)
                    .cloned()
                    .ok_or_else(|| EvalError::Unsupported("payload index out of range".into())),
                _ => Err(EvalError::Unsupported("get_payload on non-variant".into())),
            },
            Op::SetField(index) => {
                let record = self.eval_sub(p, args[0])?;
                let value = self.eval_sub(p, args[1])?;
                match record {
                    EvalValue::Record(symbol, mut fields) => {
                        if index as usize >= fields.len() {
                            return Err(EvalError::Unsupported("field index out of range".into()));
                        }
                        fields[index as usize] = value;
                        Ok(EvalValue::Record(symbol, fields))
                    }
                    _ => Err(EvalError::Unsupported("set_field on non-record".into())),
                }
            }
            // Raw memory: bump allocation over statics++heap (no free in
            // the reference evaluator).
            Op::Alloc => match self.eval_sub(p, args[0])? {
                EvalValue::I64(count) if count >= 0 => {
                    let addr = self.mem.len() as u32;
                    self.mem.resize(self.mem.len() + count as usize, 0);
                    Ok(EvalValue::Ptr(addr))
                }
                _ => Err(EvalError::Unsupported("alloc count".into())),
            },
            // Width and representation come from the primop's λ_G type
            // (see TyKind::mem_size).
            Op::Load => match self.eval_sub(p, args[0])? {
                EvalValue::Ptr(addr) => self.load(p, addr, result_ty),
                _ => Err(EvalError::Unsupported("load on non-pointer".into())),
            },
            Op::Store => {
                let ptr = self.eval_sub(p, args[0])?;
                let value = self.eval_sub(p, args[1])?;
                let EvalValue::Ptr(addr) = ptr else {
                    return Err(EvalError::Unsupported("store on non-pointer".into()));
                };
                let value_ty = p.expr_ty(args[1]);
                self.store(p, addr, value, value_ty)
            }
            Op::Copy => {
                let from = self.eval_sub(p, args[0])?;
                let to = self.eval_sub(p, args[1])?;
                let len = self.eval_sub(p, args[2])?;
                let (EvalValue::Ptr(from), EvalValue::Ptr(to), EvalValue::I64(len)) =
                    (from, to, len)
                else {
                    return Err(EvalError::Unsupported("copy operands".into()));
                };
                let (from, to, len) = (from as usize, to as usize, len as usize);
                if from + len > self.mem.len() || to + len > self.mem.len() {
                    return Err(EvalError::Unsupported("copy out of bounds".into()));
                }
                self.mem.copy_within(from..from + len, to);
                Ok(EvalValue::Void)
            }
            // The io dialect runs against the captured IO (simulated
            // descriptors; sleeping is a no-op — the evaluator exists to
            // be compared against, and tests must stay fast).
            Op::IoRead
            | Op::IoWrite
            | Op::IoOpen
            | Op::IoClose
            | Op::IoSleep
            | Op::IoPoll
            | Op::IoCtl
            | Op::IoSocket
            | Op::IoBind
            | Op::IoListen
            | Op::IoConnect
            | Op::IoAccept => {
                let mut operands = [EvalValue::Void, EvalValue::Void, EvalValue::Void];
                for (slot, &arg) in operands.iter_mut().zip(args.iter()) {
                    *slot = self.eval_sub(p, arg)?;
                }
                self.run_io(op, operands).map(EvalValue::I64)
            }
            other => Err(EvalError::Unsupported(format!("{other:?}"))),
        }
    }

    /// One io operation: marshal pointer operands against this
    /// evaluator's byte memory and call through the captured IO — the
    /// mirror of the VM's `run_io`, so the engines agree on io by
    /// construction. POSIX return conventions.
    fn run_io(&mut self, op: Op, operands: [EvalValue; 3]) -> Result<i64, EvalError> {
        let int = |index: usize| -> Result<i64, EvalError> {
            match operands[index] {
                EvalValue::I64(v) => Ok(v),
                ref other => Err(EvalError::Unsupported(format!(
                    "io integer operand, got {other:?}"
                ))),
            }
        };
        let ptr = |index: usize| -> Result<usize, EvalError> {
            match operands[index] {
                EvalValue::Ptr(off) => Ok(off as usize),
                ref other => Err(EvalError::Unsupported(format!(
                    "io pointer operand, got {other:?}"
                ))),
            }
        };
        let oob = || EvalError::Unsupported("io access out of bounds".into());
        Ok(match op {
            Op::IoWrite => {
                let (fd, start, len) = (int(0)?, ptr(1)?, int(2)? as usize);
                let bytes = self.mem.get(start..start + len).ok_or_else(oob)?;
                self.io.write(fd, bytes)
            }
            Op::IoRead => {
                let (fd, start, len) = (int(0)?, ptr(1)?, int(2)? as usize);
                let buf = self.mem.get_mut(start..start + len).ok_or_else(oob)?;
                self.io.read(fd, buf)
            }
            Op::IoOpen => {
                let start = ptr(0)?;
                let tail = self.mem.get(start..).ok_or_else(oob)?;
                let len = tail.iter().position(|&byte| byte == 0).unwrap_or(tail.len());
                let path = tail[..len].to_vec();
                self.io.open(&path, int(1)?, int(2)?)
            }
            Op::IoClose => self.io.close(int(0)?),
            Op::IoSleep => self.io.sleep(int(0)?),
            Op::IoCtl => self.io.ctl(int(0)?, int(1)?, int(2)?),
            Op::IoPoll => {
                let (start, count, timeout) = (ptr(0)?, int(1)? as usize, int(2)?);
                let records = self.mem.get(start..start + count * 8).ok_or_else(oob)?;
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
                let result = self.io.poll(&mut fds, timeout);
                for (index, (_, _, revents)) in fds.iter().enumerate() {
                    let at = start + index * 8 + 6;
                    let slot = self.mem.get_mut(at..at + 2).ok_or_else(oob)?;
                    slot.copy_from_slice(&revents.to_le_bytes());
                }
                result
            }
            Op::IoSocket => self.io.socket(int(0)?, int(1)?, int(2)?),
            Op::IoBind => self.io.bind(int(0)?, int(1)?, int(2)?),
            Op::IoListen => self.io.listen(int(0)?, int(1)?),
            Op::IoConnect => self.io.connect(int(0)?, int(1)?, int(2)?),
            Op::IoAccept => self.io.accept(int(0)?),
            other => {
                return Err(EvalError::Unsupported(format!("not an io op: {other:?}")));
            }
        })
    }

    /// One sized read from raw memory. Scalars are little-endian machine
    /// words (Byte is 1 byte); aggregates read an 8-byte handle into the
    /// boxed arena.
    fn load(
        &mut self,
        p: &Program,
        addr: u32,
        ty: crate::lambda_g::expr::TyId,
    ) -> Result<EvalValue, EvalError> {
        match p.ty_kind(ty) {
            TyKind::Byte => self
                .mem
                .get(addr as usize)
                .copied()
                .map(EvalValue::Byte)
                .ok_or_else(|| EvalError::Unsupported("load out of bounds".into())),
            TyKind::I64 => Ok(EvalValue::I64(self.read_word(addr)? as i64)),
            TyKind::F64 => Ok(EvalValue::F64(f64::from_bits(self.read_word(addr)?))),
            TyKind::Bool => Ok(EvalValue::Bool(self.read_word(addr)? != 0)),
            TyKind::Ptr => Ok(EvalValue::Ptr(self.read_word(addr)? as u32)),
            TyKind::Boxed(_) | TyKind::Variant(_) | TyKind::Tuple(_) => {
                let handle = self.read_word(addr)? as usize;
                self.boxed
                    .get(handle)
                    .cloned()
                    .ok_or_else(|| EvalError::Unsupported("load of a bad arena handle".into()))
            }
            other => Err(EvalError::Unsupported(format!("load of type {other:?}"))),
        }
    }

    /// One sized write to raw memory; aggregates park in the boxed arena
    /// and the cell holds the handle.
    fn store(
        &mut self,
        p: &Program,
        addr: u32,
        value: EvalValue,
        ty: crate::lambda_g::expr::TyId,
    ) -> Result<EvalValue, EvalError> {
        let word = match p.ty_kind(ty) {
            TyKind::Byte => {
                let EvalValue::Byte(byte) = value else {
                    return Err(EvalError::Unsupported("store byte mismatch".into()));
                };
                let slot = self
                    .mem
                    .get_mut(addr as usize)
                    .ok_or_else(|| EvalError::Unsupported("store out of bounds".into()))?;
                *slot = byte;
                return Ok(EvalValue::Void);
            }
            TyKind::I64 => {
                let EvalValue::I64(v) = value else {
                    return Err(EvalError::Unsupported("store int mismatch".into()));
                };
                v as u64
            }
            TyKind::F64 => {
                let EvalValue::F64(v) = value else {
                    return Err(EvalError::Unsupported("store float mismatch".into()));
                };
                v.to_bits()
            }
            TyKind::Bool => {
                let EvalValue::Bool(v) = value else {
                    return Err(EvalError::Unsupported("store bool mismatch".into()));
                };
                v as u64
            }
            TyKind::Ptr => {
                let EvalValue::Ptr(v) = value else {
                    return Err(EvalError::Unsupported("store pointer mismatch".into()));
                };
                v as u64
            }
            TyKind::Boxed(_) | TyKind::Variant(_) | TyKind::Tuple(_) => {
                self.boxed.push(value);
                (self.boxed.len() - 1) as u64
            }
            other => {
                return Err(EvalError::Unsupported(format!("store of type {other:?}")));
            }
        };
        let start = addr as usize;
        let slot = self
            .mem
            .get_mut(start..start + 8)
            .ok_or_else(|| EvalError::Unsupported("store out of bounds".into()))?;
        slot.copy_from_slice(&word.to_le_bytes());
        Ok(EvalValue::Void)
    }

    fn read_word(&self, addr: u32) -> Result<u64, EvalError> {
        let start = addr as usize;
        let bytes = self
            .mem
            .get(start..start + 8)
            .ok_or_else(|| EvalError::Unsupported("load out of bounds".into()))?;
        let mut buf = [0u8; 8];
        buf.copy_from_slice(bytes);
        Ok(u64::from_le_bytes(buf))
    }

    /// The unit argument for a thunk of type [] → R: an empty tuple.
    fn unit_for(&mut self, p: &mut Program, thunk_expr: ExprId) -> EvalValue {
        let ty = p.expr_ty(thunk_expr);
        if let TyKind::Fn(dom, _) = p.ty_kind(ty)
            && matches!(p.ty_kind(*dom), TyKind::Void)
        {
            return EvalValue::Void;
        }
        EvalValue::Tuple(vec![])
    }

    fn arith(&self, op: Op, a: EvalValue, b: EvalValue) -> Result<EvalValue, EvalError> {
        use EvalValue::*;
        Ok(match (op, a, b) {
            (Op::Add, I64(x), I64(y)) => I64(x.wrapping_add(y)),
            (Op::Sub, I64(x), I64(y)) => I64(x.wrapping_sub(y)),
            (Op::Mul, I64(x), I64(y)) => I64(x.wrapping_mul(y)),
            (Op::Div, I64(_), I64(0)) => return Err(EvalError::DivisionByZero),
            (Op::Div, I64(x), I64(y)) => I64(x.wrapping_div(y)),
            (Op::Add, F64(x), F64(y)) => F64(x + y),
            (Op::Sub, F64(x), F64(y)) => F64(x - y),
            (Op::Mul, F64(x), F64(y)) => F64(x * y),
            (Op::Div, F64(x), F64(y)) => F64(x / y),
            // Pointer arithmetic (`add RawPtr p offset` in the @_ir
            // dialect).
            (Op::Add, Ptr(p), I64(off)) => Ptr((p as i64 + off) as u32),
            (Op::Sub, Ptr(p), I64(off)) => Ptr((p as i64 - off) as u32),
            _ => return Err(EvalError::Unsupported("arith operand types".into())),
        })
    }

    fn compare(&self, op: CmpOp, a: EvalValue, b: EvalValue) -> Result<EvalValue, EvalError> {
        use EvalValue::*;
        let result = match (&a, &b) {
            (I64(x), I64(y)) => match op {
                CmpOp::Eq => x == y,
                CmpOp::Ne => x != y,
                CmpOp::Lt => x < y,
                CmpOp::Le => x <= y,
                CmpOp::Gt => x > y,
                CmpOp::Ge => x >= y,
            },
            (F64(x), F64(y)) => match op {
                CmpOp::Eq => x == y,
                CmpOp::Ne => x != y,
                CmpOp::Lt => x < y,
                CmpOp::Le => x <= y,
                CmpOp::Gt => x > y,
                CmpOp::Ge => x >= y,
            },
            (Byte(x), Byte(y)) => match op {
                CmpOp::Eq => x == y,
                CmpOp::Ne => x != y,
                CmpOp::Lt => x < y,
                CmpOp::Le => x <= y,
                CmpOp::Gt => x > y,
                CmpOp::Ge => x >= y,
            },
            (Bool(x), Bool(y)) => match op {
                CmpOp::Eq => x == y,
                CmpOp::Ne => x != y,
                _ => return Err(EvalError::Unsupported("bool ordering".into())),
            },
            _ => return Err(EvalError::Unsupported("cmp operand types".into())),
        };
        Ok(Bool(result))
    }
}
