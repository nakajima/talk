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
    pub out: Vec<u8>,
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
            out: vec![],
            steps: 0,
            limit: 50_000_000,
            mem: vec![],
            slots: vec![],
            slot_tys: vec![],
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
            ExprKind::PrimOp(op, args, _) => self.primop(p, op, &args),
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
            EvalValue::Cell(index) => {
                let ty = self.slot_tys[*index];
                p.constant(Const::Slot(*index as u32), ty)
            }
        }
    }

    fn primop(&mut self, p: &mut Program, op: Op, args: &[ExprId]) -> Result<EvalValue, EvalError> {
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
                let ty = match p.expr(args[0]).ty {
                    t => {
                        let cell = p.ty_cell(t);
                        cell
                    }
                };
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
            Op::Load => match self.eval_sub(p, args[0])? {
                EvalValue::Ptr(addr) => {
                    let byte = self
                        .mem
                        .get(addr as usize)
                        .copied()
                        .ok_or_else(|| EvalError::Unsupported("load out of bounds".into()))?;
                    // Width comes from the primop's result type; only bytes
                    // exist in memory until Array lands (M5).
                    Ok(EvalValue::Byte(byte))
                }
                _ => Err(EvalError::Unsupported("load on non-pointer".into())),
            },
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
            Op::IoWrite => {
                let fd = self.eval_sub(p, args[0])?;
                let buf = self.eval_sub(p, args[1])?;
                let count = self.eval_sub(p, args[2])?;
                let (EvalValue::I64(_fd), EvalValue::Ptr(off), EvalValue::I64(len)) =
                    (fd, buf, count)
                else {
                    return Err(EvalError::Unsupported("io_write operands".into()));
                };
                let start = off as usize;
                let end = start + len as usize;
                if end > self.mem.len() {
                    return Err(EvalError::Unsupported("io_write out of bounds".into()));
                }
                // The reference evaluator always captures (it exists to be
                // compared against); fd routing belongs to the VM's IO
                // trait.
                let bytes = self.mem[start..end].to_vec();
                self.out.extend_from_slice(&bytes);
                Ok(EvalValue::I64(len))
            }
            other => Err(EvalError::Unsupported(format!("{other:?}"))),
        }
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
