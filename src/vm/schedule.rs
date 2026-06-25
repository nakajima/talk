//! λ_G → bytecode: the paper's §4.1 "translation to lexical scoping" case
//! study retargeted at chunks/blocks, composed with Thorin's call/return
//! reconstruction (Leißa, Köster & Hack, CGO 2015): a CPS application
//! becomes a `Call` when the callee is a chunk-forming function, a `Jump`
//! when it is one of the chunk's own continuations, and a `Ret` when it is
//! the function's return continuation (`Extract(var F, arity)`). Well-known
//! continuations are join points and never become closures (Maurer, Downen,
//! Ariola & Peyton Jones, *Compiling without Continuations*, PLDI 2017) —
//! here they become blocks sharing the chunk's register frame.
//!
//! **Deviation from §4 nesting:** block ownership is computed by
//! function-reference reachability from each chunk-forming function, not by
//! the FV nesting tree. The nesting tree places *closed* continuations
//! (constant-bodied branch thunks have no free variables) at the forest
//! root, but they must still schedule as blocks of their unique referencing
//! chunk. The chunk set itself is producer knowledge: the lowerer's
//! demanded specializations plus `main` (in lieu of Thorin's structural
//! "top-level function" recovery). Sharing one continuation between two
//! chunks is a construction error and is rejected.

use crate::lambda_g::expr::{Const, ExprId, ExprKind, Op, TyKind};
use crate::lambda_g::program::{Label, Program};
use crate::vm::interp::Value;
use crate::vm::{Chunk, Insn, IoOp, Module};
use rustc_hash::{FxHashMap, FxHashSet};

pub fn schedule(
    p: &mut Program,
    main: Label,
    entry_funcs: &FxHashSet<Label>,
) -> Result<Module, String> {
    // Deterministic chunk order: main first (entry chunk 0), the rest by
    // label.
    let mut order: Vec<Label> = vec![main];
    let mut rest: Vec<Label> = entry_funcs.iter().copied().filter(|l| *l != main).collect();
    rest.sort_by_key(|l| l.0);
    order.extend(rest);
    let chunk_of: FxHashMap<Label, u32> = order
        .iter()
        .enumerate()
        .map(|(i, l)| (*l, i as u32))
        .collect();

    // Closure environments, precomputed: every chunk's free variables in
    // sorted label order (flat closures — Cardelli 1984; the environment
    // layout is shared by MakeClosure sites and the chunk's EnvGet reads,
    // both derived from this one map).
    let mut env_of: FxHashMap<Label, Vec<Label>> = FxHashMap::default();
    for &label in chunk_of.keys() {
        let fv = p.fv(label);
        let mut captured = p.set_labels(fv);
        captured.sort_by_key(|l| l.0);
        env_of.insert(label, captured);
    }

    let mut module = Module {
        statics: p.static_mem.clone(),
        ..Module::default()
    };
    let mut consts: FxHashMap<Const, u32> = FxHashMap::default();
    let mut claimed: FxHashSet<Label> = FxHashSet::default();
    for func in order {
        let chunk = ChunkBuilder::new(
            p,
            func,
            &chunk_of,
            &env_of,
            &mut module,
            &mut consts,
            &mut claimed,
        )
        .build()?;
        module.chunks.push(chunk);
    }
    module.entry = 0;
    Ok(module)
}

/// Where a reconstructed call transfers to: a statically-known chunk, or a
/// closure value in a register.
#[derive(Clone, Copy)]
enum CallTarget {
    Chunk(u32),
    Closure(u16),
}

/// Builds one chunk: the function's body is block 0; each continuation it
/// (transitively) references becomes a block with one parameter register.
/// All blocks share the frame, so a continuation's variable is just a
/// register every block can read — exactly the λ_G picture where nested
/// functions close over `var ℓ`.
struct ChunkBuilder<'a> {
    p: &'a Program,
    func: Label,
    chunk_of: &'a FxHashMap<Label, u32>,
    /// Every chunk's captured labels in environment order (sorted).
    env_of: &'a FxHashMap<Label, Vec<Label>>,
    module: &'a mut Module,
    consts: &'a mut FxHashMap<Const, u32>,
    claimed_global: &'a mut FxHashSet<Label>,
    arity: u16,
    next_reg: u32,
    param_reg: FxHashMap<Label, u16>,
    block_of: FxHashMap<Label, u32>,
    block_order: Vec<Label>,
    /// Per-block value numbering for *pure* expressions only; cell
    /// operations re-emit per occurrence (matching the substitution
    /// evaluator, which re-evaluates each shared occurrence).
    memo: FxHashMap<ExprId, u16>,
    code: Vec<Insn>,
}

impl<'a> ChunkBuilder<'a> {
    fn new(
        p: &'a Program,
        func: Label,
        chunk_of: &'a FxHashMap<Label, u32>,
        env_of: &'a FxHashMap<Label, Vec<Label>>,
        module: &'a mut Module,
        consts: &'a mut FxHashMap<Const, u32>,
        claimed_global: &'a mut FxHashSet<Label>,
    ) -> Self {
        // dom is Tuple([params…, ret_k]) by lowerer convention; anything
        // else (e.g. a diagnostic placeholder function) is a 0-ary chunk.
        let arity = match p.ty_kind(p.dom(func)) {
            TyKind::Tuple(items) => items.len().saturating_sub(1) as u16,
            _ => 0,
        };
        ChunkBuilder {
            p,
            func,
            chunk_of,
            env_of,
            module,
            consts,
            claimed_global,
            arity,
            next_reg: arity as u32,
            param_reg: FxHashMap::default(),
            block_of: FxHashMap::default(),
            block_order: vec![],
            memo: FxHashMap::default(),
            code: vec![],
        }
    }

    fn build(mut self) -> Result<Chunk, String> {
        self.claim()?;

        // Emit per-block instruction lists with block ids as jump targets,
        // then concatenate and patch to instruction offsets.
        let entry_body = self.p.body(self.func);
        let blocks = self.block_order.clone();
        let mut chunks_of_insns: Vec<Vec<Insn>> = Vec::with_capacity(blocks.len() + 1);
        chunks_of_insns.push(self.emit_block(entry_body)?);
        for label in blocks {
            let body = self.p.body(label);
            chunks_of_insns.push(self.emit_block(body)?);
        }

        let mut offsets = Vec::with_capacity(chunks_of_insns.len());
        let mut total = 0u32;
        for block in &chunks_of_insns {
            offsets.push(total);
            total += block.len() as u32;
        }
        let mut code = Vec::with_capacity(total as usize);
        for block in chunks_of_insns {
            code.extend(block);
        }
        for insn in &mut code {
            match insn {
                Insn::Jump { target } => *target = offsets[*target as usize],
                Insn::Branch {
                    then_target,
                    else_target,
                    ..
                } => {
                    *then_target = offsets[*then_target as usize];
                    *else_target = offsets[*else_target as usize];
                }
                // Each Switch owns its pool range exclusively, so patching
                // through the instruction patches each entry exactly once.
                Insn::Switch {
                    targets_start,
                    targets_len,
                    ..
                } => {
                    let start = *targets_start as usize;
                    let end = start + *targets_len as usize;
                    for target in &mut self.module.switch_pool[start..end] {
                        *target = offsets[*target as usize];
                    }
                }
                _ => {}
            }
        }

        if self.next_reg > u16::MAX as u32 {
            return Err(format!(
                "scheduling {}: register count {} exceeds u16",
                self.p.name(self.func),
                self.next_reg
            ));
        }
        Ok(Chunk {
            name: self.p.name(self.func),
            code,
            arity: self.arity,
            n_regs: self.next_reg as u16,
        })
    }

    /// Claim this chunk's continuations: every label reachable from the
    /// function body through `Func` references that is not itself a chunk.
    /// Discovery order is block order (deterministic).
    fn claim(&mut self) -> Result<(), String> {
        let Some(body) = self.p.body(self.func) else {
            return Ok(());
        };
        let mut work: Vec<Label> = self.p.set_labels(self.p.expr(body).lf);
        while let Some(label) = work.pop() {
            if self.chunk_of.contains_key(&label) || self.block_of.contains_key(&label) {
                continue;
            }
            if !self.claimed_global.insert(label) {
                return Err(format!(
                    "scheduling {}: continuation {} is referenced from more than one chunk",
                    self.p.name(self.func),
                    self.p.name(label)
                ));
            }
            // Block ids are offset by 1: block 0 is the function body.
            self.block_of
                .insert(label, self.block_order.len() as u32 + 1);
            self.block_order.push(label);
            let reg = self.fresh();
            self.param_reg.insert(label, reg);
            if let Some(b) = self.p.body(label) {
                work.extend(self.p.set_labels(self.p.expr(b).lf));
            }
        }
        Ok(())
    }

    fn fresh(&mut self) -> u16 {
        let reg = self.next_reg;
        self.next_reg += 1;
        // Overflow is reported once at build() with the final count.
        reg as u16
    }

    fn const_index(&mut self, c: Const, value: Value) -> u32 {
        if let Some(&index) = self.consts.get(&c) {
            return index;
        }
        let index = self.module.consts.len() as u32;
        self.module.consts.push(value);
        self.consts.insert(c, index);
        index
    }

    fn trap(&mut self, message: String) -> Insn {
        let index = self.module.traps.len() as u32;
        self.module.traps.push(message);
        Insn::Trap { message: index }
    }

    // ----- Block emission ---------------------------------------------------

    fn emit_block(&mut self, body: Option<ExprId>) -> Result<Vec<Insn>, String> {
        self.memo.clear();
        self.code.clear();
        match body {
            Some(body) => self.emit_terminal(body)?,
            None => {
                let trap = self.trap(format!(
                    "vm: function {} has no body (unsupported construct upstream)",
                    self.p.name(self.func)
                ));
                self.code.push(trap);
            }
        }
        Ok(std::mem::take(&mut self.code))
    }

    /// A ⊥-typed body is one of: a call (App of a chunk function), a jump
    /// (App of an owned continuation), a return (App of the ret
    /// continuation), or a branch primop. Thorin CGO 2015's reconstruction.
    fn emit_terminal(&mut self, e: ExprId) -> Result<(), String> {
        match &self.p.expr(e).kind {
            ExprKind::App(f, a) => {
                let (f, a) = (*f, *a);
                match &self.p.expr(f).kind {
                    ExprKind::Func(label) if self.chunk_of.contains_key(label) => {
                        let label = *label;
                        // A chunk with captures is entered through a
                        // closure so its environment rides along.
                        if self.env_of.get(&label).is_some_and(|env| !env.is_empty()) {
                            let callee = self.make_closure(label, f)?;
                            self.emit_call_like(CallTarget::Closure(callee), a)
                        } else {
                            self.emit_call_like(CallTarget::Chunk(self.chunk_of[&label]), a)
                        }
                    }
                    ExprKind::Func(label) if self.block_of.contains_key(label) => {
                        let label = *label;
                        let src = self.eval(a)?;
                        let dest = self.param_reg[&label];
                        if dest != src {
                            self.code.push(Insn::Move { dest, src });
                        }
                        self.code.push(Insn::Jump {
                            target: self.block_of[&label],
                        });
                        Ok(())
                    }
                    _ if self.is_ret_k(f) => {
                        let src = self.eval(a)?;
                        self.code.push(Insn::Ret { src });
                        Ok(())
                    }
                    // A computed callee: a closure value in a register
                    // (CallIndirect — retires the M2 trap).
                    _ => {
                        let callee = self.eval(f)?;
                        self.emit_call_like(CallTarget::Closure(callee), a)
                    }
                }
            }
            ExprKind::PrimOp(Op::Switch, args, _) => {
                // switch(tag, k_0, …, k_n, default): a jump table over the
                // tag (decision-tree dispatch — Maranget, ML 2008). All
                // arms must be direct continuation references.
                let (tag, targets) = (args[0], &args[1..]);
                let tag = self.eval(tag)?;
                let mut resolved = Vec::with_capacity(targets.len());
                for &target in targets {
                    match self.thunk_block(target)? {
                        Some(block) => resolved.push(block),
                        None => {
                            let trap =
                                self.trap("vm: switch arm is not a direct continuation".into());
                            self.code.push(trap);
                            return Ok(());
                        }
                    }
                }
                let targets_start = self.module.switch_pool.len() as u32;
                let targets_len = resolved.len() as u16;
                self.module.switch_pool.extend(resolved);
                self.code.push(Insn::Switch {
                    tag,
                    targets_start,
                    targets_len,
                });
                Ok(())
            }
            ExprKind::PrimOp(Op::Br, args, _) => {
                let (cond, then_ref, else_ref) = (args[0], args[1], args[2]);
                let cond = self.eval(cond)?;
                let then_target = self.thunk_block(then_ref)?;
                let else_target = self.thunk_block(else_ref)?;
                match (then_target, else_target) {
                    (Some(then_target), Some(else_target)) => {
                        self.code.push(Insn::Branch {
                            cond,
                            then_target,
                            else_target,
                        });
                    }
                    _ => {
                        let trap = self.trap("vm: br arm is not a direct continuation".into());
                        self.code.push(trap);
                    }
                }
                Ok(())
            }
            _ => {
                let trap = self.trap(format!(
                    "vm: unsupported terminal {} in {}",
                    self.p.render_expr(e),
                    self.p.name(self.func)
                ));
                self.code.push(trap);
                Ok(())
            }
        }
    }

    fn thunk_block(&self, e: ExprId) -> Result<Option<u32>, String> {
        match &self.p.expr(e).kind {
            ExprKind::Func(label) => Ok(self.block_of.get(label).copied()),
            _ => Ok(None),
        }
    }

    /// `App(callee, Tuple([args…, k]))`: evaluate the arguments, then
    /// reconstruct the call (Thorin CGO 2015): k = owned continuation →
    /// call into its parameter register and fall through to its block;
    /// k = ret continuation → call then `Ret` (a tail call; genuine TCO is
    /// a later optimization, flagged). The callee is a known chunk or a
    /// closure value in a register (CallIndirect).
    fn emit_call_like(&mut self, target: CallTarget, arg: ExprId) -> Result<(), String> {
        let items: Vec<ExprId> = match &self.p.expr(arg).kind {
            ExprKind::Tuple(items) => items.to_vec(),
            _ => {
                let trap = self.trap("vm: call argument is not a literal tuple".into());
                self.code.push(trap);
                return Ok(());
            }
        };
        let Some((&k, args)) = items.split_last() else {
            let trap = self.trap("vm: call without a return continuation".into());
            self.code.push(trap);
            return Ok(());
        };

        let mut arg_regs = Vec::with_capacity(args.len());
        for &a in args {
            arg_regs.push(self.eval(a)?);
        }
        let args_start = self.module.arg_pool.len() as u32;
        let args_len = arg_regs.len() as u16;
        self.module.arg_pool.extend(arg_regs);

        let call_insn = |dest: u16| match target {
            CallTarget::Chunk(chunk) => Insn::Call {
                dest,
                chunk,
                args_start,
                args_len,
            },
            CallTarget::Closure(callee) => Insn::CallIndirect {
                dest,
                callee,
                args_start,
                args_len,
            },
        };

        match &self.p.expr(k).kind {
            ExprKind::Func(label) if self.block_of.contains_key(label) => {
                let label = *label;
                self.code.push(call_insn(self.param_reg[&label]));
                self.code.push(Insn::Jump {
                    target: self.block_of[&label],
                });
                Ok(())
            }
            _ if self.is_ret_k(k) => {
                let dest = self.fresh();
                self.code.push(call_insn(dest));
                self.code.push(Insn::Ret { src: dest });
                Ok(())
            }
            _ => {
                let trap = self.trap("vm: call continuation is not a block or the return".into());
                self.code.push(trap);
                Ok(())
            }
        }
    }

    /// The environment index of a captured label in the CURRENT chunk.
    fn env_index(&self, label: Label) -> Option<u16> {
        self.env_of
            .get(&self.func)?
            .iter()
            .position(|l| *l == label)
            .map(|i| i as u16)
    }

    /// The register holding the value of `var ℓ` in the current chunk —
    /// what a closure over ℓ must capture.
    fn captured_value(&mut self, label: Label) -> Result<u16, String> {
        // An owned continuation's parameter register.
        if let Some(&reg) = self.param_reg.get(&label) {
            return Ok(reg);
        }
        // Captured here too: forward from our own environment.
        if let Some(index) = self.env_index(label) {
            let dest = self.fresh();
            self.code.push(Insn::EnvGet { dest, index });
            return Ok(dest);
        }
        // The chunk function itself: materialize its parameter tuple (the
        // closure body extracts params from it; its ret-continuation slot
        // is deliberately absent — capturing a return continuation is M9).
        if label == self.func {
            let args_start = self.module.arg_pool.len() as u32;
            let args_len = self.arity;
            self.module.arg_pool.extend(0..self.arity);
            let dest = self.fresh();
            self.code.push(Insn::TupleNew {
                dest,
                args_start,
                args_len,
            });
            return Ok(dest);
        }
        Err(format!(
            "scheduling {}: capture of {} is not available in this chunk",
            self.p.name(self.func),
            self.p.name(label)
        ))
    }

    /// MakeClosure for `label`, capturing its environment from the current
    /// chunk's registers.
    fn make_closure(&mut self, label: Label, e: ExprId) -> Result<u16, String> {
        let captured = self.env_of.get(&label).cloned().unwrap_or_default();
        let mut env_regs = Vec::with_capacity(captured.len());
        for l in captured {
            env_regs.push(self.captured_value(l)?);
        }
        let args_start = self.module.arg_pool.len() as u32;
        let args_len = env_regs.len() as u16;
        self.module.arg_pool.extend(env_regs);
        let dest = self.fresh();
        self.code.push(Insn::MakeClosure {
            dest,
            chunk: self.chunk_of[&label],
            args_start,
            args_len,
        });
        self.memo.insert(e, dest);
        Ok(dest)
    }

    /// Is this expression the chunk's return continuation,
    /// `Extract(var F, arity)`?
    fn is_ret_k(&self, e: ExprId) -> bool {
        if let ExprKind::Extract(inner, index) = &self.p.expr(e).kind
            && let ExprKind::Var(label) = &self.p.expr(*inner).kind
        {
            return *label == self.func && *index == self.arity as u32;
        }
        false
    }

    // ----- Value emission ---------------------------------------------------

    /// Lower a value expression to a register, value-numbering pure nodes
    /// per block (hash-consing already made sharing explicit; the memo just
    /// avoids recomputing it).
    fn eval(&mut self, e: ExprId) -> Result<u16, String> {
        if let Some(&reg) = self.memo.get(&e) {
            return Ok(reg);
        }
        let kind = self.p.expr(e).kind.clone();
        let reg = match kind {
            ExprKind::Const(c) => {
                let value = match c {
                    Const::I64(v) => Value::I64(v),
                    Const::F64(bits) => Value::F64(f64::from_bits(bits)),
                    Const::Bool(v) => Value::Bool(v),
                    Const::Byte(v) => Value::Byte(v),
                    Const::Void => Value::Void,
                    Const::StaticPtr(off) => Value::Ptr(off),
                    Const::Slot(_) => {
                        return self.eval_trap("vm: cell handle constant in a static program");
                    }
                };
                let k = self.const_index(c, value);
                let dest = self.fresh();
                self.code.push(Insn::Const { dest, k });
                self.memo.insert(e, dest);
                dest
            }
            ExprKind::Var(label) => {
                if let Some(&reg) = self.param_reg.get(&label) {
                    reg
                } else if let Some(index) = self.env_index(label) {
                    // A captured variable: read it from the closure's
                    // environment (immutable, so memoizable like any pure
                    // value).
                    let dest = self.fresh();
                    self.code.push(Insn::EnvGet { dest, index });
                    self.memo.insert(e, dest);
                    dest
                } else {
                    return self.eval_trap("vm: variable is not an owned continuation parameter");
                }
            }
            ExprKind::Extract(inner, index) => {
                if let ExprKind::Var(label) = &self.p.expr(inner).kind
                    && *label == self.func
                {
                    if index < self.arity as u32 {
                        index as u16
                    } else {
                        return self
                            .eval_trap("vm: return continuation used as a value (M9 territory)");
                    }
                } else if let ExprKind::Tuple(items) = &self.p.expr(inner).kind {
                    let item = items[index as usize];
                    self.eval(item)?
                } else {
                    // Runtime tuple (an inout ret pair in a continuation
                    // parameter, say).
                    let src = self.eval(inner)?;
                    let dest = self.fresh();
                    self.code.push(Insn::Extract {
                        dest,
                        src,
                        index: index as u16,
                    });
                    self.memo.insert(e, dest);
                    dest
                }
            }
            // A function value: build a flat closure over the target
            // chunk's captured labels (env layout from `env_of` — the same
            // order the chunk's own EnvGet reads use).
            ExprKind::Func(label) => {
                if !self.chunk_of.contains_key(&label) {
                    return self.eval_trap(
                        "vm: continuation used as a value (returnable continuations are M9)",
                    );
                }
                return self.make_closure(label, e);
            }
            ExprKind::Tuple(items) => {
                let mut arg_regs = Vec::with_capacity(items.len());
                for &item in items.iter() {
                    arg_regs.push(self.eval(item)?);
                }
                let args_start = self.module.arg_pool.len() as u32;
                let args_len = arg_regs.len() as u16;
                self.module.arg_pool.extend(arg_regs);
                let dest = self.fresh();
                self.code.push(Insn::TupleNew {
                    dest,
                    args_start,
                    args_len,
                });
                self.memo.insert(e, dest);
                dest
            }
            ExprKind::App(..) => {
                return self.eval_trap("vm: application in value position (lowerer bug)");
            }
            ExprKind::PrimOp(op, args, _) => return self.eval_primop(e, op, &args),
        };
        Ok(reg)
    }

    fn eval_primop(&mut self, e: ExprId, op: Op, args: &[ExprId]) -> Result<u16, String> {
        match op {
            Op::Add | Op::Sub | Op::Mul | Op::Div => {
                let a = self.eval(args[0])?;
                let b = self.eval(args[1])?;
                let dest = self.fresh();
                self.code.push(match op {
                    Op::Add => Insn::Add { dest, a, b },
                    Op::Sub => Insn::Sub { dest, a, b },
                    Op::Mul => Insn::Mul { dest, a, b },
                    _ => Insn::Div { dest, a, b },
                });
                self.memo.insert(e, dest);
                Ok(dest)
            }
            Op::Cmp(cmp) => {
                let a = self.eval(args[0])?;
                let b = self.eval(args[1])?;
                let dest = self.fresh();
                self.code.push(Insn::Cmp {
                    dest,
                    a,
                    b,
                    op: cmp,
                });
                self.memo.insert(e, dest);
                Ok(dest)
            }
            Op::Trunc | Op::IToF => {
                let src = self.eval(args[0])?;
                let dest = self.fresh();
                self.code.push(match op {
                    Op::Trunc => Insn::Trunc { dest, src },
                    _ => Insn::IToF { dest, src },
                });
                self.memo.insert(e, dest);
                Ok(dest)
            }
            // Records are pure values (functional construction/update —
            // the machine sees mutation only through cells), so all three
            // ops value-number like arithmetic.
            Op::RecordNew(symbol) => {
                let mut arg_regs = Vec::with_capacity(args.len());
                for &a in args {
                    arg_regs.push(self.eval(a)?);
                }
                let args_start = self.module.arg_pool.len() as u32;
                let args_len = arg_regs.len() as u16;
                self.module.arg_pool.extend(arg_regs);
                let dest = self.fresh();
                self.code.push(Insn::RecordNew {
                    dest,
                    symbol,
                    args_start,
                    args_len,
                });
                self.memo.insert(e, dest);
                Ok(dest)
            }
            // Variants are pure values exactly like records.
            Op::VariantNew(symbol, tag) => {
                let mut arg_regs = Vec::with_capacity(args.len());
                for &a in args {
                    arg_regs.push(self.eval(a)?);
                }
                let args_start = self.module.arg_pool.len() as u32;
                let args_len = arg_regs.len() as u16;
                self.module.arg_pool.extend(arg_regs);
                let dest = self.fresh();
                self.code.push(Insn::VariantNew {
                    dest,
                    symbol,
                    tag,
                    args_start,
                    args_len,
                });
                self.memo.insert(e, dest);
                Ok(dest)
            }
            Op::GetTag => {
                let src = self.eval(args[0])?;
                let dest = self.fresh();
                self.code.push(Insn::GetTag { dest, src });
                self.memo.insert(e, dest);
                Ok(dest)
            }
            Op::GetPayload(index) => {
                let src = self.eval(args[0])?;
                let dest = self.fresh();
                self.code.push(Insn::GetPayload {
                    dest,
                    src,
                    index: index as u16,
                });
                self.memo.insert(e, dest);
                Ok(dest)
            }
            Op::ExistentialPack(protocol) => {
                let mut arg_regs = Vec::with_capacity(args.len());
                for &a in args {
                    arg_regs.push(self.eval(a)?);
                }
                let args_start = self.module.arg_pool.len() as u32;
                let args_len = arg_regs.len() as u16;
                self.module.arg_pool.extend(arg_regs);
                let dest = self.fresh();
                self.code.push(Insn::ExistentialPack {
                    dest,
                    protocol,
                    args_start,
                    args_len,
                });
                self.memo.insert(e, dest);
                Ok(dest)
            }
            Op::ExistentialWitness(index) => {
                let src = self.eval(args[0])?;
                let dest = self.fresh();
                self.code.push(Insn::ExistentialWitness {
                    dest,
                    src,
                    index: index as u16,
                });
                self.memo.insert(e, dest);
                Ok(dest)
            }
            Op::ExistentialPayload => {
                let src = self.eval(args[0])?;
                let dest = self.fresh();
                self.code.push(Insn::ExistentialPayload { dest, src });
                self.memo.insert(e, dest);
                Ok(dest)
            }
            Op::GetField(index) => {
                let rec = self.eval(args[0])?;
                let dest = self.fresh();
                self.code.push(Insn::GetField {
                    dest,
                    rec,
                    index: index as u16,
                });
                self.memo.insert(e, dest);
                Ok(dest)
            }
            Op::SetField(index) => {
                let rec = self.eval(args[0])?;
                let src = self.eval(args[1])?;
                let dest = self.fresh();
                self.code.push(Insn::SetField {
                    dest,
                    rec,
                    src,
                    index: index as u16,
                });
                self.memo.insert(e, dest);
                Ok(dest)
            }
            // Memory and IO operations are effects: emitted per occurrence,
            // never memoized (the substitution evaluator likewise
            // re-evaluates each occurrence).
            Op::Alloc => {
                let count = self.eval(args[0])?;
                let dest = self.fresh();
                self.code.push(Insn::Alloc { dest, count });
                Ok(dest)
            }
            Op::Free => {
                let ptr = self.eval(args[0])?;
                let dest = self.fresh();
                self.code.push(Insn::Free { dest, ptr });
                Ok(dest)
            }
            Op::Load => {
                let Some(kind) = crate::vm::MemKind::of(self.p.ty_kind(self.p.expr(e).ty)) else {
                    return self.eval_trap("vm: load of a type that cannot live in memory");
                };
                let ptr = self.eval(args[0])?;
                let dest = self.fresh();
                self.code.push(Insn::Load { dest, ptr, kind });
                Ok(dest)
            }
            Op::Store => {
                let value_ty = self.p.expr_ty(args[1]);
                let Some(kind) = crate::vm::MemKind::of(self.p.ty_kind(value_ty)) else {
                    return self.eval_trap("vm: store of a type that cannot live in memory");
                };
                let ptr = self.eval(args[0])?;
                let src = self.eval(args[1])?;
                self.code.push(Insn::Store { ptr, src, kind });
                let k = self.const_index(Const::Void, Value::Void);
                let dest = self.fresh();
                self.code.push(Insn::Const { dest, k });
                Ok(dest)
            }
            Op::Copy => {
                let from = self.eval(args[0])?;
                let to = self.eval(args[1])?;
                let len = self.eval(args[2])?;
                self.code.push(Insn::Copy { from, to, len });
                let k = self.const_index(Const::Void, Value::Void);
                let dest = self.fresh();
                self.code.push(Insn::Const { dest, k });
                Ok(dest)
            }
            // The io dialect: one parametric instruction; operands in
            // IORequest order, unused slots 0.
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
                let io_op = match op {
                    Op::IoRead => IoOp::Read,
                    Op::IoWrite => IoOp::Write,
                    Op::IoOpen => IoOp::Open,
                    Op::IoClose => IoOp::Close,
                    Op::IoSleep => IoOp::Sleep,
                    Op::IoPoll => IoOp::Poll,
                    Op::IoCtl => IoOp::Ctl,
                    Op::IoSocket => IoOp::Socket,
                    Op::IoBind => IoOp::Bind,
                    Op::IoListen => IoOp::Listen,
                    Op::IoConnect => IoOp::Connect,
                    _ => IoOp::Accept,
                };
                let mut operands = [0u16; 3];
                for (slot, &arg) in operands.iter_mut().zip(args.iter()) {
                    *slot = self.eval(arg)?;
                }
                let dest = self.fresh();
                self.code.push(Insn::Io {
                    dest,
                    op: io_op,
                    a: operands[0],
                    b: operands[1],
                    c: operands[2],
                });
                Ok(dest)
            }
            // Cell operations are effects too (the lowerer guarantees
            // single occurrence per block by threading cells through
            // continuations).
            Op::CellNew => {
                let init = self.eval(args[0])?;
                let dest = self.fresh();
                self.code.push(Insn::CellNew { dest, init });
                Ok(dest)
            }
            Op::CellGet => {
                let cell = self.eval(args[0])?;
                let dest = self.fresh();
                self.code.push(Insn::CellGet { dest, cell });
                Ok(dest)
            }
            Op::CellSet => {
                let cell = self.eval(args[0])?;
                let src = self.eval(args[1])?;
                self.code.push(Insn::CellSet { cell, src });
                // Assignment evaluates to Void.
                let k = self.const_index(Const::Void, Value::Void);
                let dest = self.fresh();
                self.code.push(Insn::Const { dest, k });
                Ok(dest)
            }
            other => self.eval_trap(&format!(
                "vm: primop {other:?} not in the M2 dialect (arrives with a later milestone)"
            )),
        }
    }

    /// In value position a hole still needs a register: trap at runtime if
    /// reached, and hand back a fresh (never-written) register so emission
    /// can continue collecting further diagnostics.
    fn eval_trap(&mut self, message: &str) -> Result<u16, String> {
        let trap = self.trap(message.to_string());
        self.code.push(trap);
        Ok(self.fresh())
    }
}
