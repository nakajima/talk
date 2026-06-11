//! Lowering: typed Talk ASTs → λ_G, in continuation-passing style.
//!
//! - **CPS**: every Talk function becomes a λ_G function whose final
//!   parameter is its return continuation (codomain ⊥) — the Thorin
//!   arrangement (Leißa, Köster & Hack, CGO 2015); the SSA↔CPS
//!   correspondence is Kelsey (IR '95) / Appel (SIGPLAN 1998). Calls chain
//!   through materialized continuation functions (a first-order rendering
//!   of the one-pass CPS transform, Danvy & Filinski, *Representing
//!   Control*, 1992 — administrative redexes are left to β-inlining and
//!   the scheduler rather than smart constructors).
//! - **Monomorphization**: a lazy worklist keyed (symbol, substitution θ)
//!   — MLton's whole-program model / rustc's monomorphization collector;
//!   dictionary-free per Jones (PEPM 1994). θ composes the checker's
//!   per-call-site `instantiations` with the current specialization.
//! - **Witness resolution**: `member_resolutions` + the conformance table
//!   resolve protocol calls to witness functions or protocol default
//!   bodies (lowered with Self := the concrete receiver — the
//!   class-default treatment of Wadler & Blott, POPL 1989).
//! - **@_ir splices** become direct-style PrimOps with θ-resolved types.
//! - Effect rows are erased here: they did their checking work upstream.

pub mod lower_tests;

use indexmap::IndexMap;
use rustc_hash::{FxHashMap, FxHashSet};

use crate::ast::{AST, NameResolved};
use crate::compiling::driver::Source;
use crate::lambda_g::expr::{CmpOp, ExprId, Op, TyId, TyKind};
use crate::lambda_g::program::{Label, Program};
use crate::name_resolution::name_resolver::ResolvedNames;
use crate::name_resolution::symbol::Symbol;
use crate::node::Node;
use crate::lambda_g::expr::Const;
use crate::node_kinds::{
    block::Block,
    decl::{Decl, DeclKind},
    expr::{Expr, ExprKind},
    inline_ir_instruction::{InlineIRInstruction, InlineIRInstructionKind, Value as IrValue},
    match_arm::MatchArm,
    pattern::PatternKind,
    stmt::{Stmt, StmtKind},
    type_annotation::{TypeAnnotation, TypeAnnotationKind},
};
use crate::token_kind::TokenKind;
use crate::types::TypeOutput;
use crate::types::ty::Ty as CheckTy;

pub struct LowerUnit<'a> {
    pub asts: &'a IndexMap<Source, AST<NameResolved>>,
    pub types: &'a TypeOutput,
    pub resolved: &'a ResolvedNames,
}

/// θ: rigid type parameters (including a protocol's Self and associated
/// types) → concrete checker types, for the current specialization.
type Theta = FxHashMap<Symbol, CheckTy>;

/// A canonical, hashable form of θ for the worklist key.
type ThetaKey = Vec<(Symbol, CheckTy)>;

fn theta_key(theta: &Theta) -> ThetaKey {
    let mut pairs: Vec<(Symbol, CheckTy)> = theta.iter().map(|(s, t)| (*s, t.clone())).collect();
    pairs.sort_by_key(|(s, _)| *s);
    pairs
}

struct FuncSource<'a> {
    unit: usize,
    params: &'a [crate::node_kinds::parameter::Parameter],
    body: &'a Block,
}

pub struct Lowering<'a> {
    units: Vec<LowerUnit<'a>>,
    entry: usize,
    pub p: Program,
    sources: FxHashMap<Symbol, FuncSource<'a>>,
    /// Requirement symbol → its signature (over Self/assoc params), for
    /// protocol-default specializations.
    requirement_sigs: FxHashMap<Symbol, CheckTy>,
    /// Methods whose body assigns through `self`: their ret continuation
    /// carries `[result, Self]` and the caller writes Self back (mutable
    /// value semantics + inout self — Racordon et al., JOT 2022).
    mutating: FxHashSet<Symbol>,
    /// Interned string-literal bytes → offset in `p.static_mem`.
    statics: FxHashMap<Vec<u8>, u32>,
    /// Constant top-level lets (`public let STDOUT_FD: Int = 0`), inlined
    /// at use sites: symbol → (defining unit, rhs).
    globals: FxHashMap<Symbol, (usize, &'a Expr)>,
    done: FxHashMap<(Symbol, ThetaKey), Label>,
    queue: Vec<(Symbol, Theta, Label)>,
    pub diagnostics: Vec<String>,
    fresh: u32,
}

/// How a Talk symbol is realized in λ_G: a plain value, or a mutable cell
/// (assignment conversion — Kranz et al., ORBIT, 1986; the alternative,
/// rebuilding SSA form for mutables via Braun et al. CC 2013, is the
/// documented upgrade path once an optimizing schedule wants it).
#[derive(Clone, Copy)]
enum Binding {
    Value(ExprId),
    Cell(ExprId),
}

/// What a resolved call prepends before its source arguments: nothing, a
/// receiver expression (instance member calls), or an already-lowered
/// value (the blank record passed to an initializer).
enum Prefix<'e> {
    None,
    Receiver(&'e Expr),
    Value(ExprId),
}

#[derive(Clone)]
struct Ctx {
    unit: usize,
    theta: Theta,
    /// Talk symbol → λ_G binding (params, locals).
    env: FxHashMap<Symbol, Binding>,
    /// The current function's return continuation (a Fn(R, ⊥) value).
    ret_k: ExprId,
    /// The current λ_G function's parameter extracts (for %n in @_ir).
    params: Vec<ExprId>,
    /// Enclosing loops: (header continuation, exit continuation).
    loops: Vec<(ExprId, ExprId)>,
    /// Symbols that must live in cells in this body (assigned-to, or
    /// receivers of mutating-method calls).
    cellable: FxHashSet<Symbol>,
}

pub struct LoweredProgram {
    pub program: Program,
    pub main: Label,
    pub result_ty: TyId,
    /// Labels of chunk-forming ("real") functions: every demanded
    /// specialization plus main. The scheduler treats every other label as
    /// a continuation — a block of its unique referencing chunk (producer
    /// knowledge in lieu of Thorin's structural top-level recovery; Leißa,
    /// Köster & Hack, CGO 2015).
    pub entry_funcs: FxHashSet<Label>,
    pub diagnostics: Vec<String>,
}

pub fn lower_program<'a>(units: Vec<LowerUnit<'a>>, entry: usize) -> LoweredProgram {
    let mut lowering = Lowering {
        units,
        entry,
        p: Program::new(),
        sources: FxHashMap::default(),
        requirement_sigs: FxHashMap::default(),
        mutating: FxHashSet::default(),
        statics: FxHashMap::default(),
        globals: FxHashMap::default(),
        done: FxHashMap::default(),
        queue: vec![],
        diagnostics: vec![],
        fresh: 0,
    };
    lowering.index_sources();
    let (main, result_ty) = lowering.lower_main();
    lowering.drain_queue();
    let mut entry_funcs: FxHashSet<Label> = lowering.done.values().copied().collect();
    entry_funcs.insert(main);
    LoweredProgram {
        program: lowering.p,
        main,
        result_ty,
        entry_funcs,
        diagnostics: lowering.diagnostics,
    }
}

impl<'a> Lowering<'a> {
    // ----- Indexing -------------------------------------------------------

    /// One pass over every unit's ASTs collecting all lowerable bodies:
    /// top-level funcs (lowered to lets by the resolver), struct methods,
    /// extend members (witnesses + inherents), protocol defaults.
    fn index_sources(&mut self) {
        for unit_index in 0..self.units.len() {
            let unit_asts = self.units[unit_index].asts;
            for ast in unit_asts.values() {
                for root in &ast.roots {
                    let Node::Decl(decl) = root else { continue };
                    self.index_decl(unit_index, decl);
                }
            }
            // Requirement signatures for default-body specialization.
            for info in self.units[unit_index].types.catalog.protocols.values() {
                for requirement in info.requirements.values() {
                    self.requirement_sigs
                        .insert(requirement.symbol, requirement.sig.clone());
                }
            }
        }
    }

    fn index_decl(&mut self, unit: usize, decl: &'a Decl) {
        match &decl.kind {
            DeclKind::Let {
                lhs,
                rhs: Some(rhs),
                ..
            } => {
                if let PatternKind::Bind(name) = &lhs.kind
                    && let Ok(symbol) = name.symbol()
                {
                    match &rhs.kind {
                        ExprKind::Func(func) => {
                            self.index_callable(unit, symbol, &func.params, &func.body, false);
                        }
                        _ => {
                            self.globals.insert(symbol, (unit, rhs));
                        }
                    }
                }
            }
            DeclKind::Struct { body, .. } | DeclKind::Protocol { body, .. } => {
                for member in &body.decls {
                    self.index_decl(unit, member);
                }
            }
            DeclKind::Extend { body, .. } => {
                for member in &body.decls {
                    self.index_decl(unit, member);
                }
            }
            DeclKind::Method { func, .. } => {
                if let Ok(symbol) = func.name.symbol() {
                    self.index_callable(unit, symbol, &func.params, &func.body, false);
                }
            }
            DeclKind::Init { name, params, body } => {
                if let Ok(symbol) = name.symbol() {
                    self.index_callable(unit, symbol, params, body, true);
                }
            }
            _ => {}
        }
    }

    fn index_callable(
        &mut self,
        unit: usize,
        symbol: Symbol,
        params: &'a [crate::node_kinds::parameter::Parameter],
        body: &'a Block,
        is_init: bool,
    ) {
        // A method whose `self` is assigned through is inout: ret carries
        // [result, Self]. Initializers are excluded — their self starts
        // blank and is returned as the result instead.
        if !is_init
            && let Some(first) = params.first()
            && first.name.name_str() == "self"
            && let Ok(self_symbol) = first.name.symbol()
            && self.units[unit]
                .resolved
                .mutated_symbols
                .contains(&self_symbol)
        {
            self.mutating.insert(symbol);
        }
        self.sources.insert(symbol, FuncSource { unit, params, body });
    }

    // ----- Worklist (lazy monomorphization) -------------------------------

    /// Demand the specialization of `symbol` at θ; returns its λ_G label.
    fn demand(&mut self, symbol: Symbol, theta: Theta) -> Label {
        let key = (symbol, theta_key(&theta));
        if let Some(&label) = self.done.get(&key) {
            return label;
        }
        let sig = self.signature_of(symbol, &theta);
        let Some(CheckTy::Func(params, ret, _)) = sig else {
            self.diagnostics.push(format!(
                "lowering: no callable signature for {symbol} (not yet supported)"
            ));
            let void = self.p.ty_void();
            let bot = self.p.ty_bot();
            let dead = self.p.func("unsupported", void, bot);
            self.done.insert(key, dead);
            return dead;
        };

        let param_tys: Vec<TyId> = params.iter().map(|t| self.map_ty(t)).collect();
        let ret_ty = self.map_ty(&ret);
        // Inout self: the ret continuation of a mutating method carries
        // [result, Self]; the caller writes Self back.
        let ret_payload = if self.mutating.contains(&symbol) {
            match param_tys.first() {
                Some(&self_ty) => self.p.ty_tuple(&[ret_ty, self_ty]),
                None => ret_ty,
            }
        } else {
            ret_ty
        };
        let bot = self.p.ty_bot();
        let ret_k_ty = self.p.ty_fn(ret_payload, bot);
        let mut dom_items = param_tys;
        dom_items.push(ret_k_ty);
        let dom = self.p.ty_tuple(&dom_items);

        let name = self.spec_name(symbol, &theta);
        let label = self.p.func(&name, dom, bot);
        self.done.insert(key, label);
        self.queue.push((symbol, theta, label));
        label
    }

    fn drain_queue(&mut self) {
        while let Some((symbol, theta, label)) = self.queue.pop() {
            self.lower_function(symbol, theta, label);
        }
    }

    /// The callable signature of a symbol: its scheme's type (top-level
    /// funcs, methods, witnesses) or its protocol requirement signature
    /// (default bodies), θ-substituted.
    fn signature_of(&mut self, symbol: Symbol, theta: &Theta) -> Option<CheckTy> {
        let raw = self
            .units
            .iter()
            .find_map(|u| u.types.schemes.get(&symbol).map(|s| s.ty.clone()))
            .or_else(|| self.requirement_sigs.get(&symbol).cloned())?;
        Some(raw.substitute(theta, &Default::default(), &Default::default()))
    }

    fn spec_name(&mut self, symbol: Symbol, theta: &Theta) -> String {
        self.fresh += 1;
        let base = self
            .units
            .iter()
            .find_map(|u| u.resolved.symbol_names.get(&symbol).cloned())
            .unwrap_or_else(|| format!("{symbol}"));
        if theta.is_empty() {
            base
        } else {
            format!("{base}${}", self.fresh)
        }
    }

    // ----- Function lowering ----------------------------------------------

    fn lower_function(&mut self, symbol: Symbol, theta: Theta, label: Label) {
        let Some(source) = self.sources.get(&symbol) else {
            self.diagnostics.push(format!(
                "lowering: no body found for {symbol} (not yet supported)"
            ));
            return;
        };
        let unit = source.unit;
        let source_params = source.params;
        let source_body = source.body;

        // Symbols that must live in cells: assigned-to (resolver) plus
        // receivers of mutating-method calls (write-back targets).
        let cellable = self.cellable_symbols(unit, source_body);

        let self_var = self.p.var(label);
        let mut env = FxHashMap::default();
        let mut params = Vec::with_capacity(source_params.len());
        let mut mutated_params: Vec<(Symbol, ExprId)> = vec![];
        for (i, param) in source_params.iter().enumerate() {
            let extract = self.p.extract(self_var, i as u32);
            params.push(extract);
            if let Ok(param_symbol) = param.name.symbol() {
                if cellable.contains(&param_symbol) {
                    mutated_params.push((param_symbol, extract));
                } else {
                    env.insert(param_symbol, Binding::Value(extract));
                }
            }
        }
        let ret_k = self.p.extract(self_var, source_params.len() as u32);

        let mut ctx = Ctx {
            unit,
            theta,
            env,
            ret_k,
            params,
            loops: vec![],
            cellable,
        };
        // Mutated parameters are assignment-converted: box each into a cell
        // bound through a continuation before the body runs.
        let mut prologue: Vec<(Symbol, ExprId)> = vec![];
        for (symbol, extract) in mutated_params {
            prologue.push((symbol, extract));
        }
        let is_mutating = self.mutating.contains(&symbol);
        let self_symbol = source_params
            .first()
            .and_then(|param| param.name.symbol().ok());
        let body = self.with_cells(&prologue, &mut ctx, |this, ctx| {
            // Inout self: wrap the ret continuation so every return
            // delivers [result, current Self] (read from self's cell).
            if is_mutating && let Some(self_symbol) = self_symbol {
                let Some(Binding::Cell(self_cell)) = ctx.env.get(&self_symbol).copied() else {
                    this.diagnostics
                        .push("lowering: mutating method without a self cell".into());
                    let ret_k = ctx.ret_k;
                    return this.lower_block(source_body, ctx, ret_k);
                };
                let TyKind::Fn(pair_ty, _) = *this.p.ty_kind(this.p.expr_ty(ctx.ret_k)) else {
                    unreachable!("ret continuation is not a function");
                };
                let TyKind::Tuple(items) = this.p.ty_kind(pair_ty) else {
                    unreachable!("mutating ret payload is not a tuple");
                };
                let result_ty = items[0];
                let self_ty = items[1];
                let bot = this.p.ty_bot();
                let wrap = this.p.func("ret_inout", result_ty, bot);
                let result = this.p.var(wrap);
                let self_now = this.p.primop(Op::CellGet, &[self_cell], self_ty);
                let pair = this.p.tuple(&[result, self_now]);
                let orig_ret = ctx.ret_k;
                let wrap_body = this.p.app(orig_ret, pair);
                this.p.set_body(wrap, wrap_body);
                ctx.ret_k = this.p.func_ref(wrap);
            }
            let ret_k = ctx.ret_k;
            this.lower_block(source_body, ctx, ret_k)
        });
        self.p.set_body(label, body);
    }

    /// Symbols in this body that must be assignment-converted: those the
    /// resolver saw assigned, plus receivers of mutating-method calls
    /// (`c.bump()` writes back into `c`).
    fn cellable_symbols<D: derive_visitor::Drive>(
        &self,
        unit: usize,
        body: &D,
    ) -> FxHashSet<Symbol> {
        use derive_visitor::Visitor;

        #[derive(Visitor)]
        #[visitor(Expr(enter))]
        struct ReceiverScan<'s> {
            resolutions: &'s FxHashMap<crate::node_id::NodeID, crate::types::output::MemberResolution>,
            mutating: &'s FxHashSet<Symbol>,
            found: FxHashSet<Symbol>,
        }
        impl ReceiverScan<'_> {
            fn enter_expr(&mut self, expr: &Expr) {
                let ExprKind::Call { callee, .. } = &expr.kind else {
                    return;
                };
                let ExprKind::Member(Some(receiver), ..) = &callee.kind else {
                    return;
                };
                let ExprKind::Variable(name) = &receiver.kind else {
                    return;
                };
                let Ok(symbol) = name.symbol() else { return };
                let target = match self.resolutions.get(&callee.id) {
                    Some(crate::types::output::MemberResolution::Direct(s)) => *s,
                    Some(crate::types::output::MemberResolution::ViaConformance {
                        witness, ..
                    }) => *witness,
                    None => return,
                };
                if self.mutating.contains(&target) {
                    self.found.insert(symbol);
                }
            }
        }

        let mut scan = ReceiverScan {
            resolutions: &self.units[unit].types.member_resolutions,
            mutating: &self.mutating,
            found: FxHashSet::default(),
        };
        body.drive(&mut scan);
        let mut cellable = scan.found;
        cellable.extend(self.units[unit].resolved.mutated_symbols.iter().copied());
        cellable
    }

    /// Bind each (symbol, initial value) as a fresh cell, threading through
    /// continuations so each cell is created exactly once.
    fn with_cells(
        &mut self,
        bindings: &[(Symbol, ExprId)],
        ctx: &mut Ctx,
        finish: impl FnOnce(&mut Self, &mut Ctx) -> ExprId,
    ) -> ExprId {
        let Some(((symbol, init), rest)) = bindings.split_first() else {
            return finish(self, ctx);
        };
        let init_ty = self.p.expr_ty(*init);
        let cell_ty = self.p.ty_cell(init_ty);
        let bot = self.p.ty_bot();
        let bind = self.p.func("cell", cell_ty, bot);
        let cell_var = self.p.var(bind);
        ctx.env.insert(*symbol, Binding::Cell(cell_var));
        let body = self.with_cells(rest, ctx, finish);
        self.p.set_body(bind, body);
        let bind_ref = self.p.func_ref(bind);
        let cell = self.p.primop(Op::CellNew, &[*init], cell_ty);
        self.p.app(bind_ref, cell)
    }

    // ----- Blocks and statements -------------------------------------------

    /// Lower a block whose VALUE flows to continuation `k` (a Fn(R, ⊥)
    /// expression). A block's value is its final expression; divergent
    /// statements (return) ignore `k`.
    fn lower_block(&mut self, block: &Block, ctx: &Ctx, k: ExprId) -> ExprId {
        self.lower_nodes(&block.body, ctx, k)
    }

    fn lower_nodes(&mut self, nodes: &[Node], ctx: &Ctx, k: ExprId) -> ExprId {
        let Some((first, rest)) = nodes.split_first() else {
            let void = self.p.void();
            return self.p.app(k, void);
        };
        let is_last = rest.is_empty();
        match first {
            Node::Decl(decl) => self.lower_local_decl(decl, rest, ctx, k),
            Node::Expr(expr) if is_last => self.lower_expr(expr, ctx, k),
            Node::Expr(expr) => self.discard_then(expr, rest, ctx, k),
            Node::Stmt(stmt) => self.lower_stmt(stmt, rest, is_last, ctx, k),
            _ => self.lower_nodes(rest, ctx, k),
        }
    }

    fn lower_stmt(
        &mut self,
        stmt: &Stmt,
        rest: &[Node],
        is_last: bool,
        ctx: &Ctx,
        k: ExprId,
    ) -> ExprId {
        match &stmt.kind {
            StmtKind::Expr(expr) if is_last => self.lower_expr(expr, ctx, k),
            StmtKind::Expr(expr) => self.discard_then(expr, rest, ctx, k),
            // A block-final if/else statement is the block's value (the
            // checker's rule; both branches deliver to k).
            StmtKind::If(cond, then_block, Some(else_block)) if is_last => {
                let then_body = self.lower_block(then_block, ctx, k);
                let else_body = self.lower_block(else_block, ctx, k);
                self.branch(cond, then_body, else_body, ctx)
            }
            StmtKind::Return(value) => match value {
                Some(expr) => self.lower_expr(expr, ctx, ctx.ret_k),
                None => {
                    let void = self.p.void();
                    self.p.app(ctx.ret_k, void)
                }
            },
            StmtKind::If(cond, then_block, else_block) => {
                // Statement-position if: both branches continue with the
                // rest of the block through a join continuation.
                let void_ty = self.p.ty_void();
                let bot = self.p.ty_bot();
                let join = self.p.func("join", void_ty, bot);
                let rest_body = if is_last {
                    let void = self.p.void();
                    self.p.app(k, void)
                } else {
                    self.lower_nodes(rest, ctx, k)
                };
                self.p.set_body(join, rest_body);
                let join_ref = self.p.func_ref(join);

                let then_ty = block_value_ty(self, then_block, ctx);
                let then_k = self.discarding_cont(then_ty, join_ref);
                let then_body = self.lower_block(then_block, ctx, then_k);
                let else_body = match else_block {
                    Some(else_block) => {
                        let else_ty = block_value_ty(self, else_block, ctx);
                        let else_k = self.discarding_cont(else_ty, join_ref);
                        self.lower_block(else_block, ctx, else_k)
                    }
                    None => {
                        let void = self.p.void();
                        self.p.app(join_ref, void)
                    }
                };
                self.branch(cond, then_body, else_body, ctx)
            }
            StmtKind::Assignment(lhs, rhs) => {
                // What the new value flows into once evaluated: the cell
                // itself, or a field of the record held in the cell
                // (functional SetField, then store — value semantics).
                let target = self.assignment_target(lhs, ctx);
                let Some((cell, field)) = target else {
                    return self.continue_after(rest, is_last, ctx, k);
                };
                // rhs → set the cell → continue (one effect per step keeps
                // strict left-to-right argument evaluation an ordering).
                let void_ty = self.p.ty_void();
                let bot = self.p.ty_bot();
                let after = self.p.func("after_set", void_ty, bot);
                let after_body = self.continue_after(rest, is_last, ctx, k);
                self.p.set_body(after, after_body);
                let after_ref = self.p.func_ref(after);

                let rhs_ty = self.expr_lambda_ty(rhs, ctx);
                let setter = self.p.func("set", rhs_ty, bot);
                let value = self.p.var(setter);
                let stored = match field {
                    None => value,
                    Some(index) => {
                        let TyKind::Cell(record_ty) =
                            *self.p.ty_kind(self.p.expr_ty(cell))
                        else {
                            unreachable!("assignment target is not a cell");
                        };
                        let current = self.p.primop(Op::CellGet, &[cell], record_ty);
                        self.p
                            .primop(Op::SetField(index), &[current, value], record_ty)
                    }
                };
                let cell_set = self.p.primop(Op::CellSet, &[cell, stored], void_ty);
                let setter_body = self.p.app(after_ref, cell_set);
                self.p.set_body(setter, setter_body);
                let setter_ref = self.p.func_ref(setter);
                self.lower_expr(rhs, ctx, setter_ref)
            }

            StmtKind::Loop(condition, body) => {
                // A loop is a recursive continuation (Appel, Compiling with
                // Continuations): header tests/jumps, body jumps back.
                let void_ty = self.p.ty_void();
                let bot = self.p.ty_bot();
                let header = self.p.func("loop_head", void_ty, bot);
                let exit = self.p.func("loop_exit", void_ty, bot);
                let exit_body = self.continue_after(rest, is_last, ctx, k);
                self.p.set_body(exit, exit_body);
                let header_ref = self.p.func_ref(header);
                let exit_ref = self.p.func_ref(exit);

                let mut loop_ctx = ctx.clone();
                loop_ctx.loops.push((header_ref, exit_ref));
                // The body's value is discarded; its end jumps back to the
                // header.
                let body_value_ty = block_value_ty(self, body, ctx);
                let back = self.discarding_cont(body_value_ty, header_ref);
                let body_expr = self.lower_block(body, &loop_ctx, back);

                let header_body = match condition {
                    Some(condition) => {
                        let exit_jump = {
                            let void = self.p.void();
                            self.p.app(exit_ref, void)
                        };
                        self.branch(condition, body_expr, exit_jump, ctx)
                    }
                    None => body_expr,
                };
                self.p.set_body(header, header_body);
                let void = self.p.void();
                self.p.app(header_ref, void)
            }

            StmtKind::Break => match ctx.loops.last() {
                Some(&(_, exit_ref)) => {
                    let void = self.p.void();
                    self.p.app(exit_ref, void)
                }
                None => {
                    self.diagnostics.push("lowering: break outside loop".into());
                    let void = self.p.void();
                    self.p.app(k, void)
                }
            },
            StmtKind::Continue(_) => match ctx.loops.last() {
                Some(&(header_ref, _)) => {
                    let void = self.p.void();
                    self.p.app(header_ref, void)
                }
                None => {
                    self.diagnostics
                        .push("lowering: continue outside loop".into());
                    let void = self.p.void();
                    self.p.app(k, void)
                }
            },

            other => {
                self.diagnostics
                    .push(format!("lowering: statement not yet supported: {other:?}"));
                let void = self.p.void();
                self.p.app(k, void)
            }
        }
    }

    /// Resolve an assignment lhs to (cell, optional field index): a plain
    /// mutable variable, or `receiver.field` where the receiver is
    /// cell-bound.
    fn assignment_target(&mut self, lhs: &Expr, ctx: &Ctx) -> Option<(ExprId, Option<u32>)> {
        match &lhs.kind {
            ExprKind::Variable(name) => {
                let Some(Binding::Cell(cell)) =
                    name.symbol().ok().and_then(|s| ctx.env.get(&s).copied())
                else {
                    self.diagnostics
                        .push("lowering: assignment to a non-cell binding".into());
                    return None;
                };
                Some((cell, None))
            }
            ExprKind::Member(Some(receiver), label, _) => {
                let ExprKind::Variable(name) = &receiver.kind else {
                    self.diagnostics.push(
                        "lowering: field assignment through a non-variable receiver (not yet supported)"
                            .into(),
                    );
                    return None;
                };
                let Some(Binding::Cell(cell)) =
                    name.symbol().ok().and_then(|s| ctx.env.get(&s).copied())
                else {
                    self.diagnostics
                        .push("lowering: field assignment to a non-cell receiver".into());
                    return None;
                };
                let resolution = self.units[ctx.unit]
                    .types
                    .member_resolutions
                    .get(&lhs.id)
                    .cloned();
                let Some(crate::types::output::MemberResolution::Direct(property)) = resolution
                else {
                    self.diagnostics.push(format!(
                        "lowering: unresolved field '{label}' in assignment"
                    ));
                    return None;
                };
                let head = self.checker_ty(receiver, ctx);
                let Some(index) = self.field_index(&head, property) else {
                    self.diagnostics.push(format!(
                        "lowering: '{label}' is not a stored field of {head:?}"
                    ));
                    return None;
                };
                Some((cell, Some(index)))
            }
            _ => {
                self.diagnostics
                    .push("lowering: assignment target not yet supported".into());
                None
            }
        }
    }

    /// The continuation of a statement: the rest of the block, or k(()).
    fn continue_after(&mut self, rest: &[Node], is_last: bool, ctx: &Ctx, k: ExprId) -> ExprId {
        if is_last {
            let void = self.p.void();
            self.p.app(k, void)
        } else {
            self.lower_nodes(rest, ctx, k)
        }
    }

    fn lower_local_decl(&mut self, decl: &Decl, rest: &[Node], ctx: &Ctx, k: ExprId) -> ExprId {
        let DeclKind::Let { lhs, rhs, .. } = &decl.kind else {
            self.diagnostics
                .push(format!("lowering: declaration not yet supported: {:?}", decl.kind));
            return self.lower_nodes(rest, ctx, k);
        };
        let PatternKind::Bind(name) = &lhs.kind else {
            self.diagnostics
                .push("lowering: destructuring let not yet supported".to_string());
            return self.lower_nodes(rest, ctx, k);
        };
        let Some(rhs) = rhs else {
            return self.lower_nodes(rest, ctx, k);
        };
        let Ok(symbol) = name.symbol() else {
            return self.lower_nodes(rest, ctx, k);
        };

        // Bind the value through a continuation function; the rest of the
        // block is its body (sharing IS the let). Mutated locals are
        // assignment-converted into cells (ORBIT); write-back receivers of
        // mutating methods count as mutated.
        let mutated = ctx.cellable.contains(&symbol);
        let value_ty = self.expr_lambda_ty(rhs, ctx);
        let bot = self.p.ty_bot();
        let bind = self.p.func(&format!("let_{}", name.name_str()), value_ty, bot);
        let bound = self.p.var(bind);
        let mut inner = ctx.clone();
        let rest_body = if mutated {
            self.with_cells(&[(symbol, bound)], &mut inner, |this, inner| {
                this.lower_nodes(rest, inner, k)
            })
        } else {
            inner.env.insert(symbol, Binding::Value(bound));
            self.lower_nodes(rest, &inner, k)
        };
        self.p.set_body(bind, rest_body);
        let bind_ref = self.p.func_ref(bind);
        self.lower_expr(rhs, ctx, bind_ref)
    }

    fn discard_then(&mut self, expr: &Expr, rest: &[Node], ctx: &Ctx, k: ExprId) -> ExprId {
        // Pure path first: the drop continuation's domain must match the
        // VALUE delivered, and an unconstrained statement expression (a
        // bare @_ir, say) types more precisely in λ_G than in the
        // checker's residue.
        let (value_ty, pure_value) = match self.try_pure(expr, ctx) {
            Some(value) => (self.p.expr_ty(value), Some(value)),
            None => (self.expr_lambda_ty(expr, ctx), None),
        };
        let bot = self.p.ty_bot();
        let drop_k = self.p.func("drop", value_ty, bot);
        let rest_body = self.lower_nodes(rest, ctx, k);
        self.p.set_body(drop_k, rest_body);
        let drop_ref = self.p.func_ref(drop_k);
        match pure_value {
            Some(value) => self.p.app(drop_ref, value),
            None => self.lower_expr(expr, ctx, drop_ref),
        }
    }

    /// A continuation that discards its value and jumps to `target` with ().
    fn discarding_cont(&mut self, value_ty: TyId, target: ExprId) -> ExprId {
        let bot = self.p.ty_bot();
        let cont = self.p.func("discard", value_ty, bot);
        let void = self.p.void();
        let body = self.p.app(target, void);
        self.p.set_body(cont, body);
        self.p.func_ref(cont)
    }

    // ----- Expressions ------------------------------------------------------

    /// Lower `expr`, delivering its value to continuation `k : Fn(T, ⊥)`.
    fn lower_expr(&mut self, expr: &Expr, ctx: &Ctx, k: ExprId) -> ExprId {
        if let Some(value) = self.try_pure(expr, ctx) {
            return self.p.app(k, value);
        }
        match &expr.kind {
            ExprKind::Call {
                callee,
                args,
                trailing_block,
                ..
            } => {
                if trailing_block.is_some() {
                    self.diagnostics
                        .push("lowering: trailing blocks not yet supported".into());
                }
                self.lower_call(expr, callee, args, ctx, k)
            }
            ExprKind::If(cond, then_block, else_block) => {
                let then_body = self.lower_block(then_block, ctx, k);
                let else_body = self.lower_block(else_block, ctx, k);
                self.branch(cond, then_body, else_body, ctx)
            }
            ExprKind::Block(block) => self.lower_block(block, ctx, k),
            // A parenthesized expression parses as a 1-tuple.
            ExprKind::Tuple(items) if items.len() == 1 => self.lower_expr(&items[0], ctx, k),
            // Field read on an impure receiver: bind the receiver through
            // a continuation, then GetField.
            ExprKind::Member(Some(receiver), label, _) => {
                let receiver_ty = self.expr_lambda_ty(receiver, ctx);
                let bot = self.p.ty_bot();
                let cont = self.p.func("recv", receiver_ty, bot);
                let receiver_value = self.p.var(cont);
                let body = match self.field_read(expr, receiver, receiver_value, ctx) {
                    Some(field) => self.p.app(k, field),
                    None => {
                        self.diagnostics.push(format!(
                            "lowering: member '{label}' is not a stored field (not yet supported)"
                        ));
                        let void = self.p.void();
                        self.p.app(k, void)
                    }
                };
                self.p.set_body(cont, body);
                let cont_ref = self.p.func_ref(cont);
                self.lower_expr(receiver, ctx, cont_ref)
            }
            ExprKind::Match(scrutinee, arms) => self.lower_match(scrutinee, arms, ctx, k),
            other => {
                self.diagnostics
                    .push(format!("lowering: expression not yet supported: {other:?}"));
                let void = self.p.void();
                self.p.app(k, void)
            }
        }
    }

    // ----- Match -------------------------------------------------------------

    /// Literal/wildcard/bind match as a comparison chain (the degenerate
    /// single-column case of Maranget's decision trees, ML 2008; the full
    /// compiler arrives with enums in M4). Arms test in source order.
    fn lower_match(
        &mut self,
        scrutinee: &Expr,
        arms: &[MatchArm],
        ctx: &Ctx,
        k: ExprId,
    ) -> ExprId {
        match self.try_pure(scrutinee, ctx) {
            Some(value) => self.lower_match_arms(value, arms, ctx, k),
            None => {
                let scrutinee_ty = self.expr_lambda_ty(scrutinee, ctx);
                let bot = self.p.ty_bot();
                let cont = self.p.func("scrut", scrutinee_ty, bot);
                let value = self.p.var(cont);
                let body = self.lower_match_arms(value, arms, ctx, k);
                self.p.set_body(cont, body);
                let cont_ref = self.p.func_ref(cont);
                self.lower_expr(scrutinee, ctx, cont_ref)
            }
        }
    }

    fn lower_match_arms(
        &mut self,
        value: ExprId,
        arms: &[MatchArm],
        ctx: &Ctx,
        k: ExprId,
    ) -> ExprId {
        let Some((arm, rest)) = arms.split_first() else {
            // The checker accepted this match, so an unmatched value is a
            // checker/lowerer disagreement; deliver Void rather than a
            // wrong arm.
            self.diagnostics
                .push("lowering: non-exhaustive match reached lowering".into());
            let void = self.p.void();
            return self.p.app(k, void);
        };
        match &arm.pattern.kind {
            PatternKind::Wildcard => self.lower_block(&arm.body, ctx, k),
            PatternKind::Bind(name) => {
                let mut inner = ctx.clone();
                if let Ok(symbol) = name.symbol() {
                    inner.env.insert(symbol, Binding::Value(value));
                }
                self.lower_block(&arm.body, &inner, k)
            }
            PatternKind::LiteralInt(text) => {
                let Some(literal) = text.parse().ok().map(|v| self.p.int(v)) else {
                    self.diagnostics
                        .push("lowering: unparseable int literal pattern".into());
                    let void = self.p.void();
                    return self.p.app(k, void);
                };
                let cond = self.p.cmp(CmpOp::Eq, value, literal);
                let then_body = self.lower_block(&arm.body, ctx, k);
                let else_body = self.lower_match_arms(value, rest, ctx, k);
                self.branch_value(cond, then_body, else_body)
            }
            PatternKind::LiteralTrue | PatternKind::LiteralFalse => {
                let literal = self
                    .p
                    .bool(matches!(arm.pattern.kind, PatternKind::LiteralTrue));
                let cond = self.p.cmp(CmpOp::Eq, value, literal);
                let then_body = self.lower_block(&arm.body, ctx, k);
                let else_body = self.lower_match_arms(value, rest, ctx, k);
                self.branch_value(cond, then_body, else_body)
            }
            other => {
                self.diagnostics.push(format!(
                    "lowering: pattern not yet supported (arrives with M4): {other:?}"
                ));
                let void = self.p.void();
                self.p.app(k, void)
            }
        }
    }

    /// Pure expressions evaluate without continuations: literals, bound
    /// variables, field reads on pure receivers, and @_ir splices over
    /// pure operands.
    fn try_pure(&mut self, expr: &Expr, ctx: &Ctx) -> Option<ExprId> {
        match &expr.kind {
            ExprKind::LiteralInt(text) => Some(self.p.int(text.parse().ok()?)),
            ExprKind::LiteralFloat(text) => Some(self.p.float(text.parse().ok()?)),
            ExprKind::LiteralTrue => Some(self.p.bool(true)),
            ExprKind::LiteralFalse => Some(self.p.bool(false)),
            // A string literal is a String record over interned static
            // bytes: {base, length, capacity}.
            ExprKind::LiteralString(text) => {
                let bytes = crate::parsing::lexing::unescape(text).into_bytes();
                let offset = self.intern_static(&bytes);
                let CheckTy::Nominal(string_symbol, _) = self.checker_ty(expr, ctx) else {
                    self.diagnostics
                        .push("lowering: string literal with a non-nominal type".into());
                    return None;
                };
                let ptr_ty = self.p.ty_ptr();
                let base = self.p.constant(Const::StaticPtr(offset), ptr_ty);
                let len = self.p.int(bytes.len() as i64);
                let ty = self.p.ty(TyKind::Boxed(string_symbol));
                Some(self.p.primop(Op::RecordNew(string_symbol), &[base, len, len], ty))
            }
            // Field read on a pure receiver: GetField (records are pure
            // values).
            ExprKind::Member(Some(receiver), _, _) => {
                let receiver_value = self.try_pure(receiver, ctx)?;
                self.field_read(expr, receiver, receiver_value, ctx)
            }
            ExprKind::Variable(name) => {
                let symbol = name.symbol().ok()?;
                if let Some(&binding) = ctx.env.get(&symbol) {
                    return Some(match binding {
                        Binding::Value(value) => value,
                        Binding::Cell(cell) => {
                            let TyKind::Cell(inner) = *self.p.ty_kind(self.p.expr_ty(cell)) else {
                                return None;
                            };
                            self.p.primop(Op::CellGet, &[cell], inner)
                        }
                    });
                }
                // A function-typed global used as a value: demand its
                // specialization (instantiation recorded at this node).
                if self.sources.contains_key(&symbol) {
                    let theta = self.instantiation_at(expr.id, ctx);
                    let label = self.demand(symbol, theta);
                    return Some(self.p.func_ref(label));
                }
                // A constant global (`public let STDOUT_FD: Int = 0`):
                // inline its literal value (whole-program constant
                // propagation; non-literal globals await M8 statics).
                if let Some(&(unit, rhs)) = self.globals.get(&symbol) {
                    let global_ctx = Ctx {
                        unit,
                        theta: Theta::default(),
                        env: FxHashMap::default(),
                        ret_k: ctx.ret_k,
                        params: vec![],
                        loops: vec![],
                        cellable: FxHashSet::default(),
                    };
                    return self.try_pure(rhs, &global_ctx);
                }
                None
            }
            // The unit literal `()`.
            ExprKind::Tuple(items) if items.is_empty() => Some(self.p.void()),
            ExprKind::InlineIR(instruction) => self.splice(instruction, ctx),
            ExprKind::Tuple(items) if items.len() == 1 => self.try_pure(&items[0], ctx),
            _ => None,
        }
    }

    /// Branch on a condition expression: br(cond, then_thunk, else_thunk)
    /// (the paper's br_⊥, §2.2).
    fn branch(&mut self, cond: &Expr, then_body: ExprId, else_body: ExprId, ctx: &Ctx) -> ExprId {
        // The condition itself may need CPS (e.g. `n <= 1` is a call).
        match self.try_pure(cond, ctx) {
            Some(cv) => self.branch_value(cv, then_body, else_body),
            None => {
                let bot = self.p.ty_bot();
                let bool_ty = self.p.ty_bool();
                let ck = self.p.func("cond", bool_ty, bot);
                let cv = self.p.var(ck);
                let body = self.branch_value(cv, then_body, else_body);
                self.p.set_body(ck, body);
                let ck_ref = self.p.func_ref(ck);
                self.lower_expr(cond, ctx, ck_ref)
            }
        }
    }

    /// br over an already-lowered condition value.
    fn branch_value(&mut self, cond: ExprId, then_body: ExprId, else_body: ExprId) -> ExprId {
        let void_ty = self.p.ty_void();
        let bot = self.p.ty_bot();
        let then_fn = self.p.func("then", void_ty, bot);
        self.p.set_body(then_fn, then_body);
        let else_fn = self.p.func("else", void_ty, bot);
        self.p.set_body(else_fn, else_body);
        let then_ref = self.p.func_ref(then_fn);
        let else_ref = self.p.func_ref(else_fn);
        let thunk_ty = self.p.ty_fn(void_ty, bot);
        self.p.br(cond, then_ref, else_ref, thunk_ty)
    }

    // ----- Records -----------------------------------------------------------

    /// GetField for a member read: through member_resolutions when the
    /// checker saw the node, else by name against the receiver's record
    /// type (@_ir binds are trusted, not inferred, so they carry no
    /// resolutions).
    fn field_read(
        &mut self,
        expr: &Expr,
        receiver: &Expr,
        receiver_value: ExprId,
        ctx: &Ctx,
    ) -> Option<ExprId> {
        let resolution = self.units[ctx.unit]
            .types
            .member_resolutions
            .get(&expr.id)
            .cloned();
        if let Some(crate::types::output::MemberResolution::Direct(property)) = resolution {
            let head = self.checker_ty(receiver, ctx);
            let index = self.field_index(&head, property)?;
            let field_check_ty = self.checker_ty(expr, ctx);
            let field_ty = self.map_ty(&field_check_ty);
            return Some(
                self.p
                    .primop(Op::GetField(index), &[receiver_value], field_ty),
            );
        }

        let ExprKind::Member(_, label, _) = &expr.kind else {
            return None;
        };
        let TyKind::Boxed(record_symbol) = *self.p.ty_kind(self.p.expr_ty(receiver_value)) else {
            return None;
        };
        let info = self
            .units
            .iter()
            .find_map(|u| u.types.catalog.structs.get(&record_symbol))?;
        let (index, field_ty) = info
            .fields
            .iter()
            .enumerate()
            .find(|(_, (name, _))| *name == &label.to_string())
            .map(|(i, (_, (_, ty)))| (i as u32, ty.clone()))?;
        let field_ty = self.map_ty(&field_ty);
        Some(
            self.p
                .primop(Op::GetField(index), &[receiver_value], field_ty),
        )
    }

    /// The position of `property` in the head struct's declared field
    /// order (the record layout).
    fn field_index(&mut self, head: &CheckTy, property: Symbol) -> Option<u32> {
        let CheckTy::Nominal(head_symbol, _) = head else {
            return None;
        };
        let info = self
            .units
            .iter()
            .find_map(|u| u.types.catalog.structs.get(head_symbol))?;
        info.fields
            .values()
            .position(|(symbol, _)| *symbol == property)
            .map(|i| i as u32)
    }

    /// Intern string-literal bytes into static memory (deduplicated).
    fn intern_static(&mut self, bytes: &[u8]) -> u32 {
        if let Some(&offset) = self.statics.get(bytes) {
            return offset;
        }
        let offset = self.p.static_mem.len() as u32;
        self.p.static_mem.extend_from_slice(bytes);
        self.statics.insert(bytes.to_vec(), offset);
        offset
    }

    // ----- Calls -----------------------------------------------------------

    fn lower_call(
        &mut self,
        expr: &Expr,
        callee: &Expr,
        args: &[crate::node_kinds::call_arg::CallArg],
        ctx: &Ctx,
        k: ExprId,
    ) -> ExprId {
        // Resolve the target specialization.
        let target = self.resolve_callee(expr, callee, args, ctx);
        let Some((label, symbol, prefix)) = target else {
            let void = self.p.void();
            return self.p.app(k, void);
        };

        let mut arg_exprs: Vec<&Expr> = vec![];
        let mut done: Vec<ExprId> = vec![];
        match prefix {
            Prefix::None => {}
            Prefix::Receiver(receiver) => arg_exprs.push(receiver),
            Prefix::Value(value) => done.push(value),
        }
        arg_exprs.extend(args.iter().map(|a| &a.value));

        // Inout self: the callee's ret carries [result, Self]; write Self
        // back into the receiver's cell, then deliver the result to k.
        let k = if self.mutating.contains(&symbol) {
            match self.writeback_cont(&prefix, label, ctx, k) {
                Some(adapter) => adapter,
                None => {
                    self.diagnostics.push(
                        "lowering: mutating method on a non-writable receiver (not yet supported)"
                            .into(),
                    );
                    k
                }
            }
        } else {
            k
        };

        let func_ref = self.p.func_ref(label);
        self.lower_args(&arg_exprs, ctx, done, &mut |this, values| {
            let mut tuple_items = values;
            tuple_items.push(k);
            let arg_tuple = this.p.tuple(&tuple_items);
            this.p.app(func_ref, arg_tuple)
        })
    }

    /// The write-back adapter for a mutating-method call: receives
    /// [result, Self], stores Self into the receiver's cell, passes the
    /// result on (the "caller performs the write-back" half of inout —
    /// Racordon et al., JOT 2022).
    fn writeback_cont(
        &mut self,
        prefix: &Prefix<'_>,
        label: Label,
        ctx: &Ctx,
        k: ExprId,
    ) -> Option<ExprId> {
        let Prefix::Receiver(receiver) = prefix else {
            return None;
        };
        let ExprKind::Variable(name) = &receiver.kind else {
            return None;
        };
        let symbol = name.symbol().ok()?;
        let Some(Binding::Cell(cell)) = ctx.env.get(&symbol).copied() else {
            return None;
        };

        // The pair type comes from the demanded function's signature.
        let TyKind::Tuple(dom_items) = self.p.ty_kind(self.p.dom(label)) else {
            return None;
        };
        let ret_k_ty = *dom_items.last()?;
        let TyKind::Fn(pair_ty, _) = *self.p.ty_kind(ret_k_ty) else {
            return None;
        };

        let bot = self.p.ty_bot();
        let void_ty = self.p.ty_void();
        let unpack = self.p.func("writeback", pair_ty, bot);
        let pair = self.p.var(unpack);
        let result = self.p.extract(pair, 0);
        let new_self = self.p.extract(pair, 1);

        let after = self.p.func("after_writeback", void_ty, bot);
        let after_body = self.p.app(k, result);
        self.p.set_body(after, after_body);
        let after_ref = self.p.func_ref(after);

        let cell_set = self.p.primop(Op::CellSet, &[cell, new_self], void_ty);
        let unpack_body = self.p.app(after_ref, cell_set);
        self.p.set_body(unpack, unpack_body);
        Some(self.p.func_ref(unpack))
    }

    /// Sequentially lower argument expressions, chaining continuations for
    /// the impure ones; `finish` receives the value expressions.
    fn lower_args(
        &mut self,
        exprs: &[&Expr],
        ctx: &Ctx,
        mut done: Vec<ExprId>,
        finish: &mut dyn FnMut(&mut Self, Vec<ExprId>) -> ExprId,
    ) -> ExprId {
        let Some((first, rest)) = exprs.split_first() else {
            return finish(self, done);
        };
        if let Some(value) = self.try_pure(first, ctx) {
            done.push(value);
            return self.lower_args(rest, ctx, done, finish);
        }
        let value_ty = self.expr_lambda_ty(first, ctx);
        let bot = self.p.ty_bot();
        let arg_k = self.p.func("arg", value_ty, bot);
        let value = self.p.var(arg_k);
        done.push(value);
        let rest_owned: Vec<&Expr> = rest.to_vec();
        let body = self.lower_args(&rest_owned, ctx, done, finish);
        self.p.set_body(arg_k, body);
        let arg_ref = self.p.func_ref(arg_k);
        self.lower_expr(first, ctx, arg_ref)
    }

    /// Resolve a callee to a demanded specialization label. Returns the
    /// label plus an optional receiver to prepend (instance member calls).
    fn resolve_callee<'e>(
        &mut self,
        expr: &Expr,
        callee: &'e Expr,
        args: &[crate::node_kinds::call_arg::CallArg],
        ctx: &Ctx,
    ) -> Option<(Label, Symbol, Prefix<'e>)> {
        match &callee.kind {
            ExprKind::Variable(name) => {
                let symbol = name.symbol().ok()?;
                if ctx.env.contains_key(&symbol) {
                    self.diagnostics
                        .push("lowering: calling local function values not yet supported".into());
                    return None;
                }
                let theta = self.call_theta(symbol, callee.id, ctx);
                Some((self.demand(symbol, theta), symbol, Prefix::None))
            }
            // `Person(args…)`: construction is a call to the (explicit or
            // memberwise-synthesized) initializer with a blank record as
            // self; the init body fills the fields and returns self.
            ExprKind::Constructor(name) => {
                let struct_symbol = name.symbol().ok()?;
                let resolution = self.units[ctx.unit]
                    .types
                    .member_resolutions
                    .get(&callee.id)
                    .cloned();
                let Some(crate::types::output::MemberResolution::Direct(init)) = resolution else {
                    self.diagnostics.push(format!(
                        "lowering: unresolved initializer for {struct_symbol}"
                    ));
                    return None;
                };
                let blank = self.blank_record(struct_symbol)?;
                let theta = self.call_theta(init, expr.id, ctx);
                Some((self.demand(init, theta), init, Prefix::Value(blank)))
            }
            // Protocol-static (operators) or instance member calls: resolve
            // through member_resolutions + the conformance table.
            ExprKind::Member(receiver, label, _) => {
                let resolution = self.units[ctx.unit]
                    .types
                    .member_resolutions
                    .get(&callee.id)
                    .cloned();
                let receiver_expr: Option<&'e Expr> = match receiver {
                    Some(r) if !matches!(r.kind, ExprKind::Constructor(_)) => Some(r.as_ref()),
                    _ => None,
                };
                let prefix = match receiver_expr {
                    Some(r) => Prefix::Receiver(r),
                    None => Prefix::None,
                };
                // The dispatch head: the (θ-substituted) type of the first
                // value argument (receiver for instance calls; lhs for
                // operator protocol-static calls).
                let head_expr = receiver_expr.or_else(|| args.first().map(|a| &a.value));
                let head_ty = head_expr.map(|h| self.checker_ty(h, ctx));
                match resolution {
                    Some(crate::types::output::MemberResolution::ViaConformance {
                        protocol,
                        witness,
                    }) => {
                        let head_ty = head_ty?;
                        let (target, target_symbol) =
                            self.resolve_witness(protocol, witness, label.to_string(), &head_ty)?;
                        Some((target, target_symbol, prefix))
                    }
                    Some(crate::types::output::MemberResolution::Direct(member)) => {
                        let theta = self.call_theta(member, callee.id, ctx);
                        Some((self.demand(member, theta), member, prefix))
                    }
                    None => {
                        self.diagnostics.push(format!(
                            "lowering: unresolved member call '{label}' at {:?}",
                            expr.id
                        ));
                        None
                    }
                }
            }
            other => {
                self.diagnostics
                    .push(format!("lowering: callee not yet supported: {other:?}"));
                None
            }
        }
    }

    /// A blank record for `struct_symbol`: every field Void until the init
    /// body assigns it (Void poison keeps a partial init honest at
    /// runtime).
    fn blank_record(&mut self, struct_symbol: Symbol) -> Option<ExprId> {
        let field_count = self
            .units
            .iter()
            .find_map(|u| u.types.catalog.structs.get(&struct_symbol))
            .map(|info| info.fields.len())?;
        let void = self.p.void();
        let fields = vec![void; field_count];
        let ty = self.p.ty(TyKind::Boxed(struct_symbol));
        Some(self.p.primop(Op::RecordNew(struct_symbol), &fields, ty))
    }

    /// Witness selection (Wadler & Blott's instance method lookup, made
    /// static by monomorphization): a concrete head + protocol picks the
    /// conformance row; its witness function, or the protocol default body
    /// specialized at Self := head.
    fn resolve_witness(
        &mut self,
        protocol: Symbol,
        requirement_or_witness: Symbol,
        label: String,
        head: &CheckTy,
    ) -> Option<(Label, Symbol)> {
        let CheckTy::Nominal(head_symbol, _head_args) = head else {
            self.diagnostics.push(format!(
                "lowering: protocol dispatch on non-nominal head {head:?} (not yet supported)"
            ));
            return None;
        };
        let catalog = &self.units[self.entry].types.catalog;
        let conformance = catalog.conformances.get(&(*head_symbol, protocol)).cloned();

        if let Some(conformance) = conformance {
            if let Some(&witness) = conformance.witnesses.get(&label) {
                return Some((self.demand(witness, Theta::default()), witness));
            }
            // Default body: specialize at Self := head, with the
            // conformance's associated bindings.
            let mut theta = Theta::default();
            theta.insert(protocol, head.clone());
            for (assoc, ty) in &conformance.assoc {
                theta.insert(*assoc, ty.clone());
            }
            return Some((
                self.demand(requirement_or_witness, theta),
                requirement_or_witness,
            ));
        }
        self.diagnostics.push(format!(
            "lowering: no conformance ({head_symbol}, {protocol}) for '{label}'"
        ));
        None
    }

    // ----- @_ir splices ------------------------------------------------------

    /// Map an inline-IR instruction to a PrimOp: `$n` → lowered bind
    /// expressions, `%n` → the enclosing function's parameters, literals
    /// pass through; the type argument is θ-resolved.
    fn splice(&mut self, instruction: &InlineIRInstruction, ctx: &Ctx) -> Option<ExprId> {
        let mut binds = Vec::with_capacity(instruction.binds.len());
        for (i, bind) in instruction.binds.iter().enumerate() {
            let Some(value) = self.try_pure(bind, ctx) else {
                self.diagnostics.push(format!(
                    "lowering: @_ir bind ${i} is not a pure expression: {:?}",
                    bind.kind
                ));
                return None;
            };
            binds.push(value);
        }
        let operand = |this: &mut Self, v: &IrValue| -> Option<ExprId> {
            match v {
                IrValue::Bind(i) => binds.get(*i).copied(),
                IrValue::Reg(n) => ctx.params.get(*n as usize).copied(),
                IrValue::Int(i) => Some(this.p.int(*i)),
                IrValue::Float(f) => Some(this.p.float(*f)),
                IrValue::Bool(b) => Some(this.p.bool(*b)),
                IrValue::Void => Some(this.p.void()),
                _ => None,
            }
        };
        use InlineIRInstructionKind as K;
        let (op, operands): (Op, Vec<ExprId>) = match &instruction.kind {
            K::Add { a, b, .. } => (Op::Add, vec![operand(self, a)?, operand(self, b)?]),
            K::Sub { a, b, .. } => (Op::Sub, vec![operand(self, a)?, operand(self, b)?]),
            K::Mul { a, b, .. } => (Op::Mul, vec![operand(self, a)?, operand(self, b)?]),
            K::Div { a, b, .. } => (Op::Div, vec![operand(self, a)?, operand(self, b)?]),
            K::Cmp { lhs, rhs, op, .. } => {
                let cmp = match op {
                    TokenKind::EqualsEquals => CmpOp::Eq,
                    TokenKind::BangEquals => CmpOp::Ne,
                    TokenKind::Less => CmpOp::Lt,
                    TokenKind::LessEquals => CmpOp::Le,
                    TokenKind::Greater => CmpOp::Gt,
                    TokenKind::GreaterEquals => CmpOp::Ge,
                    _ => return None,
                };
                (Op::Cmp(cmp), vec![operand(self, lhs)?, operand(self, rhs)?])
            }
            K::Trunc { val, .. } => (Op::Trunc, vec![operand(self, val)?]),
            K::IntToFloat { val, .. } => (Op::IToF, vec![operand(self, val)?]),
            K::Alloc { ty, count, .. } => {
                // `alloc T count`: count elements of T. Only byte-sized
                // elements exist until Array (M5) makes `_alloc` generic.
                let element = self.splice_ty(ty, ctx)?;
                if !matches!(self.p.ty_kind(element), TyKind::Byte) {
                    self.diagnostics.push(
                        "lowering: non-byte alloc element (arrives with M5 Array)".into(),
                    );
                    return None;
                }
                (Op::Alloc, vec![operand(self, count)?])
            }
            K::Load { ty, addr, .. } => {
                let result = self.splice_ty(ty, ctx)?;
                let ptr = operand(self, addr)?;
                return Some(self.p.primop(Op::Load, &[ptr], result));
            }
            K::Copy {
                from, to, length, ..
            } => (
                Op::Copy,
                vec![
                    operand(self, from)?,
                    operand(self, to)?,
                    operand(self, length)?,
                ],
            ),
            K::IoWrite { fd, buf, count, .. } => (
                Op::IoWrite,
                vec![
                    operand(self, fd)?,
                    operand(self, buf)?,
                    operand(self, count)?,
                ],
            ),
            other => {
                self.diagnostics.push(format!(
                    "lowering: @_ir instruction not yet supported: {other:?}"
                ));
                return None;
            }
        };
        let result_ty = match op {
            Op::Cmp(_) => self.p.ty_bool(),
            Op::Trunc => self.p.ty_i64(),
            Op::IToF => self.p.ty_f64(),
            Op::Alloc => self.p.ty_ptr(),
            Op::Copy => self.p.ty_void(),
            Op::IoWrite => self.p.ty_i64(),
            _ => self.p.expr_ty(operands[0]),
        };
        Some(self.p.primop(op, &operands, result_ty))
    }

    /// The λ_G type named by a splice's type argument, θ-resolved (`load
    /// Element` inside a Byte specialization is a byte load).
    fn splice_ty(&mut self, annotation: &TypeAnnotation, ctx: &Ctx) -> Option<TyId> {
        let TypeAnnotationKind::Nominal { name, .. } = &annotation.kind else {
            self.diagnostics
                .push("lowering: unsupported @_ir type argument".into());
            return None;
        };
        let symbol = name.symbol().ok()?;
        if let Some(bound) = ctx.theta.get(&symbol) {
            let bound = bound.clone();
            return Some(self.map_ty(&bound));
        }
        Some(self.map_ty(&CheckTy::Nominal(symbol, vec![])))
    }

    // ----- Types and θ -------------------------------------------------------

    /// The checker type of an expression node, θ-substituted.
    fn checker_ty(&self, expr: &Expr, ctx: &Ctx) -> CheckTy {
        let raw = self.units[ctx.unit]
            .types
            .node_types
            .get(&expr.id)
            .cloned()
            .unwrap_or(CheckTy::Error);
        raw.substitute(&ctx.theta, &Default::default(), &Default::default())
    }

    fn expr_lambda_ty(&mut self, expr: &Expr, ctx: &Ctx) -> TyId {
        let ty = self.checker_ty(expr, ctx);
        self.map_ty(&ty)
    }

    /// The full θ for a call to `symbol`: per-call-site instantiation
    /// composed with the enclosing θ; scheme params with no recorded
    /// instantiation (monomorphic recursion typed against the group's
    /// skeleton — THIH §11.6.3) inherit the enclosing specialization's
    /// binding.
    fn call_theta(&self, symbol: Symbol, node: crate::node_id::NodeID, ctx: &Ctx) -> Theta {
        let mut theta = self.instantiation_at(node, ctx);
        if let Some(scheme) = self
            .units
            .iter()
            .find_map(|u| u.types.schemes.get(&symbol))
        {
            for param in &scheme.params {
                if !theta.contains_key(&param.symbol)
                    && let Some(ty) = ctx.theta.get(&param.symbol)
                {
                    theta.insert(param.symbol, ty.clone());
                }
            }
        }
        theta
    }

    /// The per-call-site instantiation, composed with the enclosing θ
    /// (`instantiations ∘ θ` — the worklist's edge label).
    fn instantiation_at(&self, node: crate::node_id::NodeID, ctx: &Ctx) -> Theta {
        let mut theta = Theta::default();
        if let Some(pairs) = self.units[ctx.unit].types.instantiations.get(&node) {
            for (symbol, ty) in pairs {
                let ty = ty.substitute(&ctx.theta, &Default::default(), &Default::default());
                theta.insert(*symbol, ty);
            }
        }
        theta
    }

    /// Checker type → λ_G type. Function types become their CPS form:
    /// (T…) → R turns into Fn([T…, Fn(R, ⊥)], ⊥).
    fn map_ty(&mut self, ty: &CheckTy) -> TyId {
        match ty {
            CheckTy::Nominal(symbol, _args) => {
                if *symbol == Symbol::Int {
                    self.p.ty_i64()
                } else if *symbol == Symbol::Float {
                    self.p.ty_f64()
                } else if *symbol == Symbol::Bool {
                    self.p.ty_bool()
                } else if *symbol == Symbol::Void {
                    self.p.ty_void()
                } else if *symbol == Symbol::Never {
                    self.p.ty_bot()
                } else if *symbol == Symbol::RawPtr {
                    self.p.ty_ptr()
                } else if *symbol == Symbol::Byte {
                    self.p.ty(TyKind::Byte)
                } else {
                    // Structs/enums/String arrive in M3+.
                    self.p.ty(TyKind::Boxed(*symbol))
                }
            }
            CheckTy::Func(params, ret, _eff) => {
                let mut dom_items: Vec<TyId> = params.iter().map(|t| self.map_ty(t)).collect();
                let ret_ty = self.map_ty(ret);
                let bot = self.p.ty_bot();
                let ret_k = self.p.ty_fn(ret_ty, bot);
                dom_items.push(ret_k);
                let dom = self.p.ty_tuple(&dom_items);
                self.p.ty_fn(dom, bot)
            }
            CheckTy::Tuple(items) => {
                let mapped: Vec<TyId> = items.iter().map(|t| self.map_ty(t)).collect();
                self.p.ty_tuple(&mapped)
            }
            // A residual solver variable on an error-free program is
            // unconstrained — its instantiation cannot matter, so default
            // it (the ambiguity-defaulting move; statement-position @_ir
            // results are the common case).
            CheckTy::Var(_) => self.p.ty_void(),
            other => {
                self.diagnostics
                    .push(format!("lowering: type not yet supported: {other:?}"));
                self.p.ty_void()
            }
        }
    }

    // ----- Entry point -------------------------------------------------------

    /// The synthetic `main`: top-level statements of the entry unit in
    /// source order; its return continuation receives the value of the
    /// final top-level expression (the program/REPL value).
    fn lower_main(&mut self) -> (Label, TyId) {
        let unit = self.entry;
        let mut nodes: Vec<Node> = vec![];
        for ast in self.units[unit].asts.values() {
            for root in &ast.roots {
                match root {
                    Node::Stmt(_) => nodes.push(root.clone()),
                    Node::Decl(decl) => {
                        // Non-func top-level lets execute in main, in order.
                        if let DeclKind::Let { rhs: Some(rhs), .. } = &decl.kind
                            && !matches!(rhs.kind, ExprKind::Func(_))
                        {
                            nodes.push(root.clone());
                        }
                    }
                    _ => {}
                }
            }
        }

        // The program value type: the final top-level expression's type.
        let result_check_ty = nodes
            .iter()
            .rev()
            .find_map(|node| match node {
                Node::Stmt(Stmt {
                    kind: StmtKind::Expr(expr),
                    ..
                }) => self.units[unit].types.node_types.get(&expr.id).cloned(),
                // A final if/else statement is valued (the checker's
                // block-final rule): its type is its branch value's.
                Node::Stmt(Stmt {
                    kind: StmtKind::If(_, then_block, Some(_)),
                    ..
                }) => then_block.body.iter().rev().find_map(|n| match n {
                    Node::Stmt(Stmt {
                        kind: StmtKind::Expr(e),
                        ..
                    })
                    | Node::Expr(e) => {
                        self.units[unit].types.node_types.get(&e.id).cloned()
                    }
                    _ => None,
                }),
                _ => None,
            })
            .unwrap_or(CheckTy::Nominal(Symbol::Void, vec![]));
        let result_ty = self.map_ty(&result_check_ty);

        let bot = self.p.ty_bot();
        let ret_k_ty = self.p.ty_fn(result_ty, bot);
        let dom = self.p.ty_tuple(&[ret_k_ty]);
        let main = self.p.func("main", dom, bot);
        let main_var = self.p.var(main);
        let ret_k = self.p.extract(main_var, 0);

        // Receivers of mutating-method calls at the top level need cells
        // too (the let-binding consults ctx.cellable).
        let mut cellable: FxHashSet<Symbol> = FxHashSet::default();
        cellable.extend(self.units[unit].resolved.mutated_symbols.iter().copied());
        for node in &nodes {
            cellable.extend(self.cellable_symbols(unit, node));
        }

        let ctx = Ctx {
            unit,
            theta: Theta::default(),
            env: FxHashMap::default(),
            ret_k,
            params: vec![],
            loops: vec![],
            cellable,
        };
        let body = self.lower_main_nodes(&nodes, &ctx, ret_k);
        self.p.set_body(main, body);
        (main, result_ty)
    }

    /// Like lower_nodes, but the final expression's value goes to ret_k.
    fn lower_main_nodes(&mut self, nodes: &[Node], ctx: &Ctx, k: ExprId) -> ExprId {
        self.lower_nodes(nodes, ctx, k)
    }
}

/// The λ_G type of a block's value, from the checker's view of its final
/// expression (Void when the block ends in a non-expression).
fn block_value_ty(lowering: &mut Lowering, block: &Block, ctx: &Ctx) -> TyId {
    let last_expr = block.body.iter().rev().find_map(|node| match node {
        Node::Stmt(Stmt {
            kind: StmtKind::Expr(e),
            ..
        }) => Some(e),
        Node::Expr(e) => Some(e),
        _ => None,
    });
    match last_expr {
        Some(e) => lowering.expr_lambda_ty(e, ctx),
        None => lowering.p.ty_void(),
    }
}
