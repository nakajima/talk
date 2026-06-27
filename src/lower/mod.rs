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

mod derive;
pub mod lower_tests;
mod mir_lowering;
mod patterns;
mod statements;

use indexmap::IndexMap;
use rustc_hash::{FxHashMap, FxHashSet};

use crate::ast::{AST, NameResolved};
use crate::compiling::driver::Source;
use crate::lambda_g::expr::Const;
use crate::lambda_g::expr::{CmpOp, ExprId, Op, TyId, TyKind};
use crate::lambda_g::program::{Label, Program};
use crate::mir;
use crate::name_resolution::name_resolver::ResolvedNames;
use crate::name_resolution::symbol::Symbol;
use crate::node::Node;
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
use crate::ownership::{KeyPath as OwnershipKeyPath, OwnershipOutput};
use crate::token_kind::TokenKind;
use crate::types::TypeOutput;
use crate::types::ty::Ty as CheckTy;
use crate::types::ty::TyFold;

pub struct LowerUnit<'a> {
    pub asts: &'a IndexMap<Source, AST<NameResolved>>,
    pub types: &'a TypeOutput,
    pub resolved: &'a ResolvedNames,
    pub ownership: &'a OwnershipOutput,
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
    /// Function values (literals, trailing blocks): they are called
    /// indirectly, so the scheduler gives each its own chunk and closure
    /// environment (unknown occurrences — the closure-conversion criterion
    /// of flat closures, Cardelli 1984).
    escaping: FxHashSet<Label>,
    /// Functions whose bodies (transitively, through direct calls) perform
    /// an effect routed to a lexical handler: symbol → the handler symbols
    /// they can abort to. Their specializations take an extra explicit
    /// normal-return continuation parameter, reserving the machine-return
    /// slot for abort propagation (capability-passing CPS for lexical
    /// handlers — Schuster, Brachthäuser & Ostermann, ICFP 2020; Schuster
    /// et al., PLDI 2022).
    abortable: FxHashMap<Symbol, Vec<Symbol>>,
    /// Installed handlers: handler symbol → its capability closure and
    /// the value type its scope's Ret chain carries.
    handler_caps: FxHashMap<Symbol, HandlerCap>,
    /// Cells of mutable top-level bindings: functions that read or assign
    /// them reference the cell directly (a free variable of main; the
    /// closure machinery carries it, exactly like handler capabilities).
    top_level_cells: FxHashMap<Symbol, ExprId>,
    pub diagnostics: Vec<String>,
}

/// A lowered `@handle`: the capability closure performs call into, and the
/// value type the handled scope's Ret chain carries (what the capability
/// ultimately delivers — abort as unwinding, Hillerström, Lindley, Atkey &
/// Sivaramakrishnan, FSCD 2017 §4.5).
#[derive(Clone, Copy)]
struct HandlerCap {
    cap: ExprId,
    scope_result_ty: TyId,
    /// For a resuming handler (effect return ≠ Never): the domain of
    /// the resumption closure the perform passes — `[effect return,
    /// slot]`. None for abort handlers.
    resume_pair_ty: Option<TyId>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(super) struct EvidenceBinding {
    protocol: Symbol,
    table: ExprId,
}

/// How a Talk symbol is realized in λ_G: a plain value, or a mutable cell
/// (assignment conversion — Kranz et al., ORBIT, 1986; the alternative,
/// rebuilding SSA form for mutables via Braun et al. CC 2013, is the
/// documented upgrade path once an optimizing schedule wants it).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
enum Binding {
    Value(ExprId),
    Cell(ExprId),
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct DropBinding {
    symbol: Symbol,
    key_path: OwnershipKeyPath,
    ty: CheckTy,
    dynamic_flags: Vec<OwnershipKeyPath>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
struct LoopBinding {
    header: ExprId,
    exit: ExprId,
    drop_depth: usize,
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
    owner: Option<Symbol>,
    theta: Theta,
    /// Talk symbol → λ_G binding (params, locals).
    env: FxHashMap<Symbol, Binding>,
    /// GADT-local evidence: hidden type parameter + protocol bound →
    /// runtime witness table extracted from the constructor payload.
    local_evidence: FxHashMap<(Symbol, Symbol), EvidenceBinding>,
    /// The current function's return continuation (a Fn(R, ⊥) value).
    ret_k: ExprId,
    /// The continuation currently representing normal fallthrough to the
    /// function tail. This may be a drop wrapper around `ret_k`.
    tail_k: ExprId,
    /// The current λ_G function's own machine-return slot, untouched by
    /// the init/inout/normal-return wrappers layered onto `ret_k`. Routed
    /// performs and calls that can abort pass it as the callee's return
    /// linkage, so an abort propagates back as a plain Ret chain running
    /// no user code in between (capability-passing CPS — Schuster et al.,
    /// PLDI 2022).
    raw_ret_k: ExprId,
    /// In an abort-capable function: the explicit normal-return
    /// continuation parameter. Results go here (paired with the return
    /// slot); the machine return itself is reserved for aborts.
    normal_k: Option<ExprId>,
    /// Whether a routed perform may lower here: true in main, in
    /// abort-capable specializations, and in the handler/rest closures
    /// they spawn; false inside plain function values, whose call sites
    /// cannot thread the abort linkage.
    abort_ok: bool,
    /// Inside a resuming handler's capability closure: its resumption
    /// parameter. `continue v` tail-transfers into it. Cleared in
    /// nested function values (they cannot resume).
    resume_k: Option<ExprId>,
    /// Lowering main's top-level statements: cellable lets register in
    /// `top_level_cells` so functions can capture them.
    top_level: bool,
    /// Handlers installed within the current function context: performs
    /// routed to them never escape this frame, so they are safe even in
    /// plain-shaped functions. Cleared in function values.
    local_handlers: FxHashSet<Symbol>,
    /// The current λ_G function's parameter extracts (for %n in @_ir).
    params: Vec<ExprId>,
    /// Enclosing loops with the drop-stack depth active at loop entry.
    loops: Vec<LoopBinding>,
    /// Owned locals currently in scope. Normal scope exits drop only the
    /// locals introduced by that scope; early exits wrap their continuation
    /// with the active suffix recorded here.
    drop_stack: Vec<DropBinding>,
    /// Runtime initializedness flags for owned locals whose drop obligation
    /// is path-sensitive (`Conditional`/`Open` in the MIR drop plan).
    drop_flags: FxHashMap<OwnershipKeyPath, ExprId>,
    /// During an initializer, assignments through this self root fill
    /// uninitialized storage rather than replacing a live value.
    initializing_self: Option<Symbol>,
    /// Symbols that must live in cells in this body (assigned-to, or
    /// receivers of mutating-method calls).
    cellable: FxHashSet<Symbol>,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct MirCtxKey {
    unit: usize,
    owner: Option<Symbol>,
    theta: ThetaKey,
    env: Vec<(Symbol, Binding)>,
    local_evidence: Vec<((Symbol, Symbol), EvidenceBinding)>,
    ret_k: ExprId,
    tail_k: ExprId,
    raw_ret_k: ExprId,
    normal_k: Option<ExprId>,
    abort_ok: bool,
    resume_k: Option<ExprId>,
    top_level: bool,
    local_handlers: Vec<Symbol>,
    params: Vec<ExprId>,
    loops: Vec<LoopBinding>,
    drop_stack: Vec<DropBinding>,
    drop_flags: Vec<(OwnershipKeyPath, ExprId)>,
    initializing_self: Option<Symbol>,
    cellable: Vec<Symbol>,
}

/// An active loop in the MIR→λ_G lowering: the header/exit MIR blocks paired
/// with the λ_G continuations a back-edge or break jumps to.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
struct MirLoop {
    header_block: mir::BlockId,
    header: ExprId,
    exit_block: mir::BlockId,
    exit: ExprId,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct MirBlockKey {
    block: mir::BlockId,
    k: ExprId,
    ctx: MirCtxKey,
    loops: Vec<MirLoop>,
}

#[derive(Default)]
struct MirBlockCache {
    blocks: FxHashMap<MirBlockKey, ExprId>,
}

impl Ctx {
    fn mir_key(&self) -> MirCtxKey {
        let mut env: Vec<_> = self
            .env
            .iter()
            .map(|(symbol, binding)| (*symbol, *binding))
            .collect();
        env.sort_by_key(|(symbol, _)| *symbol);
        let mut local_evidence: Vec<_> = self
            .local_evidence
            .iter()
            .map(|(key, evidence)| (*key, *evidence))
            .collect();
        local_evidence.sort_by_key(|((ty, protocol), _)| (*ty, *protocol));
        let mut local_handlers: Vec<_> = self.local_handlers.iter().copied().collect();
        local_handlers.sort();
        let mut drop_flags: Vec<_> = self
            .drop_flags
            .iter()
            .map(|(key_path, flag)| (key_path.clone(), *flag))
            .collect();
        drop_flags.sort_by_key(|(key_path, _)| format!("{key_path:?}"));
        let mut cellable: Vec<_> = self.cellable.iter().copied().collect();
        cellable.sort();

        MirCtxKey {
            unit: self.unit,
            owner: self.owner,
            theta: theta_key(&self.theta),
            env,
            local_evidence,
            ret_k: self.ret_k,
            tail_k: self.tail_k,
            raw_ret_k: self.raw_ret_k,
            normal_k: self.normal_k,
            abort_ok: self.abort_ok,
            resume_k: self.resume_k,
            top_level: self.top_level,
            local_handlers,
            params: self.params.clone(),
            loops: self.loops.clone(),
            drop_stack: self.drop_stack.clone(),
            drop_flags,
            initializing_self: self.initializing_self,
            cellable,
        }
    }
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
        escaping: FxHashSet::default(),
        abortable: FxHashMap::default(),
        handler_caps: FxHashMap::default(),
        top_level_cells: FxHashMap::default(),
        diagnostics: vec![],
    };
    for unit in &lowering.units {
        for (symbol, name) in &unit.resolved.symbol_names {
            lowering.p.symbol_names.insert(*symbol, name.clone());
        }
        for (symbol, name) in &unit.types.display_names {
            lowering.p.symbol_names.insert(*symbol, name.clone());
        }
    }
    lowering.index_sources();
    lowering.collect_abortable();
    lowering.diagnose_unsupported_handlers();
    let (main, result_ty) = lowering.lower_main();
    lowering.drain_queue();
    let mut entry_funcs: FxHashSet<Label> = lowering.done.values().copied().collect();
    entry_funcs.extend(lowering.escaping.iter().copied());
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
            DeclKind::Struct { body, .. }
            | DeclKind::Enum { body, .. }
            | DeclKind::Protocol { body, .. } => {
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
        // A `mut func` is internally `self: &mut Self`, which uses the
        // inout calling convention: ret carries [result, Self] and the
        // caller writes Self back. Initializers are excluded because their
        // self starts blank and is returned as the result instead.
        if !is_init && params.first().is_some_and(Self::is_mutable_self_param) {
            self.mutating.insert(symbol);
        }
        self.sources
            .insert(symbol, FuncSource { unit, params, body });
    }

    fn is_mutable_self_param(param: &crate::node_kinds::parameter::Parameter) -> bool {
        param.name.name_str() == "self"
            && matches!(
                param
                    .type_annotation
                    .as_ref()
                    .map(|annotation| &annotation.kind),
                Some(TypeAnnotationKind::Borrow { mutable: true, .. })
            )
    }

    // ----- Abort-capable functions (lexical effect handlers) --------------

    /// The transitive closure of the checker's capability tables: a
    /// binder is abort-capable if its body performs into a lexical
    /// handler (`performs_into`) or references an abort-capable binder
    /// (`binder_refs`) — its callers must thread the abort linkage (see
    /// `Ctx::raw_ret_k`). The reference edges are a conservative
    /// superset of calls; a spurious mark only costs a function the
    /// abort-capable calling convention, never correctness.
    fn collect_abortable(&mut self) {
        // A handler defined inside the binder itself contains its aborts:
        // they never escape the function, so neither the binder nor its
        // callers need the abort-capable convention for them.
        let mut contained: FxHashMap<Symbol, FxHashSet<Symbol>> = FxHashMap::default();
        for unit in &self.units {
            for (&binder, handlers) in &unit.types.handlers_defined {
                contained.entry(binder).or_default().extend(handlers);
            }
        }
        let escapes =
            |binder: Symbol, handler: Symbol, contained: &FxHashMap<Symbol, FxHashSet<Symbol>>| {
                !contained
                    .get(&binder)
                    .is_some_and(|defined| defined.contains(&handler))
            };

        let mut reached: FxHashMap<Symbol, Vec<Symbol>> = FxHashMap::default();
        for unit in &self.units {
            for (&binder, handlers) in &unit.types.performs_into {
                let owned = reached.entry(binder).or_default();
                for &handler in handlers {
                    if escapes(binder, handler, &contained) && !owned.contains(&handler) {
                        owned.push(handler);
                    }
                }
            }
        }
        loop {
            let mut changed = false;
            for unit in &self.units {
                for (&binder, refs) in &unit.types.binder_refs {
                    for target in refs {
                        let Some(handlers) = reached.get(target).cloned() else {
                            continue;
                        };
                        let owned = reached.entry(binder).or_default();
                        for handler in handlers {
                            if escapes(binder, handler, &contained) && !owned.contains(&handler) {
                                owned.push(handler);
                                changed = true;
                            }
                        }
                    }
                }
            }
            if !changed {
                break;
            }
        }
        reached.retain(|_, handlers| !handlers.is_empty());
        // Deterministic handler order (abort_scope_ty takes the first).
        for handlers in reached.values_mut() {
            handlers.sort();
        }
        self.abortable = reached;
    }

    fn diagnose_unsupported_handlers(&mut self) {
        for unit_index in 0..self.units.len() {
            let asts = self.units[unit_index].asts;
            for ast in asts.values() {
                for root in &ast.roots {
                    self.diagnose_unsupported_handlers_in_node(unit_index, root);
                }
            }
        }
    }

    fn diagnose_unsupported_handlers_in_node(&mut self, unit: usize, node: &Node) {
        match node {
            Node::Stmt(stmt) => self.diagnose_unsupported_handlers_in_stmt(unit, stmt),
            Node::Decl(decl) => match &decl.kind {
                DeclKind::Let { rhs: Some(rhs), .. } => {
                    self.diagnose_unsupported_handlers_in_expr(unit, rhs);
                }
                DeclKind::Struct { body, .. }
                | DeclKind::Enum { body, .. }
                | DeclKind::Protocol { body, .. }
                | DeclKind::Extend { body, .. } => {
                    for decl in &body.decls {
                        self.diagnose_unsupported_handlers_in_node(unit, &Node::Decl(decl.clone()));
                    }
                }
                DeclKind::Method { func, .. } => {
                    self.diagnose_unsupported_handlers_in_block(unit, &func.body);
                }
                DeclKind::Init { body, .. } => {
                    self.diagnose_unsupported_handlers_in_block(unit, body);
                }
                _ => {}
            },
            Node::Expr(expr) => self.diagnose_unsupported_handlers_in_expr(unit, expr),
            Node::Block(block) => self.diagnose_unsupported_handlers_in_block(unit, block),
            _ => {}
        }
    }

    fn diagnose_unsupported_handlers_in_block(&mut self, unit: usize, block: &Block) {
        for node in &block.body {
            self.diagnose_unsupported_handlers_in_node(unit, node);
        }
    }

    fn diagnose_unsupported_handlers_in_stmt(&mut self, unit: usize, stmt: &Stmt) {
        match &stmt.kind {
            StmtKind::Handling {
                effect_name, body, ..
            } => {
                if let Some(symbol) = effect_name.symbol().ok()
                    && self.units[unit]
                        .types
                        .catalog
                        .effects
                        .get(&symbol)
                        .is_some_and(|sig| !sig.generics.is_empty())
                {
                    self.diagnostics
                        .push("lowering: handlers for generic effects (not yet supported)".into());
                }
                self.diagnose_unsupported_handlers_in_block(unit, body);
            }
            StmtKind::Expr(expr)
            | StmtKind::Return(Some(expr))
            | StmtKind::Continue(Some(expr)) => {
                self.diagnose_unsupported_handlers_in_expr(unit, expr);
            }
            StmtKind::If(_, then_block, else_block) => {
                self.diagnose_unsupported_handlers_in_block(unit, then_block);
                if let Some(else_block) = else_block {
                    self.diagnose_unsupported_handlers_in_block(unit, else_block);
                }
            }
            StmtKind::Assignment(lhs, rhs) => {
                self.diagnose_unsupported_handlers_in_expr(unit, lhs);
                self.diagnose_unsupported_handlers_in_expr(unit, rhs);
            }
            StmtKind::Loop(condition, body) => {
                if let Some(condition) = condition {
                    self.diagnose_unsupported_handlers_in_expr(unit, condition);
                }
                self.diagnose_unsupported_handlers_in_block(unit, body);
            }
            StmtKind::For { iterable, body, .. } => {
                self.diagnose_unsupported_handlers_in_expr(unit, iterable);
                self.diagnose_unsupported_handlers_in_block(unit, body);
            }
            StmtKind::Return(None) | StmtKind::Break | StmtKind::Continue(None) => {}
        }
    }

    fn diagnose_unsupported_handlers_in_expr(&mut self, unit: usize, expr: &Expr) {
        match &expr.kind {
            ExprKind::Block(block) => self.diagnose_unsupported_handlers_in_block(unit, block),
            ExprKind::If(condition, then_block, else_block) => {
                self.diagnose_unsupported_handlers_in_expr(unit, condition);
                self.diagnose_unsupported_handlers_in_block(unit, then_block);
                self.diagnose_unsupported_handlers_in_block(unit, else_block);
            }
            ExprKind::Match(scrutinee, arms) => {
                self.diagnose_unsupported_handlers_in_expr(unit, scrutinee);
                for arm in arms {
                    self.diagnose_unsupported_handlers_in_block(unit, &arm.body);
                }
            }
            ExprKind::Tuple(items) | ExprKind::LiteralArray(items) => {
                for item in items {
                    self.diagnose_unsupported_handlers_in_expr(unit, item);
                }
            }
            ExprKind::Unary(_, inner) | ExprKind::As(inner, _) => {
                self.diagnose_unsupported_handlers_in_expr(unit, inner);
            }
            ExprKind::Binary(lhs, _, rhs) => {
                self.diagnose_unsupported_handlers_in_expr(unit, lhs);
                self.diagnose_unsupported_handlers_in_expr(unit, rhs);
            }
            ExprKind::Call {
                callee,
                args,
                trailing_block,
                ..
            } => {
                self.diagnose_unsupported_handlers_in_expr(unit, callee);
                for arg in args {
                    self.diagnose_unsupported_handlers_in_expr(unit, &arg.value);
                }
                if let Some(block) = trailing_block {
                    self.diagnose_unsupported_handlers_in_block(unit, block);
                }
            }
            ExprKind::CallEffect { args, .. } => {
                for arg in args {
                    self.diagnose_unsupported_handlers_in_expr(unit, &arg.value);
                }
            }
            ExprKind::Member(Some(receiver), ..) => {
                self.diagnose_unsupported_handlers_in_expr(unit, receiver);
            }
            ExprKind::Func(func) => self.diagnose_unsupported_handlers_in_block(unit, &func.body),
            ExprKind::RecordLiteral { fields, spread } => {
                if let Some(spread) = spread {
                    self.diagnose_unsupported_handlers_in_expr(unit, spread);
                }
                for field in fields {
                    self.diagnose_unsupported_handlers_in_expr(unit, &field.value);
                }
            }
            _ => {}
        }
    }

    /// Does this symbol's specialization take the abort-capable shape
    /// (normal-return continuation parameter + return slot reserved for
    /// aborts)? Inits and inout methods are excluded for now — their ret
    /// wrappers and the abort linkage have not been reconciled.
    fn abort_shape(&self, symbol: Symbol) -> bool {
        self.abortable.contains_key(&symbol)
            && !self.is_init(symbol)
            && !self.mutating.contains(&symbol)
    }

    // ----- Worklist (lazy monomorphization) -------------------------------

    /// Demand the specialization of `symbol` at θ; returns its λ_G label.
    fn demand(&mut self, symbol: Symbol, theta: Theta) -> Label {
        let key = (symbol, theta_key(&theta));
        if let Some(&label) = self.done.get(&key) {
            return label;
        }
        let sig = self.signature_of(symbol, &theta);
        let Some(CheckTy::Func(params, mut ret, _)) = sig else {
            self.diagnostics.push(format!(
                "lowering: no callable signature for {symbol} (not yet supported)"
            ));
            let void = self.p.ty_void();
            let bot = self.p.ty_bot();
            let dead = self.p.func("unsupported", void, bot);
            self.done.insert(key, dead);
            return dead;
        };

        // An init returns self whatever its body's final value is
        // (construction semantics — the checker types `Person(...)` as the
        // struct; the inferred body value may be Void).
        if self.is_init(symbol)
            && let Some(self_ty) = params.first()
        {
            *ret = self_ty.clone();
        }
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
        let mut dom_items = param_tys;
        if self.abort_shape(symbol) {
            // The abort-capable shape: …params, normal-return continuation
            // (taking [result, return slot]), then the return slot itself,
            // reserved for abort propagation (capability-passing CPS —
            // Schuster et al., PLDI 2022).
            let scope_ty = self.abort_scope_ty(symbol, ret_payload);
            let slot_ty = self.p.ty_fn(scope_ty, bot);
            let pair_ty = self.p.ty_tuple(&[ret_payload, slot_ty]);
            dom_items.push(self.p.ty_fn(pair_ty, bot));
            dom_items.push(slot_ty);
        } else {
            if self.abortable.contains_key(&symbol) {
                self.diagnostics.push(format!(
                    "lowering: {symbol} is an init or inout method that can abort (not yet supported)"
                ));
            }
            dom_items.push(self.p.ty_fn(ret_payload, bot));
        }
        let dom = self.p.ty_tuple(&dom_items);

        let name = self.spec_name(symbol, &theta);
        let label = self.p.func(&name, dom, bot);
        self.done.insert(key, label);
        self.queue.push((symbol, theta, label));
        label
    }

    /// The value type an abort-capable function's Ret chain carries: the
    /// result type of the scope owning the handler its performs route to.
    /// Falls back to the function's own result type (with a diagnostic)
    /// when the handler is unknown — the program is already rejected.
    fn abort_scope_ty(&mut self, symbol: Symbol, fallback: TyId) -> TyId {
        let handlers = self.abortable.get(&symbol).cloned().unwrap_or_default();
        if handlers.len() > 1 {
            self.diagnostics.push(format!(
                "lowering: {symbol} performs into more than one handler (not yet supported)"
            ));
        }
        let Some(cap) = handlers.first().and_then(|h| self.handler_caps.get(h)) else {
            self.diagnostics.push(format!(
                "lowering: {symbol} can abort but is demanded before its handler is installed (not yet supported)"
            ));
            return fallback;
        };
        cap.scope_result_ty
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

    /// A specialization's display name: the source name plus the concrete
    /// types it was specialized at (`id<Int>`), in a stable order.
    fn spec_name(&mut self, symbol: Symbol, theta: &Theta) -> String {
        let base = self
            .units
            .iter()
            .find_map(|u| u.resolved.symbol_names.get(&symbol).cloned())
            .unwrap_or_else(|| format!("{symbol}"));
        if theta.is_empty() {
            return base;
        }
        let mut args: Vec<(String, String)> = theta
            .iter()
            .map(|(param, ty)| (format!("{param:?}"), ty.render_mono()))
            .collect();
        args.sort();
        let rendered: Vec<String> = args.into_iter().map(|(_, ty)| ty).collect();
        format!("{base}<{}>", rendered.join(", "))
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
        let mut param_names: Vec<String> =
            source_params.iter().map(|p| p.name.name_str()).collect();
        param_names.push("k".into());
        if self.abort_shape(symbol) {
            param_names.push("slot".into());
        }
        let name_refs: Vec<&str> = param_names.iter().map(String::as_str).collect();
        self.p.name_params(label, &name_refs);

        let mut ctx = Ctx {
            unit,
            owner: Some(symbol),
            theta,
            env,
            local_evidence: FxHashMap::default(),
            ret_k,
            tail_k: ret_k,
            raw_ret_k: ret_k,
            normal_k: None,
            abort_ok: false,
            resume_k: None,
            top_level: false,
            local_handlers: FxHashSet::default(),
            params,
            loops: vec![],
            drop_stack: vec![],
            drop_flags: FxHashMap::default(),
            initializing_self: None,
            cellable,
        };
        // Abort-capable shape: results pair with our own return slot and
        // go to the explicit normal-return continuation; the machine
        // return is reserved for abort propagation (see Ctx::raw_ret_k).
        if self.abort_shape(symbol) {
            let normal_k = ret_k;
            let slot = self.p.extract(self_var, (source_params.len() + 1) as u32);
            let result_ty = self.normal_result_ty(normal_k);
            let bot = self.p.ty_bot();
            let wrap = self.p.func("ret_normal", result_ty, bot);
            let value = self.p.var(wrap);
            let pair = self.p.tuple(&[value, slot]);
            let wrap_body = self.p.app(normal_k, pair);
            self.p.set_body(wrap, wrap_body);
            ctx.ret_k = self.p.func_ref(wrap);
            ctx.tail_k = ctx.ret_k;
            ctx.raw_ret_k = slot;
            ctx.normal_k = Some(normal_k);
            ctx.abort_ok = true;
        }
        // Mutated parameters are assignment-converted: box each into a cell
        // bound through a continuation before the body runs.
        let mut prologue: Vec<(Symbol, ExprId)> = vec![];
        for (symbol, extract) in mutated_params {
            prologue.push((symbol, extract));
        }
        let is_mutating = self.mutating.contains(&symbol);
        let is_init = self.is_init(symbol);
        let self_symbol = source_params
            .first()
            .and_then(|param| param.name.symbol().ok());
        if is_init {
            ctx.initializing_self = self_symbol;
        }
        let body = self.with_cells(&prologue, &mut ctx, |this, ctx| {
            // Construction semantics: an init's caller receives self, not
            // the body's final value — wrap the ret continuation to drop
            // the value and deliver self's current state.
            if is_init && let Some(self_symbol) = self_symbol {
                let self_now = match ctx.env.get(&self_symbol).copied() {
                    Some(Binding::Cell(cell)) => match *this.p.ty_kind(this.p.expr_ty(cell)) {
                        TyKind::Cell(inner) => this.p.primop(Op::CellGet, &[cell], inner),
                        _ => {
                            this.diagnostics
                                .push("lowering: init self cell without a cell type".into());
                            this.p.void()
                        }
                    },
                    Some(Binding::Value(value)) => value,
                    None => {
                        this.diagnostics
                            .push("lowering: init without a self binding".into());
                        this.p.void()
                    }
                };
                let body_value_ty = block_value_ty(this, source_body, ctx);
                let bot = this.p.ty_bot();
                let wrap = this.p.func("init_ret", body_value_ty, bot);
                let orig_ret = ctx.ret_k;
                let wrap_body = this.p.app(orig_ret, self_now);
                this.p.set_body(wrap, wrap_body);
                ctx.ret_k = this.p.func_ref(wrap);
                ctx.tail_k = ctx.ret_k;
            }
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
                ctx.tail_k = ctx.ret_k;
            }
            let ret_k = ctx.ret_k;
            this.lower_block(source_body, ctx, ret_k)
        });
        self.p.set_body(label, body);
    }

    /// Symbols in this body that must be assignment-converted: those the
    /// resolver saw assigned, plus roots of mutating-method receivers
    /// (`c.bump()` and `person.name.bump()` both write back through `c` /
    /// `person`).
    fn cellable_symbols<D: derive_visitor::Drive>(
        &self,
        unit: usize,
        body: &D,
    ) -> FxHashSet<Symbol> {
        use derive_visitor::Visitor;

        #[derive(Visitor)]
        #[visitor(Expr(enter))]
        struct ReceiverScan<'s> {
            resolutions:
                &'s FxHashMap<crate::node_id::NodeID, crate::types::output::MemberResolution>,
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
                let Some(symbol) = receiver_root_symbol(receiver) else {
                    return;
                };
                let target = match self.resolutions.get(&callee.id) {
                    Some(crate::types::output::MemberResolution::Direct(s)) => *s,
                    Some(crate::types::output::MemberResolution::ViaConformance {
                        witness,
                        ..
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
        if ctx.top_level {
            self.top_level_cells.insert(*symbol, cell_var);
        }
        let body = self.with_cells(rest, ctx, finish);
        self.p.set_body(bind, body);
        let bind_ref = self.p.func_ref(bind);
        let cell = self.p.primop(Op::CellNew, &[*init], cell_ty);
        self.p.app(bind_ref, cell)
    }

    // ----- Expressions ------------------------------------------------------

    /// Lower `expr`, delivering its value to continuation `k : Fn(T, ⊥)`.
    fn lower_expr(&mut self, expr: &Expr, ctx: &Ctx, k: ExprId) -> ExprId {
        if let Some(pack) = self.existential_pack_at(expr.id, ctx) {
            if let CheckTy::Any { protocol, .. } = &pack.payload
                && *protocol == self.any_protocol(&pack.existential).unwrap_or(*protocol)
            {
                return self.lower_expr_unpacked(expr, ctx, k);
            }
            if let Some(payload) = self.try_pure_unpacked(expr, ctx) {
                return match self.existential_pack_value(expr.id, payload, &pack, ctx) {
                    Some(value) => self.p.app(k, value),
                    None => self.dead_end("existential_pack"),
                };
            }
            let payload_ty = self.map_ty(&pack.payload);
            let bot = self.p.ty_bot();
            let pack_k = self.p.func("pack_existential", payload_ty, bot);
            let payload = self.p.var(pack_k);
            let body = match self.existential_pack_value(expr.id, payload, &pack, ctx) {
                Some(value) => self.p.app(k, value),
                None => self.dead_end("existential_pack"),
            };
            self.p.set_body(pack_k, body);
            let pack_ref = self.p.func_ref(pack_k);
            return self.lower_expr_unpacked(expr, ctx, pack_ref);
        }
        self.lower_expr_unpacked(expr, ctx, k)
    }

    fn lower_expr_unpacked(&mut self, expr: &Expr, ctx: &Ctx, k: ExprId) -> ExprId {
        if let Some(value) = self.try_pure_unpacked(expr, ctx) {
            return self.p.app(k, value);
        }
        match &expr.kind {
            ExprKind::Call {
                callee,
                args,
                trailing_block,
                ..
            } => {
                // Variant construction with impure payloads: chain the
                // arguments, then build the value (no function is called).
                if let Some((enum_symbol, tag, variant_symbol, node)) =
                    self.variant_target(expr, callee, ctx)
                {
                    let arg_exprs: Vec<&Expr> = args.iter().map(|a| &a.value).collect();
                    return self.lower_args(&arg_exprs, ctx, vec![], &mut |this, values| {
                        let value = this.variant_new_for_expr(
                            node,
                            enum_symbol,
                            tag,
                            variant_symbol,
                            &values,
                            ctx,
                        );
                        this.p.app(k, value)
                    });
                }
                self.lower_call(expr, callee, args, trailing_block.as_ref(), ctx, k)
            }
            ExprKind::If(cond, then_block, else_block) => {
                let then_body = self.lower_block(then_block, ctx, k);
                let else_body = self.lower_block(else_block, ctx, k);
                self.branch(cond, then_body, else_body, ctx)
            }
            ExprKind::Block(block) => self.lower_block(block, ctx, k),
            // A parenthesized expression parses as a 1-tuple.
            ExprKind::Tuple(items) if items.len() == 1 => self.lower_expr(&items[0], ctx, k),
            // A tuple literal with impure items: chain them left to right.
            ExprKind::Tuple(items) => {
                let item_exprs: Vec<&Expr> = items.iter().collect();
                self.lower_args(&item_exprs, ctx, vec![], &mut |this, values| {
                    let tuple = this.p.tuple(&values);
                    this.p.app(k, tuple)
                })
            }
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
                        self.dead_end("member_not_a_stored_field")
                    }
                };
                self.p.set_body(cont, body);
                let cont_ref = self.p.func_ref(cont);
                self.lower_expr(receiver, ctx, cont_ref)
            }
            ExprKind::Match(scrutinee, arms) => self.lower_match(scrutinee, arms, ctx, k),
            // Performing an effect with no handler in scope reaches the
            // implicit top-level handler (Plotkin & Pretnar, LMCS 2013).
            // A request that is a syntactic IORequest variant routes
            // statically to its io primop; in-language handlers are M7,
            // the dynamic io_perform dispatch M8.
            ExprKind::CallEffect {
                effect_name, args, ..
            } => {
                // Routed first: the resolver bound this perform to a
                // lexical handler — call its capability (M7).
                if let Some(&handler_sym) =
                    self.units[ctx.unit].resolved.effect_handlers.get(&expr.id)
                {
                    return self.lower_routed_perform(handler_sym, args, ctx, k);
                }
                self.lower_perform(expr, effect_name, args, ctx, k)
            }
            // An array literal: allocate element-sized storage, store each
            // element in order (one effect per continuation step), then
            // build the Array record {storage, count, capacity}.
            // This stays as direct storage fill for now; routing through
            // Array.init would not add ownership precision.
            ExprKind::LiteralArray(items) => {
                let CheckTy::Nominal(array_symbol, args) = self.checker_ty(expr, ctx) else {
                    self.diagnostics
                        .push("lowering: array literal without an Array type".into());
                    let void = self.p.void();
                    return self.p.app(k, void);
                };
                let element_ty = args
                    .first()
                    .map(|t| self.map_ty(t))
                    .unwrap_or_else(|| self.p.ty_void());
                let Some(size) = self.p.ty_kind(element_ty).mem_size() else {
                    self.diagnostics
                        .push("lowering: array element type cannot live in memory".into());
                    let void = self.p.void();
                    return self.p.app(k, void);
                };
                let item_exprs: Vec<&Expr> = items.iter().collect();
                self.lower_args(&item_exprs, ctx, vec![], &mut |this, values| {
                    let count = values.len();
                    let ptr_ty = this.p.ty_ptr();
                    let void_ty = this.p.ty_void();
                    let bot = this.p.ty_bot();
                    // The alloc is an effect: bind its address through a
                    // continuation so it runs exactly once.
                    let array_k = this.p.func("array", ptr_ty, bot);
                    let ptr = this.p.var(array_k);
                    let record_ty = this.p.ty(TyKind::Boxed(array_symbol));
                    let n = this.p.int(count as i64);
                    let Some(storage) = this.array_storage_value(array_symbol, ptr) else {
                        return this.dead_end("invalid_array_storage_wrapper");
                    };
                    let record =
                        this.p
                            .primop(Op::RecordNew(array_symbol), &[storage, n, n], record_ty);
                    let mut body = this.p.app(k, record);
                    // Stores chain backwards so they execute in source
                    // order, each through its own continuation.
                    for (i, &value) in values.iter().enumerate().rev() {
                        let addr = if i == 0 {
                            ptr
                        } else {
                            let offset = this.p.int((i as u32 * size) as i64);
                            this.p.add(ptr, offset)
                        };
                        let store = this.p.primop(Op::Store, &[addr, value], void_ty);
                        let stored = this.p.func("stored", void_ty, bot);
                        this.p.set_body(stored, body);
                        let stored_ref = this.p.func_ref(stored);
                        body = this.p.app(stored_ref, store);
                    }
                    this.p.set_body(array_k, body);
                    let bytes = this.p.int((count as u32 * size) as i64);
                    let alloc = this.p.primop(Op::Alloc, &[bytes], ptr_ty);
                    let array_ref = this.p.func_ref(array_k);
                    this.p.app(array_ref, alloc)
                })
            }
            // A record literal with impure fields: evaluate in source
            // order, then assemble the tuple in row order.
            ExprKind::RecordLiteral { fields, spread } => {
                if spread.is_some() {
                    self.diagnostics
                        .push("lowering: record spread not yet supported".into());
                    let void = self.p.void();
                    return self.p.app(k, void);
                }
                let Some(order) = self.record_field_order(expr, fields, ctx) else {
                    self.diagnostics
                        .push("lowering: record literal without a closed record type".into());
                    let void = self.p.void();
                    return self.p.app(k, void);
                };
                let field_exprs: Vec<&Expr> = fields.iter().map(|f| &f.value).collect();
                self.lower_args(&field_exprs, ctx, vec![], &mut |this, values| {
                    let items: Vec<ExprId> = order.iter().map(|&i| values[i]).collect();
                    let tuple = this.p.tuple(&items);
                    this.p.app(k, tuple)
                })
            }
            other => {
                self.diagnostics
                    .push(format!("lowering: expression not yet supported: {other:?}"));
                self.dead_end("unsupported_expr")
            }
        }
    }

    // ----- Match -------------------------------------------------------------

    /// Match compilation: bind the scrutinee to a pure value, then build
    /// the decision tree (Maranget, ML 2008 — `patterns.rs`).
    fn lower_match(&mut self, scrutinee: &Expr, arms: &[MatchArm], ctx: &Ctx, k: ExprId) -> ExprId {
        let scrutinee_check_ty = self.checker_ty(scrutinee, ctx);
        let pattern_scrutinee_ty = Self::borrow_erased_ty(scrutinee_check_ty.clone());
        match self.try_pure(scrutinee, ctx) {
            Some(value) => patterns::compile_match(self, value, pattern_scrutinee_ty, arms, ctx, k),
            None => {
                let scrutinee_ty = self.expr_lambda_ty(scrutinee, ctx);
                let bot = self.p.ty_bot();
                let cont = self.p.func("scrut", scrutinee_ty, bot);
                let value = self.p.var(cont);
                let body = patterns::compile_match(self, value, pattern_scrutinee_ty, arms, ctx, k);
                self.p.set_body(cont, body);
                let cont_ref = self.p.func_ref(cont);
                self.lower_expr(scrutinee, ctx, cont_ref)
            }
        }
    }

    /// Pure expressions evaluate without continuations: literals, bound
    /// variables, field reads on pure receivers, and @_ir splices over
    /// pure operands.
    fn try_pure(&mut self, expr: &Expr, ctx: &Ctx) -> Option<ExprId> {
        if let Some(pack) = self.existential_pack_at(expr.id, ctx) {
            if let CheckTy::Any { protocol, .. } = &pack.payload
                && *protocol == self.any_protocol(&pack.existential).unwrap_or(*protocol)
            {
                return self.try_pure_unpacked(expr, ctx);
            }
            let payload = self.try_pure_unpacked(expr, ctx)?;
            return self.existential_pack_value(expr.id, payload, &pack, ctx);
        }
        self.try_pure_unpacked(expr, ctx)
    }

    fn try_pure_unpacked(&mut self, expr: &Expr, ctx: &Ctx) -> Option<ExprId> {
        match &expr.kind {
            ExprKind::LiteralInt(text) => Some(self.p.int(text.parse().ok()?)),
            ExprKind::LiteralFloat(text) => Some(self.p.float(text.parse().ok()?)),
            ExprKind::LiteralTrue => Some(self.p.bool(true)),
            ExprKind::LiteralFalse => Some(self.p.bool(false)),
            // A string literal is a String record over interned static
            // bytes: {storage, length, capacity}.
            ExprKind::LiteralString(text) => {
                let bytes = crate::parsing::lexing::unescape(text).into_bytes();
                let offset = self.intern_static(&bytes);
                let CheckTy::Nominal(string_symbol, _) =
                    Self::borrow_erased_ty(self.checker_ty(expr, ctx))
                else {
                    self.diagnostics
                        .push("lowering: string literal with a non-nominal type".into());
                    return None;
                };
                let ptr_ty = self.p.ty_ptr();
                let base = self.p.constant(Const::StaticPtr(offset), ptr_ty);
                let len = self.p.int(bytes.len() as i64);
                let ty = self.p.ty(TyKind::Boxed(string_symbol));
                let Some(storage) = self.string_storage_value(string_symbol, base) else {
                    return Some(self.dead_end("invalid_string_storage_wrapper"));
                };
                Some(
                    self.p
                        .primop(Op::RecordNew(string_symbol), &[storage, len, len], ty),
                )
            }
            // Field read on a pure receiver: GetField (records are pure
            // values). A member that resolves to a payload-less enum case
            // (`.none`, `Optional.none`) is a variant value instead.
            ExprKind::Member(receiver, _, _) => {
                if let Some(value) = self.try_variant_value(expr, ctx) {
                    return Some(value);
                }
                let receiver = receiver.as_deref()?;
                let receiver_value = self.try_pure(receiver, ctx)?;
                self.field_read(expr, receiver, receiver_value, ctx)
            }
            // Variant construction over pure payloads (`.some(1)`,
            // `Maybe.definitely(x)`): pure, exactly like RecordNew.
            ExprKind::Call { callee, args, .. } => {
                let (enum_symbol, tag, variant_symbol, node) =
                    self.variant_target(expr, callee, ctx)?;
                let mut payloads = Vec::with_capacity(args.len());
                for arg in args {
                    payloads.push(self.try_pure(&arg.value, ctx)?);
                }
                Some(self.variant_new_for_expr(
                    node,
                    enum_symbol,
                    tag,
                    variant_symbol,
                    &payloads,
                    ctx,
                ))
            }
            // A record literal over pure fields: a tuple in the row's
            // canonical (label-sorted) field order.
            ExprKind::RecordLiteral { fields, spread } => {
                if spread.is_some() {
                    return None;
                }
                let order = self.record_field_order(expr, fields, ctx)?;
                let mut values = Vec::with_capacity(fields.len());
                for field in fields {
                    values.push(self.try_pure(&field.value, ctx)?);
                }
                let items: Vec<ExprId> = order.iter().map(|&i| values[i]).collect();
                Some(self.p.tuple(&items))
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
                // A mutable top-level binding: read its registered cell
                // (a free variable of main; closure conversion carries it).
                if let Some(&cell) = self.top_level_cells.get(&symbol) {
                    let TyKind::Cell(inner) = *self.p.ty_kind(self.p.expr_ty(cell)) else {
                        return None;
                    };
                    return Some(self.p.primop(Op::CellGet, &[cell], inner));
                }
                // A function-typed global used as a value: demand its
                // specialization (instantiation recorded at this node).
                if self.sources.contains_key(&symbol) {
                    if self.abort_shape(symbol) {
                        self.diagnostics.push(
                            "lowering: an abort-capable function used as a value (not yet supported)"
                                .into(),
                        );
                        return None;
                    }
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
                        owner: None,
                        theta: Theta::default(),
                        env: FxHashMap::default(),
                        local_evidence: FxHashMap::default(),
                        ret_k: ctx.ret_k,
                        tail_k: ctx.ret_k,
                        raw_ret_k: ctx.raw_ret_k,
                        normal_k: None,
                        abort_ok: false,
                        resume_k: None,
                        top_level: false,
                        local_handlers: FxHashSet::default(),
                        params: vec![],
                        loops: vec![],
                        drop_stack: vec![],
                        drop_flags: FxHashMap::default(),
                        initializing_self: None,
                        cellable: FxHashSet::default(),
                    };
                    return self.try_pure(rhs, &global_ctx);
                }
                None
            }
            // A function literal is a value: its λ_G Func reference
            // (captures are its free variables).
            ExprKind::Func(func) => self.lower_func_value(expr, func, ctx),
            // The unit literal `()`.
            ExprKind::Tuple(items) if items.is_empty() => Some(self.p.void()),
            ExprKind::InlineIR(instruction) => self.splice(instruction, ctx),
            ExprKind::Tuple(items) if items.len() == 1 => self.try_pure(&items[0], ctx),
            // A tuple literal over pure items.
            ExprKind::Tuple(items) => {
                let mut values = Vec::with_capacity(items.len());
                for item in items {
                    values.push(self.try_pure(item, ctx)?);
                }
                Some(self.p.tuple(&values))
            }
            _ => None,
        }
    }

    fn existential_pack_at(
        &self,
        node: crate::node_id::NodeID,
        ctx: &Ctx,
    ) -> Option<crate::types::output::ExistentialPack> {
        let pack = self.units[ctx.unit].types.existential_packs.get(&node)?;
        let existential =
            pack.existential
                .substitute(&ctx.theta, &Default::default(), &Default::default());
        let payload = pack
            .payload
            .substitute(&ctx.theta, &Default::default(), &Default::default());
        Some(crate::types::output::ExistentialPack {
            existential: self.normalize_check_ty(existential, ctx.unit),
            payload: self.normalize_check_ty(payload, ctx.unit),
        })
    }

    fn any_protocol(&self, ty: &CheckTy) -> Option<Symbol> {
        match ty {
            CheckTy::Any { protocol, .. } => Some(*protocol),
            _ => None,
        }
    }

    fn existential_pack_value(
        &mut self,
        node: crate::node_id::NodeID,
        payload: ExprId,
        pack: &crate::types::output::ExistentialPack,
        ctx: &Ctx,
    ) -> Option<ExprId> {
        let CheckTy::Any { protocol, assoc } = &pack.existential else {
            self.diagnostics
                .push("lowering: existential pack target is not an existential".into());
            return None;
        };
        if let CheckTy::Any {
            protocol: payload_protocol,
            ..
        } = &pack.payload
        {
            if payload_protocol == protocol {
                return Some(payload);
            }
            self.diagnostics.push(
                "lowering: existential upcast/repack reached lowering after type checking".into(),
            );
            return None;
        }
        if let CheckTy::Param(param) = &pack.payload {
            return self
                .existential_pack_from_local_evidence(*protocol, assoc, *param, payload, ctx);
        }

        let requirements = self.units[ctx.unit]
            .types
            .catalog
            .requirements_for_conformance(*protocol);
        let mut values = Vec::with_capacity(requirements.len() + 1);
        values.push(payload);
        for (owner, label, requirement) in requirements {
            let witness = self.existential_witness_wrapper(
                *protocol,
                assoc,
                owner,
                &label,
                &requirement,
                &pack.payload,
                ctx,
                node,
            )?;
            values.push(witness);
        }
        let ty = self.p.ty(TyKind::Existential(*protocol));
        Some(self.p.primop(Op::ExistentialPack(*protocol), &values, ty))
    }

    fn existential_pack_from_local_evidence(
        &mut self,
        protocol: Symbol,
        assoc: &[(Symbol, CheckTy)],
        param: Symbol,
        payload: ExprId,
        ctx: &Ctx,
    ) -> Option<ExprId> {
        let evidence = self.local_evidence_for(ctx, param, protocol)?;
        let target_requirements = self.units[ctx.unit]
            .types
            .catalog
            .requirements_for_conformance(protocol);
        let source_requirements = self.units[ctx.unit]
            .types
            .catalog
            .requirements_for_conformance(evidence.protocol);
        let mut values = Vec::with_capacity(target_requirements.len() + 1);
        values.push(payload);
        for (owner, label, requirement) in target_requirements {
            let source_index = source_requirements
                .iter()
                .position(|(_, _, source)| source.symbol == requirement.symbol)?;
            let _signature =
                self.erased_requirement_signature(protocol, assoc, owner, &requirement, ctx.unit)?;
            values.push(self.p.extract(evidence.table, source_index as u32));
            let _ = label;
        }
        let ty = self.p.ty(TyKind::Existential(protocol));
        Some(self.p.primop(Op::ExistentialPack(protocol), &values, ty))
    }

    fn local_evidence_for(
        &self,
        ctx: &Ctx,
        param: Symbol,
        protocol: Symbol,
    ) -> Option<EvidenceBinding> {
        if let Some(binding) = ctx.local_evidence.get(&(param, protocol)).copied() {
            return Some(binding);
        }
        if let Some((_, binding)) =
            ctx.local_evidence
                .iter()
                .find(|((candidate_param, candidate_protocol), _)| {
                    *candidate_param == param
                        && self.units[ctx.unit]
                            .types
                            .catalog
                            .bounds_satisfy(&[*candidate_protocol], protocol)
                })
        {
            return Some(*binding);
        }
        let candidates: Vec<EvidenceBinding> = ctx
            .local_evidence
            .iter()
            .filter(|((_, candidate_protocol), _)| {
                self.units[ctx.unit]
                    .types
                    .catalog
                    .bounds_satisfy(&[*candidate_protocol], protocol)
            })
            .map(|(_, binding)| *binding)
            .collect();
        match candidates.as_slice() {
            [single] => Some(*single),
            _ => None,
        }
    }

    fn evidence_table_for_ty(
        &mut self,
        protocol: Symbol,
        payload_ty: &CheckTy,
        ctx: &Ctx,
        node: crate::node_id::NodeID,
    ) -> Option<ExprId> {
        if let CheckTy::Param(param) = payload_ty
            && let Some(evidence) = self.local_evidence_for(ctx, *param, protocol)
        {
            return Some(evidence.table);
        }
        let assoc = self.assoc_bindings_for_concrete(protocol, payload_ty, ctx.unit);
        let requirements = self.units[ctx.unit]
            .types
            .catalog
            .requirements_for_conformance(protocol);
        let mut witnesses = Vec::with_capacity(requirements.len());
        for (owner, label, requirement) in requirements {
            let witness = self.existential_witness_wrapper(
                protocol,
                &assoc,
                owner,
                &label,
                &requirement,
                payload_ty,
                ctx,
                node,
            )?;
            witnesses.push(witness);
        }
        Some(self.p.tuple(&witnesses))
    }

    fn evidence_table_ty(
        &mut self,
        protocol: Symbol,
        assoc: &[(Symbol, CheckTy)],
        unit: usize,
    ) -> TyId {
        let requirements = self.units[unit]
            .types
            .catalog
            .requirements_for_conformance(protocol);
        let witness_tys: Vec<TyId> = requirements
            .into_iter()
            .filter_map(|(owner, _, requirement)| {
                let signature =
                    self.erased_requirement_signature(protocol, assoc, owner, &requirement, unit)?;
                Some(self.map_ty(&signature))
            })
            .collect();
        self.p.ty_tuple(&witness_tys)
    }

    fn assoc_bindings_for_concrete(
        &self,
        protocol: Symbol,
        payload_ty: &CheckTy,
        unit: usize,
    ) -> Vec<(Symbol, CheckTy)> {
        let required = self.units[unit].types.catalog.associated_types_in(protocol);
        let CheckTy::Nominal(head, args) = payload_ty else {
            return required
                .into_iter()
                .map(|(_, symbol)| (symbol, CheckTy::Param(symbol)))
                .collect();
        };
        let Some(conformance) = self.units[unit]
            .types
            .catalog
            .conformances
            .get(&(*head, protocol))
        else {
            return required
                .into_iter()
                .map(|(_, symbol)| (symbol, CheckTy::Param(symbol)))
                .collect();
        };
        let mut row_theta = Theta::default();
        for (pattern, actual) in conformance.self_args.iter().zip(args) {
            crate::types::solve::bind_param_pattern(pattern, actual, &mut row_theta);
        }
        required
            .into_iter()
            .map(|(_, symbol)| {
                let ty = conformance
                    .assoc
                    .get(&symbol)
                    .map(|ty| ty.substitute(&row_theta, &Default::default(), &Default::default()))
                    .unwrap_or(CheckTy::Param(symbol));
                (symbol, ty)
            })
            .collect()
    }

    #[allow(clippy::too_many_arguments)]
    fn existential_witness_wrapper(
        &mut self,
        root_protocol: Symbol,
        assoc: &[(Symbol, CheckTy)],
        owner: Symbol,
        label: &str,
        requirement: &crate::types::catalog::Requirement,
        payload_ty: &CheckTy,
        ctx: &Ctx,
        node: crate::node_id::NodeID,
    ) -> Option<ExprId> {
        let signature =
            self.erased_requirement_signature(root_protocol, assoc, owner, requirement, ctx.unit)?;
        let CheckTy::Func(params, ret, _) = signature else {
            self.diagnostics
                .push("lowering: existential requirement is not a function".into());
            return None;
        };
        let mut dom_items: Vec<TyId> = params.iter().map(|param| self.map_ty(param)).collect();
        let ret_ty = self.map_ty(&ret);
        let bot = self.p.ty_bot();
        let ret_k_ty = self.p.ty_fn(ret_ty, bot);
        dom_items.push(ret_k_ty);
        let dom = self.p.ty_tuple(&dom_items);
        let wrapper = self.p.func(
            &format!("existential_{}_{}", root_protocol, label),
            dom,
            bot,
        );
        self.escaping.insert(wrapper);

        let self_var = self.p.var(wrapper);
        let erased_self = self.p.extract(self_var, 0);
        let payload_lambda_ty = self.map_ty(payload_ty);
        let payload = self
            .p
            .primop(Op::ExistentialPayload, &[erased_self], payload_lambda_ty);
        let mut args = Vec::with_capacity(params.len() + 1);
        args.push(payload);
        for index in 1..params.len() {
            args.push(self.p.extract(self_var, index as u32));
        }
        let ret_k = self.p.extract(self_var, params.len() as u32);
        args.push(ret_k);
        let arg_tuple = self.p.tuple(&args);
        let Some((target, _)) =
            self.resolve_witness(owner, requirement.symbol, label.to_string(), payload_ty)
        else {
            self.diagnostics.push(format!(
                "lowering: cannot build existential witness for {label} at {:?}",
                node
            ));
            return None;
        };
        let target_ref = self.p.func_ref(target);
        let body = self.p.app(target_ref, arg_tuple);
        self.p.set_body(wrapper, body);
        Some(self.p.func_ref(wrapper))
    }

    fn erased_requirement_signature(
        &mut self,
        root_protocol: Symbol,
        assoc: &[(Symbol, CheckTy)],
        owner: Symbol,
        requirement: &crate::types::catalog::Requirement,
        unit: usize,
    ) -> Option<CheckTy> {
        let mut tys = Theta::default();
        tys.insert(
            owner,
            CheckTy::Any {
                protocol: root_protocol,
                assoc: assoc.to_vec(),
            },
        );
        for (assoc_symbol, ty) in assoc {
            tys.insert(*assoc_symbol, ty.clone());
        }
        let signature = requirement
            .sig
            .substitute(&tys, &Default::default(), &Default::default());
        Some(self.normalize_check_ty(signature, unit))
    }

    fn existential_requirement_index(
        &self,
        protocol: Symbol,
        label: &str,
        requirement_symbol: Symbol,
        unit: usize,
    ) -> Option<usize> {
        self.units[unit]
            .types
            .catalog
            .requirements_for_conformance(protocol)
            .iter()
            .position(|(_, candidate_label, requirement)| {
                candidate_label == label && requirement.symbol == requirement_symbol
            })
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

    /// Array literals allocate raw bytes internally, but the public Array
    /// storage field may now be a managed storage wrapper. If the core
    /// Array still has the old RawPtr layout, leave the pointer untouched.
    fn array_storage_value(&mut self, array_symbol: Symbol, ptr: ExprId) -> Option<ExprId> {
        let Some(field_ty) = self
            .units
            .iter()
            .find_map(|unit| unit.types.catalog.structs.get(&array_symbol))
            .and_then(|info| info.fields.get("storage").map(|(_, ty)| ty.clone()))
        else {
            return Some(ptr);
        };
        self.storage_wrapper_value(&field_ty, ptr, "Array")
    }

    /// String literals also start from a raw pointer into static bytes, while
    /// the source-level String may store a managed byte storage wrapper.
    fn string_storage_value(&mut self, string_symbol: Symbol, ptr: ExprId) -> Option<ExprId> {
        let Some(field_ty) = self
            .units
            .iter()
            .find_map(|unit| unit.types.catalog.structs.get(&string_symbol))
            .and_then(|info| {
                info.fields
                    .get("storage")
                    .or_else(|| info.fields.get("base"))
                    .map(|(_, ty)| ty.clone())
            })
        else {
            return Some(ptr);
        };
        self.storage_wrapper_value(&field_ty, ptr, "String")
    }

    fn storage_wrapper_value(
        &mut self,
        field_ty: &CheckTy,
        ptr: ExprId,
        owner: &str,
    ) -> Option<ExprId> {
        let CheckTy::Nominal(storage_symbol, _) = field_ty else {
            self.diagnostics.push(format!(
                "lowering: {owner} storage field is not RawPtr or a RawPtr wrapper"
            ));
            return None;
        };
        if *storage_symbol == Symbol::RawPtr {
            return Some(ptr);
        }
        let Some(storage_info) = self
            .units
            .iter()
            .find_map(|unit| unit.types.catalog.structs.get(storage_symbol))
        else {
            self.diagnostics.push(format!(
                "lowering: {owner} storage wrapper does not resolve to a struct"
            ));
            return None;
        };
        if storage_info.fields.len() != 1 {
            self.diagnostics.push(format!(
                "lowering: {owner} storage wrapper does not expose a RawPtr field"
            ));
            return None;
        }
        let Some((_, CheckTy::Nominal(head, _))) =
            storage_info.fields.values().next().map(|(_, ty)| ((), ty))
        else {
            self.diagnostics.push(format!(
                "lowering: {owner} storage wrapper does not expose a RawPtr field"
            ));
            return None;
        };
        if *head != Symbol::RawPtr {
            self.diagnostics.push(format!(
                "lowering: {owner} storage wrapper does not expose a RawPtr field"
            ));
            return None;
        }
        let storage_ty = self.map_ty(field_ty);
        Some(
            self.p
                .primop(Op::RecordNew(*storage_symbol), &[ptr], storage_ty),
        )
    }

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
        // Anonymous records are label-sorted tuples (map_ty), so a field
        // read is an extract at the label's canonical position.
        let head = Self::borrow_erased_ty(self.checker_ty(receiver, ctx));
        if let CheckTy::Record(row) = &head
            && row.tail.is_none()
            && let ExprKind::Member(_, label, _) = &expr.kind
            && let Some(index) = row
                .fields
                .iter()
                .position(|(name, _)| name.to_string() == label.to_string())
        {
            return Some(self.p.extract(receiver_value, index as u32));
        }
        let resolution = self.units[ctx.unit]
            .types
            .member_resolutions
            .get(&expr.id)
            .cloned();
        if let Some(crate::types::output::MemberResolution::Direct(property)) = resolution {
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

    /// Is this callee a stored field holding a function value — a call
    /// through a record field (`self.route_handler0.invoke()`), as
    /// opposed to a method call? Field callees dispatch indirectly.
    fn is_field_value_callee(&mut self, callee: &Expr, ctx: &Ctx) -> bool {
        let ExprKind::Member(Some(receiver), label, _) = &callee.kind else {
            return false;
        };
        let head = Self::borrow_erased_ty(self.checker_ty(receiver, ctx));
        match self.units[ctx.unit]
            .types
            .member_resolutions
            .get(&callee.id)
            .cloned()
        {
            Some(crate::types::output::MemberResolution::Direct(property)) => {
                self.field_index(&head, property).is_some()
            }
            Some(_) => false,
            None => {
                let CheckTy::Nominal(head_symbol, _) = head else {
                    return false;
                };
                self.units
                    .iter()
                    .find_map(|u| u.types.catalog.structs.get(&head_symbol))
                    .is_some_and(|info| info.fields.contains_key(&label.to_string()))
            }
        }
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

    // ----- Enums ---------------------------------------------------------

    /// The catalog row for an enum symbol (cloned: callers keep building
    /// the program while reading it).
    fn enum_info(&self, symbol: Symbol) -> Option<crate::types::catalog::Enum> {
        self.units
            .iter()
            .find_map(|u| u.types.catalog.enums.get(&symbol).cloned())
    }

    fn is_enum(&self, symbol: Symbol) -> bool {
        self.units
            .iter()
            .any(|u| u.types.catalog.enums.contains_key(&symbol))
    }

    fn is_init(&self, symbol: Symbol) -> bool {
        self.units.iter().any(|u| {
            u.types
                .catalog
                .structs
                .values()
                .any(|info| info.inits.contains(&symbol))
        })
    }

    /// The enum and declaration-index tag of a variant symbol, when
    /// `symbol` names an enum case. Tags are declaration order — the same
    /// numbering `GetTag`/`Switch` dispatch on at runtime.
    fn variant_of(&self, symbol: Symbol) -> Option<(Symbol, u16)> {
        for unit in &self.units {
            for (enum_symbol, info) in &unit.types.catalog.enums {
                if let Some(index) = info.variants.values().position(|v| v.symbol == symbol) {
                    return Some((*enum_symbol, index as u16));
                }
            }
        }
        None
    }

    /// Does this call construct an enum variant? The checker resolves
    /// `.some(x)` at the call node (checking mode) and `Optional.some(x)`
    /// at the member callee node; either way the resolution is the variant
    /// symbol.
    fn variant_target(
        &self,
        expr: &Expr,
        callee: &Expr,
        ctx: &Ctx,
    ) -> Option<(Symbol, u16, Symbol, crate::node_id::NodeID)> {
        let resolutions = &self.units[ctx.unit].types.member_resolutions;
        let (node, symbol) =
            [callee.id, expr.id]
                .iter()
                .find_map(|node| match resolutions.get(node) {
                    Some(crate::types::output::MemberResolution::Direct(s)) => Some((*node, *s)),
                    _ => None,
                })?;
        let (enum_symbol, tag) = self.variant_of(symbol)?;
        Some((enum_symbol, tag, symbol, node))
    }

    /// Construct a variant value: source payloads followed by hidden runtime
    /// evidence for GADT-local constructor bounds.
    fn variant_new_for_expr(
        &mut self,
        node: crate::node_id::NodeID,
        enum_symbol: Symbol,
        tag: u16,
        variant_symbol: Symbol,
        payloads: &[ExprId],
        ctx: &Ctx,
    ) -> ExprId {
        let mut runtime_payloads = payloads.to_vec();
        runtime_payloads.extend(self.variant_evidence_tables(node, variant_symbol, ctx));
        self.variant_new(enum_symbol, tag, &runtime_payloads)
    }

    fn variant_evidence_tables(
        &mut self,
        node: crate::node_id::NodeID,
        variant_symbol: Symbol,
        ctx: &Ctx,
    ) -> Vec<ExprId> {
        let Some(variant) = self.variant_by_symbol(variant_symbol) else {
            return vec![];
        };
        let theta = self.instantiation_at(node, ctx);
        let mut tables = vec![];
        for predicate in &variant.constructor_scheme.predicates {
            let crate::types::ty::Predicate::Conforms { ty, protocol } = predicate else {
                continue;
            };
            let CheckTy::Param(param) = ty else {
                continue;
            };
            let concrete = theta.get(param).cloned().unwrap_or(CheckTy::Param(*param));
            match self.evidence_table_for_ty(*protocol, &concrete, ctx, node) {
                Some(table) => tables.push(table),
                None => {
                    self.diagnostics.push(format!(
                        "lowering: cannot store runtime evidence for constructor bound {param}: {protocol}"
                    ));
                    tables.push(self.p.tuple(&[]));
                }
            }
        }
        tables
    }

    pub(super) fn variant_pattern_evidence(
        &mut self,
        variant: &crate::types::catalog::Variant,
        instantiation: &crate::types::variant::VariantInstantiation,
        value: ExprId,
        source_payload_count: usize,
        unit: usize,
    ) -> Vec<((Symbol, Symbol), EvidenceBinding)> {
        let mut evidence = vec![];
        let mut runtime_index = source_payload_count as u32;
        let subst: Theta = instantiation.instantiations.iter().cloned().collect();
        for source in &variant.constructor_scheme.predicates {
            let crate::types::ty::Predicate::Conforms {
                ty: CheckTy::Param(source_param),
                protocol,
            } = source
            else {
                continue;
            };
            let instantiated = source.substitute(&subst, &Default::default(), &Default::default());
            if let crate::types::ty::Predicate::Conforms {
                ty: CheckTy::Param(param),
                ..
            } = instantiated
            {
                let table_ty = self.evidence_table_ty(*protocol, &[], unit);
                let table = self
                    .p
                    .primop(Op::GetPayload(runtime_index), &[value], table_ty);
                evidence.push((
                    (param, *protocol),
                    EvidenceBinding {
                        protocol: *protocol,
                        table,
                    },
                ));
            }
            let _ = source_param;
            runtime_index += 1;
        }
        evidence
    }

    fn variant_by_symbol(&self, variant_symbol: Symbol) -> Option<crate::types::catalog::Variant> {
        for unit in &self.units {
            for info in unit.types.catalog.enums.values() {
                if let Some(variant) = info
                    .variants
                    .values()
                    .find(|variant| variant.symbol == variant_symbol)
                {
                    return Some(variant.clone());
                }
            }
        }
        None
    }

    /// Construct a raw variant value: pure, exactly like `RecordNew`.
    fn variant_new(&mut self, enum_symbol: Symbol, tag: u16, payloads: &[ExprId]) -> ExprId {
        let ty = self.p.ty(TyKind::Variant(enum_symbol));
        self.p
            .primop(Op::VariantNew(enum_symbol, tag), payloads, ty)
    }

    /// A bare member that *is* a payload-less variant (`.none`,
    /// `Optional.none`): a pure value.
    fn try_variant_value(&mut self, expr: &Expr, ctx: &Ctx) -> Option<ExprId> {
        let resolution = self.units[ctx.unit]
            .types
            .member_resolutions
            .get(&expr.id)?;
        let crate::types::output::MemberResolution::Direct(symbol) = resolution else {
            return None;
        };
        let (enum_symbol, tag) = self.variant_of(*symbol)?;
        // A payload-carrying variant used bare is a function value (M6
        // closures); only payload-less cases are values here.
        let has_payloads = self.units.iter().any(|u| {
            u.types
                .catalog
                .enums
                .get(&enum_symbol)
                .and_then(|info| info.variants.get_index(tag as usize))
                .is_some_and(|(_, v)| !v.argument_types().is_empty())
        });
        if has_payloads {
            return None;
        }
        Some(self.variant_new_for_expr(expr.id, enum_symbol, tag, *symbol, &[], ctx))
    }

    /// For a record literal: row position → source field index, from the
    /// checker's (label-sorted) row. Fields still *evaluate* in source
    /// order; this permutation only places the values.
    fn record_field_order(
        &mut self,
        expr: &Expr,
        fields: &[crate::node_kinds::record_field::RecordField],
        ctx: &Ctx,
    ) -> Option<Vec<usize>> {
        let CheckTy::Record(row) = self.checker_ty(expr, ctx) else {
            return None;
        };
        if row.tail.is_some() || row.fields.len() != fields.len() {
            return None;
        }
        row.fields
            .iter()
            .map(|(label, _)| {
                let name = label.to_string();
                fields.iter().position(|f| f.label.name_str() == name)
            })
            .collect()
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

    // ----- Function values (closures) ---------------------------------------

    /// A function literal: a λ_G function whose body sees the enclosing
    /// environment — free variables ARE the captures (paper §2.2's
    /// higher-order setting; the reference evaluator runs them by
    /// dependency-aware substitution, the scheduler closure-converts).
    fn lower_func_value(
        &mut self,
        expr: &Expr,
        func: &crate::node_kinds::func::Func,
        ctx: &Ctx,
    ) -> Option<ExprId> {
        let CheckTy::Func(param_check_tys, ret_check, _) = self.checker_ty(expr, ctx) else {
            self.diagnostics
                .push("lowering: function literal without a function type".into());
            return None;
        };
        let param_tys: Vec<TyId> = param_check_tys.iter().map(|t| self.map_ty(t)).collect();
        let ret_ty = self.map_ty(&ret_check);
        let bot = self.p.ty_bot();
        let ret_k_ty = self.p.ty_fn(ret_ty, bot);
        let mut dom_items = param_tys;
        dom_items.push(ret_k_ty);
        let dom = self.p.ty_tuple(&dom_items);
        let label = self.p.func("closure", dom, bot);
        self.escaping.insert(label);

        let self_var = self.p.var(label);
        // The enclosing environment stays visible: references to it become
        // the closure's free variables.
        let mut inner = ctx.clone();
        inner.owner = None;
        inner.loops = vec![];
        inner.drop_stack = vec![];
        inner.initializing_self = None;
        let mut params = Vec::with_capacity(func.params.len());
        let mut prologue: Vec<(Symbol, ExprId)> = vec![];
        for (i, param) in func.params.iter().enumerate() {
            let extract = self.p.extract(self_var, i as u32);
            params.push(extract);
            if let Ok(symbol) = param.name.symbol() {
                if inner.cellable.contains(&symbol) {
                    prologue.push((symbol, extract));
                } else {
                    inner.env.insert(symbol, Binding::Value(extract));
                }
            }
        }
        inner.params = params;
        inner.ret_k = self.p.extract(self_var, func.params.len() as u32);
        inner.tail_k = inner.ret_k;
        inner.raw_ret_k = inner.ret_k;
        inner.normal_k = None;
        // A function value's call sites are indirect: they cannot thread
        // the abort linkage, so routed performs are rejected inside (and
        // it cannot resume an enclosing handler).
        inner.abort_ok = false;
        inner.resume_k = None;
        inner.top_level = false;
        inner.local_handlers = FxHashSet::default();
        let body_block = &func.body;
        let body = self.with_cells(&prologue, &mut inner, |this, inner| {
            let ret_k = inner.ret_k;
            this.lower_block(body_block, inner, ret_k)
        });
        self.p.set_body(label, body);
        Some(self.p.func_ref(label))
    }

    /// The callee's final declared parameter type (where a trailing block
    /// lands): for `Fn([params…, trailing, ret_k], ⊥)`, the
    /// second-to-last domain item.
    fn final_param_ty(&self, callee_ty: TyId) -> Option<TyId> {
        let TyKind::Fn(dom, _) = *self.p.ty_kind(callee_ty) else {
            return None;
        };
        match self.p.ty_kind(dom) {
            TyKind::Tuple(items) if items.len() >= 2 => Some(items[items.len() - 2]),
            _ => None,
        }
    }

    /// A trailing block: a closure over the enclosing environment. Its
    /// shape comes from the callee's declared parameter type (`expected`,
    /// a λ_G Fn type) — the checker already typed the block's arguments
    /// against it; without one (no parameters), the block's value type
    /// suffices.
    fn lower_block_closure(&mut self, block: &Block, expected: Option<TyId>, ctx: &Ctx) -> ExprId {
        let bot = self.p.ty_bot();
        let expected_dom = expected.and_then(|ty| match *self.p.ty_kind(ty) {
            TyKind::Fn(dom, _) => Some(dom),
            _ => None,
        });
        let dom = match expected_dom {
            Some(dom) => dom,
            _ => {
                if !block.args.is_empty() {
                    self.diagnostics.push(
                        "lowering: a parametered trailing block without a known callee parameter type"
                            .into(),
                    );
                }
                let ret_ty = block_value_ty(self, block, ctx);
                let ret_k_ty = self.p.ty_fn(ret_ty, bot);
                self.p.ty_tuple(&[ret_k_ty])
            }
        };
        let n_params = match self.p.ty_kind(dom) {
            TyKind::Tuple(items) => items.len().saturating_sub(1),
            _ => 0,
        };
        let label = self.p.func("trailing", dom, bot);
        self.escaping.insert(label);
        let self_var = self.p.var(label);
        let mut inner = ctx.clone();
        inner.owner = None;
        inner.loops = vec![];
        inner.drop_stack = vec![];
        inner.initializing_self = None;
        let mut params = Vec::with_capacity(n_params);
        let mut celled: Vec<(Symbol, ExprId)> = vec![];
        for (i, arg) in block.args.iter().enumerate().take(n_params) {
            let extract = self.p.extract(self_var, i as u32);
            params.push(extract);
            let Ok(symbol) = arg.name.symbol() else {
                continue;
            };
            if inner.cellable.contains(&symbol) {
                celled.push((symbol, extract));
            } else {
                inner.env.insert(symbol, Binding::Value(extract));
            }
        }
        inner.params = params;
        inner.ret_k = self.p.extract(self_var, n_params as u32);
        inner.tail_k = inner.ret_k;
        inner.raw_ret_k = inner.ret_k;
        inner.normal_k = None;
        inner.abort_ok = false;
        inner.resume_k = None;
        inner.top_level = false;
        inner.local_handlers = FxHashSet::default();
        let body = self.with_cells(&celled, &mut inner, |this, inner| {
            let ret_k = inner.ret_k;
            this.lower_block(block, inner, ret_k)
        });
        self.p.set_body(label, body);
        self.p.func_ref(label)
    }

    /// A call through a function VALUE (a local binding or a literal):
    /// apply the value's CPS function directly; the scheduler dispatches
    /// it indirectly.
    fn lower_value_call(
        &mut self,
        callee: &Expr,
        args: &[crate::node_kinds::call_arg::CallArg],
        trailing_block: Option<&Block>,
        ctx: &Ctx,
        k: ExprId,
    ) -> ExprId {
        let Some(callee_value) = self.try_pure(callee, ctx) else {
            self.diagnostics
                .push("lowering: computed callee expressions not yet supported".into());
            return self.dead_end("computed_callee");
        };
        let trailing_value = trailing_block.map(|b| {
            let expected = self.final_param_ty(self.p.expr_ty(callee_value));
            self.lower_block_closure(b, expected, ctx)
        });
        let arg_exprs: Vec<&Expr> = args.iter().map(|a| &a.value).collect();
        self.lower_args(&arg_exprs, ctx, vec![], &mut |this, mut values| {
            if let Some(trailing) = trailing_value {
                values.push(trailing);
            }
            values.push(k);
            let tuple = this.p.tuple(&values);
            this.p.app(callee_value, tuple)
        })
    }

    // ----- Calls -----------------------------------------------------------

    fn lower_call(
        &mut self,
        expr: &Expr,
        callee: &Expr,
        args: &[crate::node_kinds::call_arg::CallArg],
        trailing_block: Option<&Block>,
        ctx: &Ctx,
        k: ExprId,
    ) -> ExprId {
        // Calls through function VALUES — local bindings, function
        // literals, and function-typed record fields — dispatch
        // indirectly (M6 closures).
        let is_value_callee = matches!(&callee.kind, ExprKind::Func(_))
            || matches!(&callee.kind, ExprKind::Variable(name)
                if name.symbol().ok().is_some_and(|s| ctx.env.contains_key(&s)))
            || self.is_field_value_callee(callee, ctx);
        if is_value_callee {
            return self.lower_value_call(callee, args, trailing_block, ctx, k);
        }
        if let Some(done) =
            self.try_lower_existential_member_call(callee, args, trailing_block, ctx, k)
        {
            return done;
        }
        if let Some(done) =
            self.try_lower_local_evidence_member_call(callee, args, trailing_block, ctx, k)
        {
            return done;
        }

        // Resolve the target specialization.
        let target = self.resolve_callee(expr, callee, args, ctx);
        let Some((label, symbol, prefix)) = target else {
            return self.dead_end("unresolved_callee");
        };
        let trailing_value = trailing_block.map(|b| {
            let bot = self.p.ty_bot();
            let callee_ty = self.p.ty_fn(self.p.dom(label), bot);
            let expected = self.final_param_ty(callee_ty);
            self.lower_block_closure(b, expected, ctx)
        });
        // Abort-capable calls are handled by the MIR statement-spine
        // splitter; reaching one here means it sits in an expression
        // position the abort linkage cannot thread through yet.
        if self.abort_shape(symbol) {
            self.diagnostics.push(
                "lowering: a call that can abort in expression position (not yet supported)".into(),
            );
            return self.dead_end("abort_call_in_expression");
        }

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
            if let Some(trailing) = trailing_value {
                tuple_items.push(trailing);
            }
            tuple_items.push(k);
            let arg_tuple = this.p.tuple(&tuple_items);
            this.p.app(func_ref, arg_tuple)
        })
    }

    /// Shared tail for dispatching a protocol-requirement call through an
    /// erased witness: builds the CPS witness type from `signature`, lowers the
    /// trailing block and arguments, then assembles the call. `build_witness`
    /// produces the witness expression for the resolved receiver (and may
    /// rewrite `values[0]`, e.g. to repack a payload); returning `Err` aborts
    /// the call with that expression (a `dead_end`).
    #[allow(clippy::too_many_arguments)]
    fn lower_requirement_call(
        &mut self,
        receiver: &Expr,
        args: &[crate::node_kinds::call_arg::CallArg],
        trailing_block: Option<&Block>,
        ctx: &Ctx,
        k: ExprId,
        signature: CheckTy,
        not_a_function: &str,
        dead_end_label: &str,
        mut build_witness: impl FnMut(&mut Self, &mut Vec<ExprId>, TyId) -> Result<ExprId, ExprId>,
    ) -> Option<ExprId> {
        let CheckTy::Func(params, ret, _) = signature else {
            self.diagnostics.push(not_a_function.into());
            return Some(self.dead_end(dead_end_label));
        };
        let mut dom_items: Vec<TyId> = params.iter().map(|param| self.map_ty(param)).collect();
        let ret_ty = self.map_ty(&ret);
        let bot = self.p.ty_bot();
        let ret_k_ty = self.p.ty_fn(ret_ty, bot);
        dom_items.push(ret_k_ty);
        let dom = self.p.ty_tuple(&dom_items);
        let witness_ty = self.p.ty_fn(dom, bot);
        let trailing_value = trailing_block.map(|block| {
            let expected = self.final_param_ty(witness_ty);
            self.lower_block_closure(block, expected, ctx)
        });

        let mut arg_exprs: Vec<&Expr> = vec![receiver];
        arg_exprs.extend(args.iter().map(|arg| &arg.value));
        Some(
            self.lower_args(&arg_exprs, ctx, vec![], &mut |this, mut values| {
                let witness = match build_witness(this, &mut values, witness_ty) {
                    Ok(witness) => witness,
                    Err(early) => return early,
                };
                if let Some(trailing) = trailing_value {
                    values.push(trailing);
                }
                values.push(k);
                let tuple = this.p.tuple(&values);
                this.p.app(witness, tuple)
            }),
        )
    }

    fn try_lower_existential_member_call(
        &mut self,
        callee: &Expr,
        args: &[crate::node_kinds::call_arg::CallArg],
        trailing_block: Option<&Block>,
        ctx: &Ctx,
        k: ExprId,
    ) -> Option<ExprId> {
        let ExprKind::Member(Some(receiver), label, _) = &callee.kind else {
            return None;
        };
        let CheckTy::Any { protocol, assoc } = self.checker_ty(receiver, ctx) else {
            return None;
        };
        let label_str = label.to_string();
        let (owner, requirement) = self.units[ctx.unit]
            .types
            .catalog
            .requirement_in(protocol, &label_str)
            .map(|(owner, requirement)| (owner, requirement.clone()))?;
        let index =
            self.existential_requirement_index(protocol, &label_str, requirement.symbol, ctx.unit)?;
        let signature =
            self.erased_requirement_signature(protocol, &assoc, owner, &requirement, ctx.unit)?;
        self.lower_requirement_call(
            receiver,
            args,
            trailing_block,
            ctx,
            k,
            signature,
            "lowering: existential requirement is not a function",
            "existential_requirement",
            |this, values, witness_ty| {
                let receiver_value = values[0];
                Ok(this.p.primop(
                    Op::ExistentialWitness(index as u32),
                    &[receiver_value],
                    witness_ty,
                ))
            },
        )
    }

    fn try_lower_local_evidence_member_call(
        &mut self,
        callee: &Expr,
        args: &[crate::node_kinds::call_arg::CallArg],
        trailing_block: Option<&Block>,
        ctx: &Ctx,
        k: ExprId,
    ) -> Option<ExprId> {
        let ExprKind::Member(Some(receiver), label, _) = &callee.kind else {
            return None;
        };
        let CheckTy::Param(param) = self.checker_ty(receiver, ctx) else {
            return None;
        };
        let resolution = self.units[ctx.unit]
            .types
            .member_resolutions
            .get(&callee.id)
            .cloned();
        let protocol = match resolution {
            Some(crate::types::output::MemberResolution::ViaConformance { protocol, .. }) => {
                protocol
            }
            _ => return None,
        };
        let evidence = self.local_evidence_for(ctx, param, protocol)?;
        let label_str = label.to_string();
        let (owner, requirement) = self.units[ctx.unit]
            .types
            .catalog
            .requirement_in(protocol, &label_str)
            .map(|(owner, requirement)| (owner, requirement.clone()))?;
        let source_requirements = self.units[ctx.unit]
            .types
            .catalog
            .requirements_for_conformance(evidence.protocol);
        let index = source_requirements
            .iter()
            .position(|(_, _, source)| source.symbol == requirement.symbol)?;
        let signature =
            self.erased_requirement_signature(protocol, &[], owner, &requirement, ctx.unit)?;
        self.lower_requirement_call(
            receiver,
            args,
            trailing_block,
            ctx,
            k,
            signature,
            "lowering: local-evidence requirement is not a function",
            "local_evidence_requirement",
            |this, values, _witness_ty| {
                let payload = values[0];
                let Some(package) =
                    this.existential_pack_from_local_evidence(protocol, &[], param, payload, ctx)
                else {
                    return Err(this.dead_end("local_evidence_pack"));
                };
                values[0] = package;
                Ok(this.p.extract(evidence.table, index as u32))
            },
        )
    }

    /// The write-back adapter for a mutating-method call: receives
    /// [result, Self], writes Self back through the receiver's assignment
    /// target, and passes the result on (the "caller performs the
    /// write-back" half of inout — Racordon et al., JOT 2022).
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
        let (cell, path) = self.assignment_target(receiver, ctx)?;

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
        let stored = self.rebuilt_assignment_value(cell, &path, new_self);

        let after = self.p.func("after_writeback", void_ty, bot);
        let after_body = self.p.app(k, result);
        self.p.set_body(after, after_body);
        let after_ref = self.p.func_ref(after);

        let cell_set = self.p.primop(Op::CellSet, &[cell, stored], void_ty);
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
                let mut theta = self.call_theta(init, expr.id, ctx);
                let constructed = self.checker_ty(expr, ctx);
                self.owner_theta(init, &constructed, &mut theta);
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
                let head_ty = head_expr.map(|h| Self::borrow_erased_ty(self.checker_ty(h, ctx)));
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
                        let mut theta = self.call_theta(member, callee.id, ctx);
                        if let Some(head) = &head_ty {
                            self.owner_theta(member, head, &mut theta);
                        }
                        Some((self.demand(member, theta), member, prefix))
                    }
                    None => {
                        // No resolution at this node: the member use rode
                        // its binder's scheme (qualified types — Jones
                        // 1994) and the checker discharged it per call
                        // site. The θ-substituted head is concrete here,
                        // so resolve the label the way the solver's
                        // try_member does: the type's own methods first,
                        // then protocol witnesses.
                        if let Some(CheckTy::Nominal(symbol, _)) = &head_ty {
                            let label_str = label.to_string();
                            let catalog = &self.units[self.entry].types.catalog;
                            let method = catalog
                                .structs
                                .get(symbol)
                                .and_then(|i| i.methods.get(&label_str))
                                .or_else(|| {
                                    catalog
                                        .enums
                                        .get(symbol)
                                        .and_then(|i| i.methods.get(&label_str))
                                })
                                .copied();
                            if let Some(member) = method {
                                let head = head_ty.clone()?;
                                let mut theta = self.call_theta(member, callee.id, ctx);
                                self.owner_theta(member, &head, &mut theta);
                                return Some((self.demand(member, theta), member, prefix));
                            }
                            let protocols: Vec<Symbol> = catalog
                                .member_owners
                                .get(&label_str)
                                .into_iter()
                                .flatten()
                                .filter_map(|owner| match owner {
                                    crate::types::catalog::MemberOwner::Protocol(p) => Some(*p),
                                    _ => None,
                                })
                                .filter(|p| {
                                    catalog.conformances.contains_key(&(*symbol, *p))
                                        || self
                                            .units
                                            .iter()
                                            .any(|u| u.types.catalog.derivable.contains(p))
                                })
                                .collect();
                            for protocol in protocols {
                                let Some((_, requirement)) = self.units[self.entry]
                                    .types
                                    .catalog
                                    .requirement_in(protocol, &label_str)
                                else {
                                    continue;
                                };
                                let witness = requirement.symbol;
                                let head = head_ty.clone()?;
                                if let Some((target, target_symbol)) = self.resolve_witness(
                                    protocol,
                                    witness,
                                    label_str.clone(),
                                    &head,
                                ) {
                                    return Some((target, target_symbol, prefix));
                                }
                            }
                        }
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
        let CheckTy::Nominal(head_symbol, head_args) = head else {
            self.diagnostics.push(format!(
                "lowering: protocol dispatch on non-nominal head {head:?} (not yet supported)"
            ));
            return None;
        };
        let catalog = &self.units[self.entry].types.catalog;
        let conformance = catalog.conformances.get(&(*head_symbol, protocol)).cloned();

        if let Some(conformance) = conformance {
            // Bind the row's rigid params against the concrete head args —
            // the same binding the solver performed at discharge (instances
            // with contexts, Hall et al., TOPLAS 1996; the context itself
            // needs no re-check: the checker proved it).
            let mut row_theta = Theta::default();
            for (pattern, actual) in conformance.self_args.iter().zip(head_args) {
                crate::types::solve::bind_param_pattern(pattern, actual, &mut row_theta);
            }
            if let Some(&witness) = conformance.witnesses.get(&label) {
                return Some((self.demand(witness, row_theta), witness));
            }
            // Default body: specialize at Self := head, with the
            // conformance's associated bindings (substituted through the
            // row's params for conditional rows).
            let mut theta = Theta::default();
            theta.insert(protocol, head.clone());
            for (assoc, ty) in &conformance.assoc {
                let bound = ty.substitute(&row_theta, &Default::default(), &Default::default());
                theta.insert(*assoc, bound);
            }
            return Some((
                self.demand(requirement_or_witness, theta),
                requirement_or_witness,
            ));
        }
        // No explicit row: an auto-derived protocol (today: Showable)
        // synthesizes its witness in λ_G — the checker discharged the
        // conformance structurally (`solve/conformance.rs::try_derive`).
        let derivable = self
            .units
            .iter()
            .any(|u| u.types.catalog.derivable.contains(&protocol));
        if derivable
            && label == "show"
            && let Some(synth) = self.demand_derived_show(protocol, requirement_or_witness, head)
        {
            return Some((synth, requirement_or_witness));
        }
        self.diagnostics.push(format!(
            "lowering: no conformance ({head_symbol}, {protocol}) for '{label}'"
        ));
        None
    }

    // ----- Effects ------------------------------------------------------------

    /// A diagnosed, abandoned path: a call to a bodyless function. The
    /// scheduler emits the missing body as a `Trap`, the evaluator
    /// reports `UnsetBody` — honest if ever reached, and well-typed no
    /// matter what the abandoned expression's continuation expects
    /// (delivering `void` to an arbitrary continuation is ill-typed and
    /// trips the λ_G constructor's T-App check).
    fn dead_end(&mut self, why: &str) -> ExprId {
        let void_ty = self.p.ty_void();
        let bot = self.p.ty_bot();
        let dead = self.p.func(why, void_ty, bot);
        let dead_ref = self.p.func_ref(dead);
        let void = self.p.void();
        self.p.app(dead_ref, void)
    }

    /// One unhandled perform: `'io(.sleep(ms))` and friends. The request
    /// must be a syntactic variant construction so the operation routes
    /// statically; its payloads become the primop's operands.
    fn lower_perform(
        &mut self,
        expr: &Expr,
        effect_name: &crate::name::Name,
        args: &[crate::node_kinds::call_arg::CallArg],
        ctx: &Ctx,
        k: ExprId,
    ) -> ExprId {
        let ret_ty = effect_name
            .symbol()
            .ok()
            .and_then(|symbol| {
                self.units
                    .iter()
                    .find_map(|u| u.types.catalog.effects.get(&symbol).cloned())
            })
            .map(|sig| self.map_ty(&sig.ret));
        let Some(ret_ty) = ret_ty else {
            self.diagnostics
                .push("lowering: perform of an undeclared effect".into());
            return self.dead_end("undeclared_effect");
        };

        // The request expression: a leading-dot variant construction.
        let operation = args.first().and_then(|request| match &request.value.kind {
            ExprKind::Call {
                callee,
                args: payloads,
                ..
            } => {
                let (enum_symbol, tag, _, _) = self.variant_target(&request.value, callee, ctx)?;
                let name = self
                    .enum_info(enum_symbol)?
                    .variants
                    .get_index(tag as usize)
                    .map(|(name, _)| name.clone())?;
                Some((name, payloads.as_slice()))
            }
            _ => None,
        });
        let Some((operation, payloads)) = operation else {
            self.diagnostics.push(
                "lowering: perform with a computed request (not yet supported — operations route statically)"
                    .into(),
            );
            return self.dead_end("computed_request");
        };

        let op = match operation.as_str() {
            "read" => Op::IoRead,
            "write" => Op::IoWrite,
            "open" => Op::IoOpen,
            "close" => Op::IoClose,
            "sleep" => Op::IoSleep,
            "poll" => Op::IoPoll,
            "ctl" => Op::IoCtl,
            "socket" => Op::IoSocket,
            "bind" => Op::IoBind,
            "listen" => Op::IoListen,
            "connect" => Op::IoConnect,
            "accept" => Op::IoAccept,
            other => {
                self.diagnostics
                    .push(format!("lowering: unknown io operation '{other}'"));
                return self.dead_end("unknown_io_operation");
            }
        };
        let _ = expr;
        let payload_exprs: Vec<&Expr> = payloads.iter().map(|a| &a.value).collect();
        self.lower_args(&payload_exprs, ctx, vec![], &mut |this, values| {
            let result = this.p.primop(op, &values, ret_ty);
            this.p.app(k, result)
        })
    }

    // ----- Lexical effect handlers (M7: aborts) -----------------------------

    /// The result type carried by an abort-capable function's
    /// normal-return continuation (`Fn([result, slot], ⊥)` → result).
    fn normal_result_ty(&mut self, normal_k: ExprId) -> TyId {
        let normal_k_ty = self.p.expr_ty(normal_k);
        if let TyKind::Fn(pair_ty, _) = *self.p.ty_kind(normal_k_ty)
            && let TyKind::Tuple(items) = self.p.ty_kind(pair_ty)
            && items.len() == 2
        {
            return items[0];
        }
        self.diagnostics
            .push("lowering: abort-capable function without a paired normal return".into());
        self.p.ty_void()
    }

    /// Clone a context for code that moves into an escaping closure: `rk`,
    /// the closure's own return slot, replaces the function's return
    /// linkage, and normal completions are re-pointed at it — directly, or
    /// through the enclosing abort-capable function's normal-return
    /// parameter (which the closure captures as an ordinary value).
    fn rebase_into_closure(&mut self, ctx: &Ctx, rk: ExprId) -> Ctx {
        let mut inner = ctx.clone();
        inner.loops = vec![];
        inner.raw_ret_k = rk;
        inner.ret_k = match ctx.normal_k {
            None => rk,
            Some(normal_k) => {
                let result_ty = self.normal_result_ty(normal_k);
                let bot = self.p.ty_bot();
                let wrap = self.p.func("ret_normal", result_ty, bot);
                let value = self.p.var(wrap);
                let pair = self.p.tuple(&[value, rk]);
                let body = self.p.app(normal_k, pair);
                self.p.set_body(wrap, body);
                self.p.func_ref(wrap)
            }
        };
        inner.tail_k = inner.ret_k;
        inner
    }

    /// A perform routed to a lexical handler: call the capability with
    /// the payloads and our own return slot. The handler's value rides
    /// the Ret chain back through every frame between here and the
    /// handled scope's caller; nothing after the perform is emitted on
    /// this path (the effect returns Never).
    fn lower_routed_perform(
        &mut self,
        handler_sym: Symbol,
        args: &[crate::node_kinds::call_arg::CallArg],
        ctx: &Ctx,
        k: ExprId,
    ) -> ExprId {
        if !ctx.abort_ok && !ctx.local_handlers.contains(&handler_sym) {
            self.diagnostics
                .push("lowering: perform inside a function value (not yet supported)".into());
            let _ = k;
            return self.dead_end("perform_in_function_value");
        }
        let Some(cap) = self.handler_caps.get(&handler_sym).copied() else {
            self.diagnostics.push(
                "lowering: perform reached before its handler was installed (not yet supported)"
                    .into(),
            );
            return self.dead_end("perform_before_handler");
        };
        // Resumable performs are handled by the MIR statement-spine
        // splitter, where the rest of the block can become the
        // resumption; reaching one here means it sits in an expression
        // position the split cannot reach yet.
        if cap.resume_pair_ty.is_some() {
            self.diagnostics.push(
                "lowering: a resumable perform in expression position (not yet supported)".into(),
            );
            return self.dead_end("resumable_perform_in_expression");
        }
        let slot = ctx.raw_ret_k;
        let arg_exprs: Vec<&Expr> = args.iter().map(|a| &a.value).collect();
        self.lower_args(&arg_exprs, ctx, vec![], &mut |this, mut values| {
            values.push(slot);
            let tuple = this.p.tuple(&values);
            this.p.app(cap.cap, tuple)
        })
    }

    /// Is this expression a direct call to an abort-capable function?
    fn abortable_callee(&self, expr: &Expr, ctx: &Ctx) -> Option<Symbol> {
        let ExprKind::Call { callee, .. } = &expr.kind else {
            return None;
        };
        let ExprKind::Variable(name) = &callee.kind else {
            return None;
        };
        let symbol = name.symbol().ok()?;
        if ctx.env.contains_key(&symbol) {
            return None;
        }
        self.abort_shape(symbol).then_some(symbol)
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
                // `alloc T count`: count elements of T, sized by
                // TyKind::mem_size (Op::Alloc itself counts bytes). An
                // element the checker left unconstrained (`_alloc(n)`
                // with nothing loading or storing through it — the raw
                // buffers of ChatServer and friends) is a byte buffer:
                // map_ty would default the residual variable to Void,
                // which cannot live in memory.
                let unconstrained = matches!(&ty.kind, TypeAnnotationKind::Nominal { name, .. }
                    if name.symbol().is_ok_and(|s| matches!(ctx.theta.get(&s), Some(CheckTy::Var(_)))));
                let element = if unconstrained {
                    self.p.ty(TyKind::Byte)
                } else {
                    self.splice_ty(ty, ctx)?
                };
                let Some(size) = self.p.ty_kind(element).mem_size() else {
                    self.diagnostics
                        .push("lowering: alloc element type cannot live in memory".into());
                    return None;
                };
                let count = operand(self, count)?;
                let bytes = if size == 1 {
                    count
                } else {
                    let size = self.p.int(size as i64);
                    self.p.mul(count, size)
                };
                (Op::Alloc, vec![bytes])
            }
            K::Load { ty, addr, .. } => {
                let result = self.splice_ty(ty, ctx)?;
                let ptr = operand(self, addr)?;
                return Some(self.p.primop(Op::Load, &[ptr], result));
            }
            // `store T $value $addr`: one sized write; the width comes
            // from the value's λ_G type at the engines.
            K::Store { value, addr, .. } => {
                (Op::Store, vec![operand(self, addr)?, operand(self, value)?])
            }
            // `%? = gep T $addr $index`: pure pointer arithmetic —
            // addr + index · size(T) (no runtime op needed).
            K::Gep {
                ty,
                addr,
                offset_index,
                ..
            } => {
                let element = self.splice_ty(ty, ctx)?;
                let Some(size) = self.p.ty_kind(element).mem_size() else {
                    self.diagnostics
                        .push("lowering: gep element type cannot live in memory".into());
                    return None;
                };
                let addr = operand(self, addr)?;
                let index = operand(self, offset_index)?;
                let offset = if size == 1 {
                    index
                } else {
                    let size = self.p.int(size as i64);
                    self.p.mul(index, size)
                };
                return Some(self.p.add(addr, offset));
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
        };
        let result_ty = match op {
            Op::Cmp(_) => self.p.ty_bool(),
            Op::Trunc => self.p.ty_i64(),
            Op::IToF => self.p.ty_f64(),
            Op::Alloc => self.p.ty_ptr(),
            Op::Copy | Op::Store | Op::Free => self.p.ty_void(),
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
        let substituted = raw.substitute(&ctx.theta, &Default::default(), &Default::default());
        self.normalize_check_ty(substituted, ctx.unit)
    }

    fn borrow_erased_ty(ty: CheckTy) -> CheckTy {
        match ty {
            CheckTy::Borrow(_, inner) => *inner,
            other => other,
        }
    }

    fn normalize_check_ty(&self, ty: CheckTy, unit: usize) -> CheckTy {
        CheckNormalizer {
            catalog: &self.units[unit].types.catalog,
        }
        .fold_ty(&ty)
    }

    fn expr_lambda_ty(&mut self, expr: &Expr, ctx: &Ctx) -> TyId {
        let ty = self.checker_ty(expr, ctx);
        self.map_ty(&ty)
    }

    /// θ contribution from a member's owner: a method/init of a generic
    /// struct (or an inherent extend member) ranges over its owner's rigid
    /// params, which the checker discharges by head substitution rather
    /// than scheme instantiation (`solve/member.rs::try_member`) — so no
    /// instantiation is recorded. Recover the same bindings by matching
    /// the declared self type against the concrete head. Existing θ
    /// entries win.
    fn owner_theta(&self, member: Symbol, head: &CheckTy, theta: &mut Theta) {
        let CheckTy::Nominal(head_symbol, args) = head else {
            return;
        };
        for unit in &self.units {
            let catalog = &unit.types.catalog;
            if let Some(info) = catalog.structs.get(head_symbol) {
                let owns = info.methods.values().any(|s| *s == member)
                    || info.statics.values().any(|s| *s == member)
                    || info.inits.contains(&member);
                if owns {
                    for (param, arg) in info.params.iter().zip(args) {
                        theta.entry(*param).or_insert_with(|| arg.clone());
                    }
                    return;
                }
            }
            if let Some(info) = catalog.enums.get(head_symbol)
                && info.methods.values().any(|s| *s == member)
            {
                for (param, arg) in info.params.iter().zip(args) {
                    theta.entry(*param).or_insert_with(|| arg.clone());
                }
                return;
            }
            if let Some(members) = catalog.extend_members.get(head_symbol)
                && let Some(m) = members.values().find(|m| m.symbol == member)
            {
                for (pattern, actual) in m.self_args.iter().zip(args) {
                    crate::types::solve::bind_param_pattern(pattern, actual, theta);
                }
                return;
            }
        }
    }

    /// The full θ for a call to `symbol`: per-call-site instantiation
    /// composed with the enclosing θ; scheme params with no recorded
    /// instantiation (monomorphic recursion typed against the group's
    /// skeleton — THIH §11.6.3) inherit the enclosing specialization's
    /// binding.
    fn call_theta(&self, symbol: Symbol, node: crate::node_id::NodeID, ctx: &Ctx) -> Theta {
        let mut theta = self.instantiation_at(node, ctx);
        if let Some(scheme) = self.units.iter().find_map(|u| u.types.schemes.get(&symbol)) {
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
                } else if self.is_enum(*symbol) {
                    // Enums are tagged variants; type arguments are erased
                    // (monomorphization already specialized every use).
                    self.p.ty(TyKind::Variant(*symbol))
                } else {
                    self.p.ty(TyKind::Boxed(*symbol))
                }
            }
            CheckTy::Borrow(_, inner) => self.map_ty(inner),
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
            // A closed record row is a tuple in the row's field order
            // (`Row::closed` sorts by label, so the layout is canonical —
            // Leijen's scoped labels, Trends in FP 2005, fixed to closed
            // rows until row polymorphism reaches the backend).
            CheckTy::Record(row) if row.tail.is_none() => {
                let field_tys: Vec<CheckTy> = row.fields.iter().map(|(_, t)| t.clone()).collect();
                let mapped: Vec<TyId> = field_tys.iter().map(|t| self.map_ty(t)).collect();
                self.p.ty_tuple(&mapped)
            }
            CheckTy::Any { protocol, .. } => self.p.ty(TyKind::Existential(*protocol)),
            CheckTy::Param(_) => self.p.ty(TyKind::Erased),
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
    /// final top-level expression (the program/REPL value). When the
    /// program defines an explicit `func main`, it runs *after* the
    /// top-level statements and its value is the program's value.
    fn lower_main(&mut self) -> (Label, TyId) {
        let unit = self.entry;
        let mut nodes: Vec<Node> = vec![];
        let mut explicit_main: Option<Symbol> = None;
        for ast in self.units[unit].asts.values() {
            for root in &ast.roots {
                match root {
                    Node::Stmt(_) => nodes.push(root.clone()),
                    Node::Decl(decl) => {
                        // Non-func top-level lets execute in main, in order.
                        if let DeclKind::Let {
                            lhs,
                            rhs: Some(rhs),
                            ..
                        } = &decl.kind
                        {
                            if !matches!(rhs.kind, ExprKind::Func(_)) {
                                nodes.push(root.clone());
                            } else if let PatternKind::Bind(name) = &lhs.kind
                                && name.name_str() == "main"
                                && let Ok(symbol) = name.symbol()
                            {
                                explicit_main = Some(symbol);
                            }
                        }
                    }
                    _ => {}
                }
            }
        }
        if let Some(symbol) = explicit_main {
            return self.lower_main_with_entry(unit, symbol, nodes);
        }

        // The program value type: the FINAL node's value — an expression
        // statement's type, a block-final if/else's branch type, and Void
        // for everything else (a trailing loop or declaration yields
        // nothing; scanning past it to an earlier expression mistypes
        // main's return).
        let result_check_ty = self
            .top_level_value_ty(unit, nodes.last())
            .unwrap_or(CheckTy::Nominal(Symbol::Void, vec![]));
        let result_ty = self.map_ty(&result_check_ty);

        let bot = self.p.ty_bot();
        let ret_k_ty = self.p.ty_fn(result_ty, bot);
        let dom = self.p.ty_tuple(&[ret_k_ty]);
        let main = self.p.func("main", dom, bot);
        self.p.name_params(main, &["k"]);
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
            owner: None,
            theta: Theta::default(),
            env: FxHashMap::default(),
            local_evidence: FxHashMap::default(),
            ret_k,
            tail_k: ret_k,
            raw_ret_k: ret_k,
            normal_k: None,
            // Performs directly in main abort straight to its return.
            abort_ok: true,
            resume_k: None,
            top_level: true,
            local_handlers: FxHashSet::default(),
            params: vec![],
            loops: vec![],
            drop_stack: vec![],
            drop_flags: FxHashMap::default(),
            initializing_self: None,
            cellable,
        };
        let body = self.lower_main_nodes(&nodes, &ctx, ret_k);
        self.p.set_body(main, body);
        (main, result_ty)
    }

    /// Like lower_nodes, but the final expression's value goes to ret_k.
    fn lower_main_nodes(&mut self, nodes: &[Node], ctx: &Ctx, k: ExprId) -> ExprId {
        let body = mir::build_nodes(self.units[ctx.unit].types, nodes);
        self.lower_mir_body(&body, ctx, k)
    }

    /// The checker type of a top-level block's final value: the last
    /// node's expression type (or the branch type of a block-final
    /// if/else); None for statements that yield nothing.
    fn top_level_value_ty(&self, unit: usize, last: Option<&Node>) -> Option<CheckTy> {
        match last? {
            Node::Stmt(Stmt {
                kind: StmtKind::Expr(expr),
                ..
            }) => self.units[unit].types.node_types.get(&expr.id).cloned(),
            Node::Stmt(Stmt {
                kind: StmtKind::If(_, then_block, Some(_)),
                ..
            }) => then_block.body.iter().next_back().and_then(|n| match n {
                Node::Stmt(Stmt {
                    kind: StmtKind::Expr(e),
                    ..
                })
                | Node::Expr(e) => self.units[unit].types.node_types.get(&e.id).cloned(),
                _ => None,
            }),
            _ => None,
        }
    }

    /// An explicit `func main` entrypoint: top-level statements run in
    /// source order (initialization), then main is called; its value is
    /// the program's value.
    fn lower_main_with_entry(
        &mut self,
        unit: usize,
        symbol: Symbol,
        nodes: Vec<Node>,
    ) -> (Label, TyId) {
        let entry_label = self.demand(symbol, Theta::default());
        if self.abort_shape(symbol) {
            self.diagnostics.push(
                "lowering: main performing into a lexical handler (not yet supported)".into(),
            );
        }
        let result_ty = match self.signature_of(symbol, &Theta::default()) {
            Some(CheckTy::Func(params, ret, _)) => {
                if !params.is_empty() {
                    self.diagnostics
                        .push("lowering: main must take no parameters".into());
                }
                self.map_ty(&ret)
            }
            _ => {
                self.diagnostics
                    .push("lowering: main is not a function".into());
                self.p.ty_void()
            }
        };

        let bot = self.p.ty_bot();
        let ret_k_ty = self.p.ty_fn(result_ty, bot);
        let dom = self.p.ty_tuple(&[ret_k_ty]);
        let main = self.p.func("main", dom, bot);
        self.p.name_params(main, &["k"]);
        let main_var = self.p.var(main);
        let ret_k = self.p.extract(main_var, 0);

        let mut cellable: FxHashSet<Symbol> = FxHashSet::default();
        cellable.extend(self.units[unit].resolved.mutated_symbols.iter().copied());
        for node in &nodes {
            cellable.extend(self.cellable_symbols(unit, node));
        }
        let ctx = Ctx {
            unit,
            owner: None,
            theta: Theta::default(),
            env: FxHashMap::default(),
            local_evidence: FxHashMap::default(),
            ret_k,
            tail_k: ret_k,
            raw_ret_k: ret_k,
            normal_k: None,
            abort_ok: true,
            resume_k: None,
            top_level: true,
            local_handlers: FxHashSet::default(),
            params: vec![],
            loops: vec![],
            drop_stack: vec![],
            drop_flags: FxHashMap::default(),
            initializing_self: None,
            cellable,
        };

        // call_main: the top-level statements' value is discarded, then
        // main delivers the program value.
        let void_ty = self.p.ty_void();
        let call_main = self.p.func("call_main", void_ty, bot);
        let entry_ref = self.p.func_ref(entry_label);
        let args = self.p.tuple(&[ret_k]);
        let call = self.p.app(entry_ref, args);
        self.p.set_body(call_main, call);
        let call_main_ref = self.p.func_ref(call_main);

        let setup_value_ty = self
            .top_level_value_ty(unit, nodes.last())
            .map(|ty| self.map_ty(&ty))
            .unwrap_or(void_ty);
        let k = self.discarding_cont(setup_value_ty, call_main_ref);
        let body = self.lower_main_nodes(&nodes, &ctx, k);
        self.p.set_body(main, body);
        (main, result_ty)
    }
}

/// The λ_G type of a block's value, from the checker's view of its final
/// expression (Void when the block ends in a non-expression).
fn block_value_ty(lowering: &mut Lowering, block: &Block, ctx: &Ctx) -> TyId {
    // Only the FINAL node carries the block's value: a trailing
    // statement (assignment, loop, declaration) yields Void — scanning
    // past it to an earlier expression mistypes the continuation.
    let last_expr = match block.body.last() {
        Some(Node::Stmt(Stmt {
            kind: StmtKind::Expr(e),
            ..
        }))
        | Some(Node::Expr(e)) => Some(e),
        _ => None,
    };
    match last_expr {
        Some(e) => lowering.expr_lambda_ty(e, ctx),
        None => lowering.p.ty_void(),
    }
}

fn receiver_root_symbol(expr: &Expr) -> Option<Symbol> {
    match &expr.kind {
        ExprKind::Variable(name) => name.symbol().ok(),
        ExprKind::Member(Some(receiver), ..) => receiver_root_symbol(receiver),
        _ => None,
    }
}

/// Post-solve associated-type normalization over `CheckTy` (a bottom-up
/// `TyFold`): recurse children first, then reduce a projection whose base is a
/// concrete nominal through the conformance table. Catalog-only — the solver's
/// `VarStore` is gone by lowering time.
struct CheckNormalizer<'a> {
    catalog: &'a crate::types::catalog::TypeCatalog,
}

impl TyFold for CheckNormalizer<'_> {
    fn fold_ty(&mut self, ty: &CheckTy) -> CheckTy {
        let rebuilt = self.fold_children(ty);
        let CheckTy::Proj(base, protocol, assoc) = &rebuilt else {
            return rebuilt;
        };
        let CheckTy::Nominal(symbol, args) = base.as_ref() else {
            return rebuilt;
        };
        match crate::types::solve::reduce_projection(self.catalog, *symbol, args, *protocol, *assoc)
        {
            Some(reduced) => self.fold_ty(&reduced),
            None => rebuilt,
        }
    }

    fn fold_eff(&mut self, eff: &crate::types::ty::EffectRow) -> crate::types::ty::EffectRow {
        eff.clone()
    }
}
