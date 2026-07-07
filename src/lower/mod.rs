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

mod calls;
mod closures;
mod demand;
mod derive;
mod effects;
mod functions;
pub mod lower_tests;
mod matches;
pub(crate) mod mir;
mod mir_lowering;
mod patterns;
mod splices;
mod statements;
mod theta;
mod values;

use indexmap::IndexMap;
use rustc_hash::{FxHashMap, FxHashSet};

use crate::compiling::driver::Source;
use crate::flow::Place;
use crate::lambda_g::expr::Const;
use crate::lambda_g::expr::{CmpOp, ExprId, Op, TyId, TyKind};
use crate::lambda_g::program::{Label, Program};
use crate::name_resolution::name_resolver::ResolvedNames;
use crate::name_resolution::symbol::Symbol;
use crate::node_kinds::{
    inline_ir_instruction::{InlineIRInstructionKind, Value as IrValue},
    type_annotation::{TypeAnnotation, TypeAnnotationKind},
};
use crate::token_kind::TokenKind;
use crate::typed_ast::{
    self, Block, Decl, DeclKind, Expr, ExprKind, InlineIRInstruction, MatchArm, Node, PatternKind,
    Stmt, StmtKind, TypedFile,
};
use crate::types::TypeOutput;
use crate::types::ty::Ty as CheckTy;
use crate::types::ty::{ProtocolRef, TyFold};

pub(crate) struct LowerUnit<'a> {
    pub asts: &'a IndexMap<Source, TypedFile>,
    pub types: &'a TypeOutput,
    pub resolved: &'a ResolvedNames,
    /// The module's flow-checked MIR bodies, built behind `mir::build_checked`.
    pub bodies: &'a mir::CheckedMir,
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
    params: &'a [crate::typed_ast::Parameter],
    body: &'a Block,
}

/// The per-instantiation meaning of a tier-2 auto-clone mark.
enum AutoClone {
    Retain,
    Nothing,
    Unsupported(CheckTy),
}

pub struct Lowering<'a> {
    units: Vec<LowerUnit<'a>>,
    entry: usize,
    pub p: Program,
    sources: FxHashMap<Symbol, FuncSource<'a>>,
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
    /// Synthesized finalizer thunks per `'heap` instantiation.
    finalizer_thunks: FxHashMap<(Symbol, ThetaKey), Label>,
    queue: Vec<(Symbol, Theta, Label)>,
    /// Function values (literals, trailing blocks): they are called
    /// indirectly, so the scheduler gives each its own chunk and closure
    /// environment (unknown occurrences — the closure-conversion criterion
    /// of flat closures, Cardelli 1984).
    escaping: FxHashSet<Label>,
    /// Named local funcs' labels, minted before their bodies lower (per
    /// enclosing instantiation): block hoisting binds every func-valued
    /// binder of a block up front, so local funcs can call themselves
    /// and each other regardless of declaration order.
    local_func_labels: FxHashMap<(Symbol, ThetaKey), Label>,
    /// Cells of mutable top-level bindings: functions that read or assign
    /// them reference the cell directly (a free variable of main; the
    /// closure machinery carries it, exactly like handler capabilities).
    top_level_cells: FxHashMap<Symbol, ExprId>,
    /// One checked MIR body per typed block: fetched from the unit's store on
    /// first lowering, shared by every later lowering of the same block (each
    /// θ-specialization of a generic function re-lowers its body but must not
    /// rebuild its MIR).
    checked_bodies: FxHashMap<(usize, crate::node_id::NodeID), std::sync::Arc<mir::Body>>,
    /// Stack of bodies being lowered (innermost last): expression lowering
    /// resolves expression-position constructs' scaffold blocks against the
    /// innermost entry.
    scaffold_ctx: Vec<ScaffoldCtx>,
    /// Installed `@handle`s awaiting instantiation (indexed by
    /// `Ctx::cap_templates`); capability closures materialize from them
    /// per demanded instantiation, memoized in `materialized_caps`.
    handler_templates: Vec<HandlerTemplate>,
    materialized_caps: FxHashMap<(usize, Vec<CheckTy>), ExprId>,
    pub diagnostics: Vec<String>,
}

/// A lowered `@handle`, held as a template: the capability closure is
/// materialized per effect instantiation demanded inside its extent,
/// specializing the handler body with the effect's generics bound —
/// the generic-function θ machinery applied to a handler block
/// (docs/generic-effects-plan.md).
struct HandlerTemplate {
    effect: Symbol,
    /// The `Handling` statement's id — the scaffold key for the handler
    /// body's blocks in `scaffold`.
    handling_id: crate::node_id::NodeID,
    scaffold: std::sync::Arc<mir::Body>,
    /// Handler parameters, kept for argument names and cell conversion.
    handler_args: Vec<typed_ast::Parameter>,
    /// The installing frame's context: the delimiter (`raw_ret_k`) and
    /// environment the materialized closure captures.
    install_ctx: Ctx,
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
    key_path: Place,
    ty: CheckTy,
    dynamic_flags: Vec<Place>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
struct LoopBinding {
    header: ExprId,
    exit: ExprId,
    drop_depth: usize,
}

/// A variant constructor's call site, carried from `variant_target` into
/// evidence-table generation: the node (for diagnostics) and its per-call-site
/// instantiation (the θ source, baked on the typed node by the builder).
#[derive(Clone)]
struct VariantSite {
    node: crate::node_id::NodeID,
    instantiation: Option<Vec<(Symbol, CheckTy)>>,
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
    /// MIR temporaries in scope: a flattened construct's value, bound by
    /// its join continuation (`ExprKind::Temp` resolves here).
    temps: FxHashMap<u32, ExprId>,
    /// The current function's return continuation (a Fn(R, ⊥) value).
    ret_k: ExprId,
    /// The continuation currently representing normal fallthrough to the
    /// function tail. This may be a drop wrapper around `ret_k`.
    tail_k: ExprId,
    /// The current λ_G function's own machine-return slot, untouched by
    /// the init/inout wrappers layered onto `ret_k`. A `@handle` installed
    /// here captures it as its capability's delimiter: an aborting handler
    /// finishes into it directly, running no user code in the frames
    /// between the perform and this scope (ADR 0011).
    raw_ret_k: ExprId,
    /// Inside a resuming handler's capability closure: its resumption
    /// parameter. `continue v` tail-transfers into it. Cleared in
    /// nested function values (they cannot resume).
    resume_k: Option<ExprId>,
    /// Lowering main's top-level statements: cellable lets register in
    /// `top_level_cells` so functions can capture them.
    top_level: bool,
    /// Capability VALUES in scope, keyed by (effect, instantiation): our
    /// own capability parameters. A perform or call needing one of these
    /// exact instantiations uses the value directly.
    caps: FxHashMap<(Symbol, Vec<CheckTy>), ExprId>,
    /// Capability TEMPLATES in scope, by effect label: installed by
    /// `@handle` for the rest of its block. A needed instantiation not
    /// present in `caps` materializes a capability closure from the
    /// nearest template (label-scoped: one `@handle` covers every
    /// instantiation of its effect — docs/generic-effects-plan.md).
    cap_templates: FxHashMap<Symbol, usize>,
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
    drop_flags: FxHashMap<Place, ExprId>,
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
    resume_k: Option<ExprId>,
    top_level: bool,
    caps: Vec<((Symbol, Vec<CheckTy>), ExprId)>,
    cap_templates: Vec<(Symbol, usize)>,
    params: Vec<ExprId>,
    loops: Vec<LoopBinding>,
    drop_stack: Vec<DropBinding>,
    drop_flags: Vec<(Place, ExprId)>,
    initializing_self: Option<Symbol>,
    cellable: Vec<Symbol>,
}

/// An active loop in the MIR→λ_G lowering: the continue/exit MIR blocks paired
/// with the λ_G continuations a back-edge or break jumps to.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
struct MirLoop {
    continue_block: mir::BlockId,
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
    temps: Vec<(u32, ExprId)>,
}

#[derive(Default)]
struct MirBlockCache {
    blocks: FxHashMap<MirBlockKey, ExprId>,
}

/// The MIR body whose statements are currently being lowered, plus the
/// loops in scope at the consuming statement — what expression lowering
/// needs to lower an expression-position construct from its scaffold
/// blocks (delivering the value through the continuation).
struct ScaffoldCtx {
    body: std::sync::Arc<mir::Body>,
    loops: Vec<MirLoop>,
}

/// A match's scaffold arm blocks, resolved before pattern compilation: the
/// decision tree's arm bodies lower from these (value through `k`; a jump
/// to `join` delivers void).
pub(super) struct ScaffoldArms {
    pub(super) blocks: Vec<mir::BlockId>,
    pub(super) join: Option<mir::BlockId>,
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
        let mut caps: Vec<_> = self
            .caps
            .iter()
            .map(|(key, cap)| (key.clone(), *cap))
            .collect();
        caps.sort_by(|(a, _), (b, _)| format!("{a:?}").cmp(&format!("{b:?}")));
        let mut cap_templates: Vec<_> = self
            .cap_templates
            .iter()
            .map(|(symbol, index)| (*symbol, *index))
            .collect();
        cap_templates.sort();
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
            resume_k: self.resume_k,
            top_level: self.top_level,
            caps,
            cap_templates,
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

pub(crate) fn lower_program<'a>(units: Vec<LowerUnit<'a>>, entry: usize) -> LoweredProgram {
    let mut lowering = Lowering {
        units,
        entry,
        p: Program::new(),
        sources: FxHashMap::default(),
        mutating: FxHashSet::default(),
        statics: FxHashMap::default(),
        globals: FxHashMap::default(),
        done: FxHashMap::default(),
        finalizer_thunks: FxHashMap::default(),
        queue: vec![],
        escaping: FxHashSet::default(),
        local_func_labels: FxHashMap::default(),
        top_level_cells: FxHashMap::default(),
        checked_bodies: FxHashMap::default(),
        scaffold_ctx: vec![],
        handler_templates: vec![],
        materialized_caps: FxHashMap::default(),
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
    lowering.diagnose_unsupported_handlers();
    let (main, result_ty) = lowering.lower_main();
    lowering.drain_queue();
    let mut entry_funcs: FxHashSet<Label> = lowering.done.values().copied().collect();
    entry_funcs.extend(lowering.escaping.iter().copied());
    entry_funcs.extend(lowering.finalizer_thunks.values().copied());
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
    // ----- Expressions ------------------------------------------------------

    /// Lower `expr`, delivering its value to continuation `k : Fn(T, ⊥)`.
    fn lower_expr(&mut self, expr: &Expr, ctx: &Ctx, k: ExprId) -> ExprId {
        // Tier-2 auto-clone: retain the value's buffers before handing it to
        // the consumer, so the clone and the original release independently.
        // The mark may sit on a generic body; the θ-resolved type decides
        // per instantiation: CheapClone retains, non-owned needs nothing,
        // owned-but-not-CheapClone is unsupported.
        let k = if expr.ownership.auto_clone {
            match self.auto_clone_action(expr, ctx) {
                AutoClone::Retain => self.retain_then(expr, ctx, k),
                AutoClone::Nothing => k,
                AutoClone::Unsupported(ty) => {
                    self.diagnostics.push(format!(
                        "lowering: extracting owned value of type {ty:?} from a heap object                          requires a CheapClone (or copy) instantiation"
                    ));
                    k
                }
            }
        } else {
            k
        };
        if let Some(pack) = self.existential_pack_at(expr.existential_pack.as_ref(), ctx) {
            if let CheckTy::Any { protocol, .. } = &pack.payload
                && protocol.protocol
                    == self
                        .any_protocol(&pack.existential)
                        .unwrap_or(protocol.protocol)
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

    /// What a tier-2 mark means at this instantiation.
    fn auto_clone_action(&mut self, expr: &Expr, ctx: &Ctx) -> AutoClone {
        let ty = Self::borrow_erased_ty(self.checker_ty(expr, ctx));
        if !self.needs_drop_type(&ty) {
            return AutoClone::Nothing;
        }
        if let CheckTy::Nominal(symbol, _) = &ty
            && self.symbol_has_conformance(*symbol, Symbol::CheapClone)
        {
            return AutoClone::Retain;
        }
        AutoClone::Unsupported(ty)
    }

    fn symbol_has_conformance(&self, symbol: Symbol, protocol: Symbol) -> bool {
        self.units.iter().any(|unit| {
            unit.types
                .catalog
                .conformances
                .contains_key(&(symbol, ProtocolRef::bare(protocol)))
        })
    }

    /// A continuation that retains `expr`'s refcounted buffers, then applies
    /// `k` — the receiving end of a tier-2 auto-clone.
    fn retain_then(&mut self, expr: &Expr, ctx: &Ctx, k: ExprId) -> ExprId {
        let ty = self.checker_ty(expr, ctx);
        let value_ty = self.map_ty(&ty);
        let bot = self.p.ty_bot();
        let cont = self.p.func("retain", value_ty, bot);
        let value = self.p.var(cont);
        let next = self.p.app(k, value);
        let body = self.lower_retain_value_then(ctx, value, &ty, next);
        self.p.set_body(cont, body);
        self.p.func_ref(cont)
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
            } => self.lower_call(expr, callee, args, trailing_block.as_ref(), ctx, k),
            // Variant construction with impure payloads: chain the
            // arguments, then build the value (no function is called).
            ExprKind::Con {
                enum_symbol,
                tag,
                variant_symbol,
                args,
            } => {
                let site = VariantSite {
                    node: expr.id,
                    instantiation: expr.instantiation.clone(),
                };
                let arg_exprs: Vec<&Expr> = args.iter().collect();
                self.lower_args(&arg_exprs, ctx, vec![], &mut |this, values| {
                    let value = this.variant_new_for_expr(
                        site.clone(),
                        *enum_symbol,
                        *tag,
                        *variant_symbol,
                        &values,
                        ctx,
                    );
                    let body = this.p.app(k, value);
                    this.embed_acquires_then(&arg_exprs, &values, ctx, body)
                })
            }
            ExprKind::Block(block) => self.lower_block(block, ctx, k),
            // A tuple literal with impure items: chain them left to right.
            ExprKind::Tuple(items) => {
                let item_exprs: Vec<&Expr> = items.iter().collect();
                self.lower_args(&item_exprs, ctx, vec![], &mut |this, values| {
                    let tuple = this.p.tuple(&values);
                    let body = this.p.app(k, tuple);
                    this.embed_acquires_then(&item_exprs, &values, ctx, body)
                })
            }
            // Field read on an impure receiver: bind the receiver through
            // a continuation, then GetField. (`Member` still covers
            // anonymous-record fields, which have no catalog symbol.)
            ExprKind::Member(Some(receiver), label) | ExprKind::Proj(receiver, label, _) => {
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
            ExprKind::Match(scrutinee, arms) => {
                let scaffold_arms = self.match_scaffold_arms(expr);
                self.lower_match(scrutinee, arms, scaffold_arms, ctx, k)
            }
            // Performing an effect with no handler in scope reaches the
            // implicit top-level handler (Plotkin & Pretnar, LMCS 2013).
            // A request that is a syntactic IORequest variant routes
            // statically to its io primop; in-language handlers are M7,
            // the dynamic io_perform dispatch M8.
            ExprKind::CallEffect {
                effect_name, args, ..
            } => {
                // A capability in scope wins: the nearest `@handle` for
                // this effect's label (or one of our own capability
                // parameters) put one on the context.
                if let Some(effect) = effect_name.symbol().ok()
                    && (ctx.cap_templates.contains_key(&effect)
                        || ctx.caps.keys().any(|(label, _)| *label == effect))
                {
                    return self.lower_capped_perform(effect, expr, args, ctx, k);
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
                    let body = this.p.app(k, tuple);
                    this.embed_acquires_then(&field_exprs, &values, ctx, body)
                })
            }
            // An impure @_ir (a bind needing an auto-clone retain — e.g.
            // `_store<Element>`'s value under implicit-copy generics):
            // lower the binds continuation-style, which applies the
            // per-bind retains, then splice over the values.
            ExprKind::InlineIR(instruction) => {
                let bind_refs: Vec<&Expr> = instruction.binds.iter().collect();
                self.lower_args(&bind_refs, ctx, vec![], &mut |this, values| match this
                    .splice_with_values(instruction, ctx, &values)
                {
                    Some(result) => this.p.app(k, result),
                    None => this.dead_end("unsupported_ir"),
                })
            }
            other => {
                self.diagnostics
                    .push(format!("lowering: expression not yet supported: {other:?}"));
                self.dead_end("unsupported_expr")
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
            .top_level_value_ty(nodes.last())
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
            temps: FxHashMap::default(),
            ret_k,
            tail_k: ret_k,
            raw_ret_k: ret_k,
            resume_k: None,
            top_level: true,
            caps: FxHashMap::default(),
            cap_templates: FxHashMap::default(),
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
    fn lower_main_nodes(&mut self, _nodes: &[Node], ctx: &Ctx, k: ExprId) -> ExprId {
        // The combined main body spans every file's runnable top-level nodes:
        // `mir::build_checked` built and checked it from the same node filter
        // (`mir::main_body_nodes`).
        let body = self.units[ctx.unit]
            .bodies
            .top_level()
            .unwrap_or_else(|| panic!("missing checked MIR top-level body"));
        self.lower_mir_body(&body, ctx, k)
    }

    /// The checker type of a top-level block's final value: the last
    /// node's expression type (or the branch type of a block-final
    /// if/else); None for statements that yield nothing.
    fn top_level_value_ty(&self, last: Option<&Node>) -> Option<CheckTy> {
        match last? {
            Node::Stmt(Stmt {
                kind: StmtKind::Expr(expr),
                ..
            }) => Some(expr.ty.clone()),
            Node::Stmt(Stmt {
                kind: StmtKind::If(_, then_block, Some(_)),
                ..
            }) => then_block.body.iter().next_back().and_then(|n| match n {
                Node::Stmt(Stmt {
                    kind: StmtKind::Expr(e),
                    ..
                })
                | Node::Expr(e) => Some(e.ty.clone()),
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
        if !self.cap_entries_of(symbol, &Theta::default()).is_empty() {
            self.diagnostics
                .push("lowering: main performing an unhandled effect (not yet supported)".into());
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
        // No callable `main` (diagnosed above, plus by `demand`): a
        // bodyless entry of the right shape keeps the program well-typed;
        // the scheduler emits it as a trap, honest if ever reached.
        let entry_label = entry_label.unwrap_or_else(|| self.p.func("main_unsupported", dom, bot));
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
            temps: FxHashMap::default(),
            ret_k,
            tail_k: ret_k,
            raw_ret_k: ret_k,
            resume_k: None,
            top_level: true,
            caps: FxHashMap::default(),
            cap_templates: FxHashMap::default(),
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
            .top_level_value_ty(nodes.last())
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
        ExprKind::Member(Some(receiver), ..) | ExprKind::Proj(receiver, ..) => {
            receiver_root_symbol(receiver)
        }
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
        match crate::types::solve::reduce_projection(self.catalog, *symbol, args, protocol, *assoc)
        {
            Some(reduced) => self.fold_ty(&reduced),
            None => rebuilt,
        }
    }

    fn fold_eff(&mut self, eff: &crate::types::ty::EffectRow) -> crate::types::ty::EffectRow {
        eff.clone()
    }
}
