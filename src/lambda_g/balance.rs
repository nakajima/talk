//! The free-balance verifier (ADR 0017 stage 2): a post-lowering pass over
//! λ_G that checks, per body, that every owned allocation is freed exactly
//! once per execution path. It re-derives balance INDEPENDENTLY from the
//! emitted IR — it never consults flow's drop annotations — which is what
//! makes it a check on the pipeline's output invariant rather than a third
//! drop authority. The shape is rustc's drop elaboration: forward dataflow
//! computing maybe-initialized-style facts per allocation-producing value,
//! classifying each `free` site as Static (must-live → ok), Dead
//! (must-dead → double-free report), or Conditional (maybe-live →
//! flag-guarded; v1 trusts the drop-flag discipline and only counts these).
//! The property itself is Perceus's "garbage-free" claim for precise RC.
//!
//! # Model
//!
//! A **unit** is one chunk-forming function (an `entry_funcs` member, plus
//! `main`) together with the local continuation helpers reachable from it
//! by function reference — the same grouping the bytecode scheduler uses
//! for chunks/blocks. Each helper is a basic block whose single parameter
//! is a block argument; edges are jumps (`App` to a helper), branch/switch
//! thunk references, and the continuation argument of calls. Calls to the
//! unit's return continuation (`Extract(var root, arity)`) are exits.
//!
//! Tracked allocation roots, per unit:
//! - **Fresh**: the result of an `alloc` primop. Owned by construction;
//!   live-at-exit without escaping is a leak.
//! - **CallResult**: the value a call delivers to its continuation helper.
//!   Because λ_G erases borrows, an owned return and a borrowed return look
//!   identical, so a CallResult root is only ever reported when the unit
//!   frees it on one path but exits with it live on another (inconsistent
//!   teardown) — a genuinely borrowed result is freed on no path and stays
//!   silent.
//! - **Param**: the root function's own parameters, tracked only to build
//!   call summaries (see below); never reported as leaks (ADR 0018:
//!   parameters are borrows by default, so the callee owes no free).
//!
//! Frees target *places* — a root plus a `get_field`/`extract` path (the
//! `free(get_field(...))` chains lowering emits). Aggregates built with
//! `record_new`/tuples are tracked structurally, so a fresh pointer stored
//! into a record and freed through a field read resolves to its root.
//!
//! # Calling convention assumptions (ADR 0018)
//!
//! Parameters are borrow-by-default: passing a root to a call does not by
//! itself transfer ownership. For callees that are statically-known chunk
//! functions, a bottom-up **summary** (computed in reverse-topological
//! call-graph order; cycles get no summary) records which parameter-derived
//! places the callee frees on ALL of its paths, and whether a parameter
//! escapes (is stored, repacked, or passed on opaquely). Callers apply the
//! summary: must-freed places die at the call (a later caller-side free of
//! the same place is a double free — this is exactly the S1 deinit shape),
//! escaped arguments stop being tracked. Calls through computed callees
//! (closures, existential witnesses, capabilities) have no summary: their
//! arguments escape, which silences rather than guesses.
//!
//! # v1 scope — what is skipped, loudly
//!
//! Units are SKIPPED (counted per unit in [`BalanceOutcome::skipped`], with
//! a reason — never silently) when their control flow is not a
//! chunk-shaped CFG:
//! - a local helper escapes as a value (handler installation, delimiter
//!   capture — the `@handle` shapes; ADR 0017 stage 4 territory);
//! - a continuation is delivered a bare value through a computed callee
//!   (effect resumption / CallCont);
//! - branch or switch targets are computed rather than direct references;
//! - the fixpoint fails to converge within a budget.
//!
//! Precision losses inside analyzed units are counted in
//! [`BalanceOutcome::widened`] / [`BalanceOutcome::conditional_frees`], not
//! reported: retains (CoW clones), values entering cells / raw memory /
//! variants / existentials / heap objects, pointer arithmetic on tracked
//! pointers, and merge points where two different roots join. Enum payload
//! teardown reads through `get_payload` and raw-memory element loops read
//! through `load`, so container/enum element accounting is out of v1's
//! reach (it happens through untracked places, never misreported).
//!
//! ON by default in test builds (plan 6.1): `Driver::lower` runs it over
//! every lowered body in unit tests and the dedicated fuzz target and
//! asserts zero reports; set
//! `TALK_SKIP_VERIFY_BALANCE=1` to opt out. Production builds never run
//! it. Its acceptance tests (including the known-bug shapes it was built
//! red against) live in `balance_tests.rs`.

use rustc_hash::{FxHashMap, FxHashSet};
use std::collections::VecDeque;
use std::rc::Rc;

use crate::lambda_g::expr::{Const, ExprId, ExprKind, Op, TyId, TyKind};
use crate::lambda_g::program::{Label, Program};

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum ReportKind {
    /// A path frees a place that is already dead on every path reaching it.
    DoubleFree,
    /// A path exits (or re-enters a loop) with a live owned allocation that
    /// other paths free.
    Leak,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct BalanceReport {
    /// The chunk-forming function whose unit the imbalance was found in.
    pub unit: String,
    pub kind: ReportKind,
    /// Human-readable locus: root, place path, and what happened.
    pub detail: String,
}

#[derive(Debug, Default)]
pub struct BalanceOutcome {
    pub reports: Vec<BalanceReport>,
    /// Units not analyzed, with the reason — the no-silent-caps ledger.
    pub skipped: Vec<(String, String)>,
    /// Units fully analyzed.
    pub analyzed: usize,
    /// Frees classified Conditional (maybe-live; flag-guarded drops). v1
    /// trusts the flag discipline and does not report these.
    pub conditional_frees: usize,
    /// Precision-loss events (escapes into cells/memory/variants, retains,
    /// join widenings). Diagnostic only.
    pub widened: usize,
}

impl BalanceOutcome {
    pub fn render(&self) -> String {
        let mut out = format!(
            "balance: {} analyzed, {} skipped, {} conditional frees, {} widened, {} reports",
            self.analyzed,
            self.skipped.len(),
            self.conditional_frees,
            self.widened,
            self.reports.len()
        );
        for report in &self.reports {
            out.push_str(&format!(
                "\n  {:?} in {}: {}",
                report.kind, report.unit, report.detail
            ));
        }
        for (unit, reason) in &self.skipped {
            out.push_str(&format!("\n  skipped {unit}: {reason}"));
        }
        out
    }
}

/// Run the free-balance verifier over every lowered body.
pub fn verify_balance(p: &Program, main: Label, entry_funcs: &FxHashSet<Label>) -> BalanceOutcome {
    let mut chunks: FxHashSet<Label> = entry_funcs.clone();
    chunks.insert(main);

    // Reverse-topological order over the chunk call graph so callee
    // summaries exist before their callers are analyzed. petgraph's
    // tarjan_scc returns SCCs with callees before callers when edges point
    // caller → callee.
    use petgraph::algo::tarjan_scc;
    use petgraph::graph::DiGraph;
    let mut graph = DiGraph::<Label, ()>::new();
    let mut index = FxHashMap::default();
    let mut ordered: Vec<Label> = chunks.iter().copied().collect();
    ordered.sort_by_key(|l| l.0);
    for &label in &ordered {
        index.insert(label, graph.add_node(label));
    }
    let mut members_of: FxHashMap<Label, FxHashSet<Label>> = FxHashMap::default();
    for &root in &ordered {
        let members = unit_members(p, root, &chunks);
        let mut callees: FxHashSet<Label> = FxHashSet::default();
        for &member in &members {
            if let Some(body) = p.body(member) {
                for target in p.set_labels(p.expr(body).lf) {
                    if chunks.contains(&target) && target != root {
                        callees.insert(target);
                    }
                }
            }
        }
        for callee in callees {
            graph.add_edge(index[&root], index[&callee], ());
        }
        members_of.insert(root, members);
    }

    let mut outcome = BalanceOutcome::default();
    let mut summaries: FxHashMap<Label, Summary> = FxHashMap::default();
    for scc in tarjan_scc(&graph) {
        // Within an SCC (recursion), members see no summaries for each
        // other — calls into the cycle escape their arguments.
        let mut scc_labels: Vec<Label> = scc.iter().map(|n| graph[*n]).collect();
        scc_labels.sort_by_key(|l| l.0);
        for root in scc_labels {
            let unit = UnitAnalysis::new(p, root, &members_of[&root], &chunks, &summaries);
            match unit.run() {
                Ok((reports, summary, conditional, widened)) => {
                    outcome.analyzed += 1;
                    outcome.conditional_frees += conditional;
                    outcome.widened += widened;
                    outcome.reports.extend(reports);
                    summaries.insert(root, summary);
                }
                Err(reason) => outcome.skipped.push((p.name(root), reason)),
            }
        }
    }
    outcome.reports.sort();
    outcome.reports.dedup();
    outcome
}

/// Entry point for the test harnesses: ON by default (plan 6.1 -
/// `Driver::lower` runs it over every lowered body in unit tests and the
/// dedicated fuzz target); `TALK_SKIP_VERIFY_BALANCE=1` opts out, returning
/// `None`.
pub fn verify_balance_unless_skipped(
    p: &Program,
    main: Label,
    entry_funcs: &FxHashSet<Label>,
) -> Option<BalanceOutcome> {
    match std::env::var("TALK_SKIP_VERIFY_BALANCE") {
        Ok(v) if v == "1" => None,
        _ => Some(verify_balance(p, main, entry_funcs)),
    }
}

/// The unit's blocks: the root plus every non-chunk label reachable from it
/// through function references (the scheduler's block-claiming rule).
fn unit_members(p: &Program, root: Label, chunks: &FxHashSet<Label>) -> FxHashSet<Label> {
    let mut members: FxHashSet<Label> = FxHashSet::default();
    members.insert(root);
    let mut queue: VecDeque<Label> = VecDeque::new();
    queue.push_back(root);
    while let Some(label) = queue.pop_front() {
        let Some(body) = p.body(label) else { continue };
        for target in p.set_labels(p.expr(body).lf) {
            if chunks.contains(&target) || members.contains(&target) {
                continue;
            }
            members.insert(target);
            queue.push_back(target);
        }
    }
    members
}

// ---------------------------------------------------------------------------
// Abstract domain
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
struct RootId(u32);

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum RootKey {
    /// An `alloc` primop in this unit.
    Alloc(ExprId),
    /// The value delivered to a call's continuation helper.
    ContResult(Label),
    /// The root function's i-th parameter.
    Param(u32),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum RootKind {
    Fresh,
    CallResult,
    Param(u32),
}

/// Abstract value: what a λ_G expression denotes within one unit.
#[derive(Debug, Clone, PartialEq)]
enum AbsVal {
    /// Untracked (loads, cells, payloads, unknown call plumbing).
    Opaque,
    /// Scalars, statics, unit — never owned heap state.
    Scalar,
    /// A place: allocation root + field/extract path ([] = the root value).
    Place(RootId, Vec<u32>),
    /// A structural aggregate (record_new / tuple) with per-field values.
    Agg(Rc<Vec<AbsVal>>),
    /// A reference to a function (helper, chunk, or foreign).
    FuncRef(Label),
    /// `var root` — the root function's whole parameter bundle.
    SelfTuple,
    /// The unit's return continuation (`Extract(var root, arity)`).
    RetK,
    /// A drop-flag cell: `cell_new` of a constant bool, keyed by the
    /// cell_new expression. Its per-path state lives in [`Flow::flags`].
    FlagCell(ExprId),
    /// The value of `cell_get` on a drop-flag cell — a branch condition
    /// the transfer can resolve against the cell's per-path state.
    FlagRead(ExprId),
}

/// Per-path state of a drop-flag cell (three-point constant lattice).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Flag {
    True,
    False,
    Unknown,
}

impl Flag {
    fn from_bool(value: bool) -> Flag {
        if value { Flag::True } else { Flag::False }
    }

    fn join(a: Flag, b: Flag) -> Flag {
        if a == b { a } else { Flag::Unknown }
    }
}

/// Three-point liveness lattice. For paths, an absent entry means
/// "implicitly live since the root was minted" — only Dead/Maybe are
/// stored. For roots, an absent entry means "not allocated on this path".
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Tri {
    Live,
    Dead,
    Maybe,
}

impl Tri {
    fn join(a: Tri, b: Tri) -> Tri {
        if a == b { a } else { Tri::Maybe }
    }
}

#[derive(Debug, Clone, Default, PartialEq)]
struct Flow {
    /// Allocation roots present on this path: Live (must) or Maybe.
    roots: FxHashMap<RootId, Tri>,
    /// Freed places: Dead (must) or Maybe. Absent = live.
    paths: FxHashMap<(RootId, Vec<u32>), Tri>,
    /// Values bound to helper parameters along this path.
    bindings: FxHashMap<Label, AbsVal>,
    /// Drop-flag cell states along this path (see [`AbsVal::FlagCell`]):
    /// the drop-flag discipline is path-correlated, so branch edges on a
    /// known flag prune — otherwise every flag-guarded free reads as a
    /// phantom double-free/leak on the infeasible path.
    flags: FxHashMap<ExprId, Flag>,
}

impl Flow {
    /// Lattice join; returns whether self changed plus the binding values
    /// that conflicted (the caller escapes their roots — a value that loses
    /// its name at a merge can no longer be tracked to its free).
    fn join_from(&mut self, other: &Flow) -> (bool, Vec<AbsVal>) {
        let mut changed = false;
        let mut conflicts = vec![];
        // Roots: key union; missing = not-allocated joins to Maybe.
        for (&r, &state) in &other.roots {
            let entry = self.roots.get(&r).copied();
            let joined = match entry {
                Some(existing) => Tri::join(existing, state),
                None => Tri::Maybe,
            };
            if entry != Some(joined) {
                self.roots.insert(r, joined);
                changed = true;
            }
        }
        let missing: Vec<RootId> = self
            .roots
            .keys()
            .copied()
            .filter(|r| !other.roots.contains_key(r))
            .collect();
        for r in missing {
            if self.roots.insert(r, Tri::Maybe) != Some(Tri::Maybe) {
                changed = true;
            }
        }
        // Paths: missing = implicitly Live.
        for (key, &state) in &other.paths {
            let entry = self.paths.get(key).copied();
            let joined = match entry {
                Some(existing) => Tri::join(existing, state),
                None => Tri::join(Tri::Live, state),
            };
            if joined == Tri::Live {
                continue;
            }
            if entry != Some(joined) {
                self.paths.insert(key.clone(), joined);
                changed = true;
            }
        }
        let softened: Vec<(RootId, Vec<u32>)> = self
            .paths
            .iter()
            .filter(|(key, state)| **state == Tri::Dead && !other.paths.contains_key(*key))
            .map(|(key, _)| key.clone())
            .collect();
        for key in softened {
            self.paths.insert(key, Tri::Maybe);
            changed = true;
        }
        // Flags: key union; a side that never minted the cell joins to
        // Unknown.
        for (&cell, &state) in &other.flags {
            let entry = self.flags.get(&cell).copied();
            let joined = match entry {
                Some(existing) => Flag::join(existing, state),
                None => Flag::Unknown,
            };
            if entry != Some(joined) {
                self.flags.insert(cell, joined);
                changed = true;
            }
        }
        let unshared: Vec<ExprId> = self
            .flags
            .iter()
            .filter(|(cell, state)| **state != Flag::Unknown && !other.flags.contains_key(*cell))
            .map(|(cell, _)| *cell)
            .collect();
        for cell in unshared {
            self.flags.insert(cell, Flag::Unknown);
            changed = true;
        }
        // Bindings: agree or widen to Opaque.
        for (&label, value) in &other.bindings {
            match self.bindings.get(&label) {
                Some(existing) if existing == value => {}
                Some(existing) if *existing == AbsVal::Opaque => {}
                Some(existing) => {
                    conflicts.push(existing.clone());
                    conflicts.push(value.clone());
                    self.bindings.insert(label, AbsVal::Opaque);
                    changed = true;
                }
                None => {
                    self.bindings.insert(label, value.clone());
                    changed = true;
                }
            }
        }
        (changed, conflicts)
    }
}

/// What a chunk function does to its parameters, observed on all paths.
#[derive(Debug, Clone, Default)]
struct Summary {
    /// Per parameter index: places (paths) freed on every path to every
    /// exit — the caller may treat them as dead after the call.
    must_freed: FxHashMap<u32, Vec<Vec<u32>>>,
    /// Parameters whose value escapes inside the callee (stored, repacked,
    /// forwarded opaquely). Callers stop tracking those arguments.
    escaped: FxHashSet<u32>,
}

const MAX_PATH_DEPTH: usize = 8;
const MAX_BLOCK_VISITS: usize = 20_000;

// ---------------------------------------------------------------------------
// Per-unit analysis
// ---------------------------------------------------------------------------

struct UnitAnalysis<'a> {
    p: &'a Program,
    root: Label,
    /// Parameter count excluding the return continuation slot.
    arity: usize,
    dom_items: Vec<TyId>,
    members: &'a FxHashSet<Label>,
    chunks: &'a FxHashSet<Label>,
    summaries: &'a FxHashMap<Label, Summary>,

    root_infos: Vec<RootKind>,
    root_ids: FxHashMap<RootKey, RootId>,
    /// Sticky across paths: once escaped, a root is never reported.
    escaped: FxHashSet<RootId>,
    /// Drop-flag cells that escaped the cell_new/cell_set/cell_get
    /// discipline (passed to a call, joined against a different value):
    /// their state is Unknown forever — branches on them take both edges.
    unknown_flags: FxHashSet<ExprId>,
    /// Every place ever freed, per root (the free universe for leak checks).
    freed_universe: FxHashMap<RootId, FxHashSet<Vec<u32>>>,
    in_states: FxHashMap<Label, Flow>,
    skip: Option<String>,

    reporting: bool,
    reports: Vec<BalanceReport>,
    conditional: usize,
    widened: usize,
    /// Per-exit sets of must-freed Param places, for the summary.
    exit_param_frees: Vec<FxHashSet<(u32, Vec<u32>)>>,
}

impl<'a> UnitAnalysis<'a> {
    fn new(
        p: &'a Program,
        root: Label,
        members: &'a FxHashSet<Label>,
        chunks: &'a FxHashSet<Label>,
        summaries: &'a FxHashMap<Label, Summary>,
    ) -> Self {
        let dom_items: Vec<TyId> = match p.ty_kind(p.dom(root)) {
            TyKind::Tuple(items) => items.to_vec(),
            _ => vec![],
        };
        let arity = dom_items.len().saturating_sub(1);
        UnitAnalysis {
            p,
            root,
            arity,
            dom_items,
            members,
            chunks,
            summaries,
            root_infos: vec![],
            root_ids: FxHashMap::default(),
            escaped: FxHashSet::default(),
            unknown_flags: FxHashSet::default(),
            freed_universe: FxHashMap::default(),
            in_states: FxHashMap::default(),
            skip: None,
            reporting: false,
            reports: vec![],
            conditional: 0,
            widened: 0,
            exit_param_frees: vec![],
        }
    }

    /// Fixpoint, then a reporting pass over the converged states.
    /// Ok((reports, summary, conditional, widened)) or Err(skip reason).
    fn run(mut self) -> Result<(Vec<BalanceReport>, Summary, usize, usize), String> {
        let mut initial = Flow::default();
        for index in 0..self.arity {
            let ty = self.dom_items[index];
            if self.trackable(ty) {
                let r = self.mint(RootKey::Param(index as u32), RootKind::Param(index as u32));
                initial.roots.insert(r, Tri::Live);
            }
        }
        self.in_states.insert(self.root, initial);

        let mut worklist: VecDeque<Label> = VecDeque::new();
        worklist.push_back(self.root);
        let mut visits = 0usize;
        while let Some(block) = worklist.pop_front() {
            visits += 1;
            if visits > MAX_BLOCK_VISITS {
                return Err("fixpoint budget exceeded".to_string());
            }
            let mut flow = self.in_states[&block].clone();
            let edges = self.transfer(block, &mut flow);
            if let Some(reason) = self.skip.take() {
                return Err(reason);
            }
            for (target, value) in edges {
                let mut incoming = flow.clone();
                incoming.bindings.insert(target, value);
                let mut conflicts = vec![];
                match self.in_states.get_mut(&target) {
                    Some(existing) => {
                        let (changed, found) = existing.join_from(&incoming);
                        conflicts = found;
                        if changed && !worklist.contains(&target) {
                            worklist.push_back(target);
                        }
                    }
                    None => {
                        self.in_states.insert(target, incoming);
                        worklist.push_back(target);
                    }
                }
                for conflict in &conflicts {
                    self.escape(conflict);
                }
            }
        }

        // Reporting pass: re-run every reached block once against its
        // converged in-state, collecting classifications and exit checks.
        self.reporting = true;
        let mut reached: Vec<Label> = self.in_states.keys().copied().collect();
        reached.sort_by_key(|l| l.0);
        for block in reached {
            let mut flow = self.in_states[&block].clone();
            let _ = self.transfer(block, &mut flow);
            if let Some(reason) = self.skip.take() {
                return Err(reason);
            }
        }

        // Summary: Param places freed on every path to every exit.
        let mut summary = Summary::default();
        if let Some(first) = self.exit_param_frees.first() {
            let mut must: FxHashSet<(u32, Vec<u32>)> = first.clone();
            for exit in &self.exit_param_frees[1..] {
                must.retain(|entry| exit.contains(entry));
            }
            for (index, path) in must {
                summary.must_freed.entry(index).or_default().push(path);
            }
        }
        for (key, r) in &self.root_ids {
            if let RootKey::Param(index) = key
                && self.escaped.contains(r)
            {
                summary.escaped.insert(*index);
            }
        }

        let mut reports = std::mem::take(&mut self.reports);
        reports.sort();
        reports.dedup();
        Ok((reports, summary, self.conditional, self.widened))
    }

    fn trackable(&self, ty: TyId) -> bool {
        matches!(
            self.p.ty_kind(ty),
            TyKind::Boxed(_) | TyKind::Ptr | TyKind::Tuple(_)
        )
    }

    fn mint(&mut self, key: RootKey, kind: RootKind) -> RootId {
        if let Some(&r) = self.root_ids.get(&key) {
            return r;
        }
        let r = RootId(self.root_infos.len() as u32);
        self.root_infos.push(kind);
        self.root_ids.insert(key, r);
        r
    }

    fn describe_root(&self, r: RootId) -> String {
        let key = self
            .root_ids
            .iter()
            .find(|(_, id)| **id == r)
            .map(|(key, _)| key.clone());
        match key {
            Some(RootKey::Alloc(_)) => "fresh allocation".to_string(),
            Some(RootKey::ContResult(label)) => {
                format!("call result bound at {}", self.p.name(label))
            }
            Some(RootKey::Param(index)) => format!("parameter {index}"),
            None => "allocation".to_string(),
        }
    }

    fn report(&mut self, kind: ReportKind, detail: String) {
        if self.reporting {
            self.reports.push(BalanceReport {
                unit: self.p.name(self.root),
                kind,
                detail,
            });
        }
    }

    fn set_skip(&mut self, reason: &str) {
        if self.skip.is_none() {
            self.skip = Some(reason.to_string());
        }
    }

    /// Whether a value carries the unit's own control (a helper reference
    /// or the parameter bundle) — the handler/delimiter escape shapes.
    fn contains_local_control(&self, value: &AbsVal) -> bool {
        match value {
            AbsVal::FuncRef(label) => self.members.contains(label) && *label != self.root,
            AbsVal::SelfTuple => true,
            AbsVal::Agg(items) => items.iter().any(|item| self.contains_local_control(item)),
            _ => false,
        }
    }

    /// Escape every root reachable from a value; a local helper escaping as
    /// a value makes the unit unanalyzable (handler/delimiter shapes).
    fn escape(&mut self, value: &AbsVal) {
        match value {
            AbsVal::Place(r, _) => {
                if self.escaped.insert(*r) && !self.reporting {
                    self.widened += 1;
                }
            }
            AbsVal::Agg(items) => {
                for item in items.iter() {
                    self.escape(item);
                }
            }
            AbsVal::FuncRef(label) => {
                if self.members.contains(label) && *label != self.root {
                    self.set_skip("local continuation escapes as a value (handler/closure body)");
                }
            }
            AbsVal::SelfTuple => {
                self.set_skip("function's own parameter bundle escapes (delimiter capture)");
            }
            AbsVal::FlagCell(cell) => {
                // The cell left the flag discipline: its state is Unknown
                // forever (branches on it take both edges again).
                self.unknown_flags.insert(*cell);
            }
            AbsVal::Opaque | AbsVal::Scalar | AbsVal::RetK | AbsVal::FlagRead(_) => {}
        }
    }

    /// The per-path state of a drop-flag cell, Unknown once escaped.
    fn flag_state(&self, flow: &Flow, cell: ExprId) -> Flag {
        if self.unknown_flags.contains(&cell) {
            return Flag::Unknown;
        }
        flow.flags.get(&cell).copied().unwrap_or(Flag::Unknown)
    }

    /// Resolve a place under a value: descend aggregates, extend places.
    fn resolve_path(&self, value: &AbsVal, path: &[u32]) -> Option<(RootId, Vec<u32>)> {
        match value {
            AbsVal::Place(r, base) => {
                let mut full = base.clone();
                full.extend_from_slice(path);
                if full.len() > MAX_PATH_DEPTH {
                    return None;
                }
                Some((*r, full))
            }
            AbsVal::Agg(items) => {
                let (&head, rest) = path.split_first()?;
                let item = items.get(head as usize)?;
                self.resolve_path(item, rest)
            }
            _ => None,
        }
    }

    /// A `free` (or a callee's summarized must-free) of a place.
    fn kill_place(&mut self, flow: &mut Flow, r: RootId, path: Vec<u32>, via: &str) {
        if self.escaped.contains(&r) {
            return;
        }
        let root_state = flow.roots.get(&r).copied();
        let key = (r, path);
        let state = flow.paths.get(&key).copied().unwrap_or(Tri::Live);
        match (root_state, state) {
            (_, Tri::Dead) => {
                let detail = format!(
                    "double free: {} place {:?} already freed on every path reaching this free{}",
                    self.describe_root(r),
                    key.1,
                    via
                );
                self.report(ReportKind::DoubleFree, detail);
            }
            (Some(Tri::Live), Tri::Live) => {
                // Static free: exactly the must-live case — balanced.
            }
            _ => {
                // Maybe-live (or maybe-allocated) — Conditional. v1 trusts
                // the drop-flag discipline: count, don't report.
                if self.reporting {
                    self.conditional += 1;
                }
            }
        }
        self.freed_universe
            .entry(r)
            .or_default()
            .insert(key.1.clone());
        flow.paths.insert(key, Tri::Dead);
    }

    /// A control-flow point that leaves the unit: report owned roots still
    /// live on this path that are freed on some other path (CallResult) or
    /// unconditionally owed a free (Fresh).
    fn exit_check(&mut self, flow: &Flow) {
        if self.reporting {
            let mut param_frees: FxHashSet<(u32, Vec<u32>)> = FxHashSet::default();
            for ((r, path), state) in &flow.paths {
                if *state == Tri::Dead
                    && let Some(kind) = self.root_infos.get(r.0 as usize)
                    && let RootKind::Param(index) = kind
                {
                    param_frees.insert((*index, path.clone()));
                }
            }
            self.exit_param_frees.push(param_frees);
        }

        let mut live: Vec<(RootId, RootKind)> = flow
            .roots
            .iter()
            .filter(|(r, state)| **state == Tri::Live && !self.escaped.contains(r))
            .map(|(r, _)| (*r, self.root_infos[r.0 as usize]))
            .collect();
        live.sort_by_key(|(r, _)| *r);
        for (r, kind) in live {
            match kind {
                RootKind::Param(_) => {}
                RootKind::Fresh => {
                    let freed = flow.paths.get(&(r, vec![])).copied() == Some(Tri::Dead);
                    if !freed {
                        let detail = format!(
                            "leaked on this path: {} is live at exit and never freed or moved",
                            self.describe_root(r)
                        );
                        self.report(ReportKind::Leak, detail);
                    }
                }
                RootKind::CallResult => {
                    let Some(universe) = self.freed_universe.get(&r) else {
                        continue;
                    };
                    let mut paths: Vec<Vec<u32>> = universe.iter().cloned().collect();
                    paths.sort();
                    for path in paths {
                        // Absent = never freed on THIS path, while some
                        // other path frees it: leaked-on-some-path.
                        if !flow.paths.contains_key(&(r, path.clone())) {
                            let detail = format!(
                                "leaked on this path: {} place {:?} is freed on another path but live at this exit",
                                self.describe_root(r),
                                path
                            );
                            self.report(ReportKind::Leak, detail);
                        }
                    }
                }
            }
        }
    }

    /// A call delivers a (potentially owned) result to a continuation
    /// helper: mint/refresh the CallResult root.
    fn mint_call_result(&mut self, flow: &mut Flow, cont: Label) -> AbsVal {
        let dom = self.p.dom(cont);
        if !self.trackable(dom) {
            return if matches!(self.p.ty_kind(dom), TyKind::Void) {
                AbsVal::Scalar
            } else {
                AbsVal::Opaque
            };
        }
        let r = self.mint(RootKey::ContResult(cont), RootKind::CallResult);
        // Re-minting while the previous instance is must-live and torn
        // down elsewhere = a loop-carried leak (B2's `continue` shape).
        if flow.roots.get(&r).copied() == Some(Tri::Live)
            && !self.escaped.contains(&r)
            && self.freed_universe.contains_key(&r)
        {
            let detail = format!(
                "leaked on loop back-edge: {} is still live when the next iteration rebinds it",
                self.describe_root(r)
            );
            self.report(ReportKind::Leak, detail);
        }
        flow.roots.insert(r, Tri::Live);
        flow.paths.retain(|(root, _), _| *root != r);
        AbsVal::Place(r, vec![])
    }

    // -----------------------------------------------------------------
    // Expression evaluation (effects fire in evaluation order; sharing is
    // respected through the per-block memo).
    // -----------------------------------------------------------------

    fn eval(&mut self, e: ExprId, flow: &mut Flow, memo: &mut FxHashMap<ExprId, AbsVal>) -> AbsVal {
        if let Some(v) = memo.get(&e) {
            return v.clone();
        }
        let expr = self.p.expr(e).clone();
        let value = match &expr.kind {
            ExprKind::Const(Const::StaticPtr(_)) => AbsVal::Scalar,
            ExprKind::Const(_) => AbsVal::Scalar,
            ExprKind::Func(label) => AbsVal::FuncRef(*label),
            ExprKind::Var(label) => {
                if *label == self.root {
                    if matches!(self.p.ty_kind(self.p.dom(self.root)), TyKind::Tuple(_)) {
                        AbsVal::SelfTuple
                    } else {
                        AbsVal::Opaque
                    }
                } else if self.members.contains(label) {
                    flow.bindings.get(label).cloned().unwrap_or(AbsVal::Opaque)
                } else {
                    AbsVal::Opaque
                }
            }
            // The unwind operand (ADR 0027) is abort-path-only code and is
            // not part of this analysis (normal-path balance); it is
            // deliberately not evaluated, so its entry never registers as
            // an escaping local helper.
            ExprKind::App(f, a, _) => {
                // A nested (direct-style) application mid-expression: no
                // summary machinery here — escape and move on.
                let fv = self.eval(*f, flow, memo);
                let av = self.eval(*a, flow, memo);
                self.escape(&fv);
                self.escape(&av);
                if !self.reporting {
                    self.widened += 1;
                }
                AbsVal::Opaque
            }
            ExprKind::Tuple(items) => {
                let values: Vec<AbsVal> = items
                    .iter()
                    .map(|item| self.eval(*item, flow, memo))
                    .collect();
                AbsVal::Agg(Rc::new(values))
            }
            ExprKind::Extract(inner, index) => {
                let value = self.eval(*inner, flow, memo);
                self.project(value, *index)
            }
            ExprKind::PrimOp(op, args, ty) => self.eval_primop(e, *op, args, *ty, flow, memo),
        };
        memo.insert(e, value.clone());
        value
    }

    fn project(&mut self, value: AbsVal, index: u32) -> AbsVal {
        match value {
            AbsVal::SelfTuple => {
                if index as usize == self.arity && !self.dom_items.is_empty() {
                    AbsVal::RetK
                } else if let Some(&r) = self.root_ids.get(&RootKey::Param(index)) {
                    AbsVal::Place(r, vec![])
                } else {
                    AbsVal::Opaque
                }
            }
            AbsVal::Agg(items) => items.get(index as usize).cloned().unwrap_or(AbsVal::Opaque),
            AbsVal::Place(r, mut path) => {
                path.push(index);
                if path.len() > MAX_PATH_DEPTH {
                    if self.escaped.insert(r) && !self.reporting {
                        self.widened += 1;
                    }
                    AbsVal::Opaque
                } else {
                    AbsVal::Place(r, path)
                }
            }
            _ => AbsVal::Opaque,
        }
    }

    fn eval_primop(
        &mut self,
        e: ExprId,
        op: Op,
        args: &[ExprId],
        _ty: TyId,
        flow: &mut Flow,
        memo: &mut FxHashMap<ExprId, AbsVal>,
    ) -> AbsVal {
        // Br/Switch are terminators; reaching one mid-expression means the
        // body isn't chunk-shaped.
        if matches!(op, Op::Br | Op::Switch) {
            self.set_skip("nested branch/switch outside body position");
            return AbsVal::Opaque;
        }
        let values: Vec<AbsVal> = args.iter().map(|arg| self.eval(*arg, flow, memo)).collect();
        match op {
            Op::Alloc => {
                let r = self.mint(RootKey::Alloc(e), RootKind::Fresh);
                if flow.roots.get(&r).copied() == Some(Tri::Live)
                    && !self.escaped.contains(&r)
                    && flow.paths.get(&(r, vec![])).copied() != Some(Tri::Dead)
                {
                    let detail = "leaked on loop back-edge: fresh allocation is still live when \
                                  the allocation site runs again"
                        .to_string();
                    self.report(ReportKind::Leak, detail);
                }
                flow.roots.insert(r, Tri::Live);
                flow.paths.retain(|(root, _), _| *root != r);
                AbsVal::Place(r, vec![])
            }
            Op::Free => {
                if let Some((r, path)) = self.resolve_path(&values[0], &[]) {
                    self.kill_place(flow, r, path, "");
                }
                AbsVal::Scalar
            }
            Op::Retain => {
                // CoW clone: refcount accounting is out of v1's reach; the
                // buffer becomes rc-managed and untracked.
                self.escape(&values[0]);
                AbsVal::Scalar
            }
            Op::RecordNew(_) => AbsVal::Agg(Rc::new(values)),
            Op::GetField(index) => self.project(values[0].clone(), index),
            Op::SetField(_) => {
                // A functional record update aliases the original's fields;
                // v1 stops tracking everything involved.
                for value in &values {
                    self.escape(&value.clone());
                }
                AbsVal::Opaque
            }
            Op::VariantNew(..) | Op::ExistentialPack(_) => {
                // Payload reads come back through GetPayload /
                // ExistentialPayload as Opaque, so tracking through these
                // would dangle; escape the payloads instead.
                for value in &values {
                    self.escape(&value.clone());
                }
                AbsVal::Opaque
            }
            Op::GetTag | Op::IsUnique | Op::Cmp(_) => AbsVal::Scalar,
            Op::GetPayload(_) | Op::ExistentialWitness(_) | Op::ExistentialPayload | Op::Load => {
                AbsVal::Opaque
            }
            Op::CellNew => {
                // A drop-flag cell (cell_new of a constant bool) is
                // tracked so branches on the flag prune infeasible paths —
                // the drop-flag discipline is path-correlated, and without
                // this every flag-guarded free reads as a phantom
                // double-free/leak (rustc's drop elaboration tracks its
                // flags the same way). Any other cell stays opaque.
                if let [init] = args
                    && let ExprKind::Const(Const::Bool(value)) = self.p.expr(*init).kind
                {
                    flow.flags.insert(e, Flag::from_bool(value));
                    AbsVal::FlagCell(e)
                } else {
                    for value in &values {
                        self.escape(&value.clone());
                    }
                    AbsVal::Opaque
                }
            }
            Op::CellSet => {
                if let AbsVal::FlagCell(cell) = values[0] {
                    // Stored flags are bools (scalar): nothing escapes.
                    let state = match args.get(1).map(|arg| &self.p.expr(*arg).kind) {
                        Some(ExprKind::Const(Const::Bool(value))) => Flag::from_bool(*value),
                        _ => Flag::Unknown,
                    };
                    flow.flags.insert(cell, state);
                    AbsVal::Scalar
                } else {
                    for value in &values {
                        self.escape(&value.clone());
                    }
                    AbsVal::Opaque
                }
            }
            Op::CellGet => {
                if let AbsVal::FlagCell(cell) = values[0] {
                    AbsVal::FlagRead(cell)
                } else {
                    AbsVal::Opaque
                }
            }
            Op::Store | Op::Swap(_) | Op::Move => {
                // Values entering raw memory are reachable through
                // channels the place model cannot follow.
                for value in &values {
                    self.escape(&value.clone());
                }
                AbsVal::Opaque
            }
            Op::ObjectNew
            | Op::ObjectGet(_)
            | Op::ObjectSet(_)
            | Op::SetFinalizer
            | Op::RegionAcquire
            | Op::RegionRelease => {
                // 'heap objects are region-managed (ledger rules A–F), a
                // different accounting domain; out of v1 scope.
                for value in &values {
                    self.escape(&value.clone());
                }
                AbsVal::Opaque
            }
            Op::Add | Op::Sub | Op::Mul | Op::Div | Op::Gep => {
                // Arithmetic never transfers ownership: pointer offsets are
                // reads (element loads, byte comparisons), and emitted
                // frees always target the base place, never a computed
                // offset — so the base root stays tracked.
                AbsVal::Opaque
            }
            Op::Trunc | Op::IToF | Op::BToI => AbsVal::Scalar,
            Op::Copy => AbsVal::Scalar,
            // The `@handle` install marker (ADR 0027): its delimiter
            // operand is the return continuation, which stays untracked.
            Op::HandleInstall => AbsVal::Scalar,
            // Abort/unwind terminators mid-expression: not a chunk-shaped
            // body — skip loudly like nested branches.
            Op::Abort | Op::UnwindDone => {
                self.set_skip("abort/unwind op outside body position");
                AbsVal::Opaque
            }
            // IO reads buffers, it never consumes them.
            Op::IoPerform
            | Op::IoOpen
            | Op::IoRead
            | Op::IoWrite
            | Op::IoClose
            | Op::IoCtl
            | Op::IoPoll
            | Op::IoSocket
            | Op::IoBind
            | Op::IoListen
            | Op::IoConnect
            | Op::IoAccept
            | Op::IoSleep
            | Op::IoCwdLen
            | Op::IoCwdCopy
            | Op::IoGetenvLen
            | Op::IoGetenvCopy
            | Op::IoArgc
            | Op::IoArgLen
            | Op::IoArgCopy
            | Op::IoDirCount
            | Op::IoDirEntryKind
            | Op::IoDirEntryLen
            | Op::IoDirEntryCopy
            | Op::IoExit => AbsVal::Opaque,
            Op::Br | Op::Switch => unreachable!("handled above"),
        }
    }

    // -----------------------------------------------------------------
    // Block transfer: evaluate the body, interpret the terminator, and
    // return the out-edges (target, block-argument value).
    // -----------------------------------------------------------------

    fn transfer(&mut self, block: Label, flow: &mut Flow) -> Vec<(Label, AbsVal)> {
        let Some(body) = self.p.body(block) else {
            // Unset body: a deliberate trap (match_failed) — a dead end.
            return vec![];
        };
        let mut memo: FxHashMap<ExprId, AbsVal> = FxHashMap::default();
        let expr = self.p.expr(body).clone();
        match &expr.kind {
            // The unwind operand (ADR 0027) is ignored: it is abort-path
            // cleanup, and its block never receives a normal-path edge.
            ExprKind::App(f, a, _) => {
                let callee = self.eval(*f, flow, &mut memo);
                let arg = self.eval(*a, flow, &mut memo);
                self.apply_call(callee, arg, flow)
            }
            // An effect abort (ADR 0027): delivery through a captured
            // delimiter — the same out-of-v1-scope shape the computed
            // bare-value delivery was.
            ExprKind::PrimOp(Op::Abort, _, _) => {
                self.set_skip("continuation delivery through a computed callee (effects)");
                vec![]
            }
            // An unwind entry's terminator: entries are only reachable on
            // the abort path, which this pass does not model.
            ExprKind::PrimOp(Op::UnwindDone, _, _) => vec![],
            ExprKind::PrimOp(Op::Br, args, _) => {
                let cond = self.eval(args[0], flow, &mut memo);
                // A branch on a drop-flag with a known per-path state takes
                // only the feasible edge (then = index 0, else = index 1).
                let taken = match cond {
                    AbsVal::FlagRead(cell) => match self.flag_state(flow, cell) {
                        Flag::True => Some(0),
                        Flag::False => Some(1),
                        Flag::Unknown => None,
                    },
                    _ => None,
                };
                let mut edges = vec![];
                for (index, thunk) in args[1..].iter().enumerate() {
                    if taken.is_some_and(|taken| index != taken) {
                        continue;
                    }
                    match self.eval(*thunk, flow, &mut memo) {
                        AbsVal::FuncRef(label) if self.members.contains(&label) => {
                            edges.push((label, AbsVal::Scalar));
                        }
                        _ => {
                            self.set_skip("computed branch target");
                            return vec![];
                        }
                    }
                }
                edges
            }
            ExprKind::PrimOp(Op::Switch, args, _) => {
                let _tag = self.eval(args[0], flow, &mut memo);
                let mut edges = vec![];
                for arm in &args[1..] {
                    match self.eval(*arm, flow, &mut memo) {
                        AbsVal::FuncRef(label) if self.members.contains(&label) => {
                            edges.push((label, AbsVal::Scalar));
                        }
                        _ => {
                            self.set_skip("computed switch target");
                            return vec![];
                        }
                    }
                }
                edges
            }
            _ => {
                // Direct-style body (rare): evaluate for effects, then the
                // value leaves through an ordinary return.
                let value = self.eval(body, flow, &mut memo);
                self.escape(&value);
                self.exit_check(flow);
                vec![]
            }
        }
    }

    /// Interpret a body-position application.
    fn apply_call(&mut self, callee: AbsVal, arg: AbsVal, flow: &mut Flow) -> Vec<(Label, AbsVal)> {
        match callee {
            // Call to a statically-known chunk function (checked before
            // membership: a directly recursive chunk is its own "member").
            AbsVal::FuncRef(label) if self.chunks.contains(&label) => {
                let args = match arg {
                    AbsVal::Agg(items) => items.as_ref().clone(),
                    other => vec![other],
                };
                self.apply_known_call(label, args, flow)
            }
            // Jump to a local continuation: an edge carrying the argument.
            AbsVal::FuncRef(label) if self.members.contains(&label) => vec![(label, arg)],
            // Return: the result escapes to the caller; leak-check the path.
            AbsVal::RetK => {
                self.escape(&arg);
                self.exit_check(flow);
                vec![]
            }
            // A helper belonging to some other unit: shared continuation —
            // not a shape the scheduler accepts either.
            AbsVal::FuncRef(_) => {
                self.set_skip("call to a continuation of another unit");
                vec![]
            }
            // Computed callee applied to a bare value: delivery into a
            // captured continuation (effects) — out of v1 scope.
            _ if !matches!(arg, AbsVal::Agg(_)) => {
                self.set_skip("continuation delivery through a computed callee (effects)");
                vec![]
            }
            // Computed callee with an argument tuple: closure/witness/
            // capability call — no summary; arguments escape.
            _ => {
                let AbsVal::Agg(items) = arg else {
                    unreachable!()
                };
                let args = items.as_ref().clone();
                self.apply_unknown_call(args, flow)
            }
        }
    }

    /// Call to a chunk function: apply its summary (or escape without one),
    /// then follow the continuation argument.
    fn apply_known_call(
        &mut self,
        callee: Label,
        args: Vec<AbsVal>,
        flow: &mut Flow,
    ) -> Vec<(Label, AbsVal)> {
        // The lowerer's convention: dom is Tuple([params…, ret_k]); the
        // last argument is where the callee sends its result.
        let callee_dom_is_tuple = matches!(self.p.ty_kind(self.p.dom(callee)), TyKind::Tuple(_));
        let (plain, cont) = match args.split_last() {
            Some((last, rest)) if callee_dom_is_tuple => (rest.to_vec(), Some(last.clone())),
            _ => (args, None),
        };

        // A local helper (or the parameter bundle) passed as a plain
        // argument installs a handler / captures a delimiter: not a
        // chunk-shaped CFG, so skip the unit loudly.
        for value in &plain {
            if self.contains_local_control(value) {
                self.set_skip(
                    "local continuation passed as a call argument (handler installation)",
                );
                return vec![];
            }
        }

        let summary = self.summaries.get(&callee).cloned();
        for (index, value) in plain.iter().enumerate() {
            match &summary {
                Some(summary) => {
                    let index = index as u32;
                    if summary.escaped.contains(&index) {
                        self.escape(value);
                        continue;
                    }
                    if let Some(freed) = summary.must_freed.get(&index) {
                        for path in freed {
                            if let Some((r, full)) = self.resolve_path(value, path) {
                                let via = format!(" (freed inside {})", self.p.name(callee));
                                self.kill_place(flow, r, full, &via);
                            }
                        }
                    }
                    // Borrow-by-default (ADR 0018): a summarized callee
                    // that neither frees nor escapes a parameter leaves the
                    // caller's ownership intact.
                }
                None => self.escape(value),
            }
        }

        match cont {
            Some(AbsVal::FuncRef(label)) if self.members.contains(&label) => {
                let result = self.mint_call_result(flow, label);
                vec![(label, result)]
            }
            Some(AbsVal::RetK) => {
                // Tail call: the callee returns to our caller; this path
                // leaves the unit here.
                self.exit_check(flow);
                vec![]
            }
            Some(other) => {
                // Continuation is itself a chunk or a computed value —
                // control leaves the unit.
                self.escape(&other);
                self.exit_check(flow);
                vec![]
            }
            None => {
                // No continuation slot: a diverging/trap call.
                vec![]
            }
        }
    }

    /// Call through a computed callee (closure, existential witness,
    /// capability): no summary, arguments escape; the continuation argument
    /// still names where control resumes.
    fn apply_unknown_call(&mut self, args: Vec<AbsVal>, flow: &mut Flow) -> Vec<(Label, AbsVal)> {
        let Some((cont, plain)) = args.split_last() else {
            return vec![];
        };
        for value in plain {
            self.escape(value);
        }
        match cont {
            AbsVal::FuncRef(label) if self.members.contains(label) => {
                let result = self.mint_call_result(flow, *label);
                vec![(*label, result)]
            }
            AbsVal::RetK => {
                self.exit_check(flow);
                vec![]
            }
            other => {
                self.escape(other);
                self.exit_check(flow);
                vec![]
            }
        }
    }
}
