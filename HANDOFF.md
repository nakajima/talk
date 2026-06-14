# Talk Compiler — Handoff Guide

*Last updated: June 11, 2026 (post-M6). Branch: `no-types-no-lowerer` (the
old ~41k-line type system and backend were deleted in 6a602348 "let's get a
fresh start"; everything described here was rebuilt after that commit.
B-M0..M3 are committed in 8433f379 "checkpoint"; M4–M6 are uncommitted in
the working tree.)*

This document is the orientation guide for anyone picking up the compiler.
It covers the architecture, the invariants you must not break, how the work
is verified, where every subsystem lives, and the concrete plan for what
remains.

---

## 1. The ten-minute picture

Talk is a statically-typed language with protocols, effects, and mutable
value semantics. The compiler pipeline:

```
source ─ parse ─→ AST ─ resolve ─→ AST(NameResolved) + ResolvedNames
       ─ type_check ─→ TypeOutput            (OutsideIn(X); src/types)
       ─ lower ─→ λ_G Program                (CPS soup IR; src/lower, src/lambda_g)
       ─ schedule ─→ bytecode Module         (chunks/blocks/registers; src/vm/schedule.rs)
       ─ run ─→ value + IO                   (frame-stack VM; src/vm/interp.rs)
```

Two execution engines exist on purpose:

- **Reference evaluator** (`src/lambda_g/eval.rs`) — a definitional
  interpreter for the small-step semantics of the λ_G paper (Leißa &
  Griebler §3.4; see §3 below). It is the *executable specification*.
  Slow (substitution-based), always captures stdout.
- **Bytecode VM** (`src/vm/`) — the product. Every language construct is
  **tested on both engines**: the same program runs on each and the value
  *and* captured stdout must agree, so a bug would have to appear
  identically in two implementations that share almost no code.

Driver phases (`src/compiling/driver.rs`): `Parsed → NameResolved → Typed →
Lowered`. `Driver<Lowered>` exposes `eval_with_output()` (reference evaluator),
`run_vm()` / `run_vm_with_output()` (VM), and carries `entry_funcs` (see
§4.2).

### Commands

```sh
cargo test                                   # full suite; ALWAYS run before claiming done
cargo test --test examples                   # example expected-output tests only
cargo build --features cli
./target/debug/talk run file.tlk [more.tlk]  # parse→…→VM
./target/debug/talk repl                     # REPL (evaluates on the VM)
```

### Status at a glance

| Piece | State |
|---|---|
| Type system (OutsideIn(X), effect rows, record rows, projections) | **Complete** — all 27 `examples/*.tlk` + core prelude check clean |
| B-M0 λ_G calculus core | **Done** — verified against the paper's own figures |
| B-M1 AST→λ_G CPS lowering (worklist mono, witnesses, cells, loops) | **Done** |
| B-M2 scheduler + register bytecode + VM, `talk run`, REPL | **Done** |
| B-M3 records/inits/inout, strings/statics, IO, literal match, multi-file | **Done** |
| B-M4 enums + Maranget decision trees + Optional, record/tuple patterns, destructuring lets | **Done** |
| B-M5 arrays, sized memory + arena, conditional conformance, iterators, derived show | **Done** |
| B-M6 closures (MakeClosure/EnvGet/CallIndirect), trailing blocks, sleep | **Done** |
| B-M7 abort effects (lexical handlers, capability-passing CPS) | **Done** |
| B-M8 full io dialect (files, sockets, poll; servers run for real) | **Done** |
| B-M9 resumable handlers (`continue v`; one-shot by construction) | **Done** |
| Feature parity with the previous backend (playground wasm, `talk lower`/`hover`, open_path, hover) | **Done** (see below) |
| Type-system GADTs; tail-resumptive fast path; dynamic io_perform; computed globals; multi-shot | **Next** (§7) |

**Examples running today** (both engines; stdout frozen or value asserted):
HelloWorld, Strings, Struct, Identity, Loop, Imports(+Exports), Fib,
MatchBind, StructuralTyping, Array, Sum, Iteratin, ForLoop, Protocols,
Show, AnonFunc, Capture, TrailingBlock, Sleep, Effects, FileIO,
ChatClient — 22 of 27. The other four (ChatServer, Http, WebApi,
Website) are servers that loop forever: they lower and verify under
test, and serve real sockets under `talk run` (curl/nc them). Test
counts: 478 lib tests + 23 example tests, 0 failures (5 pre-existing
ignores).

### Parity with the previous backend (audited against the pre-rewrite tree)

Everything the old system *shipped* works again. Restored this pass:
the playground's wasm `run_program` (a non-persisting `ReplSession::
eval_program` — the REPL's persist shortcut would have swallowed
programs that begin with a declaration) and `show_ir`
(`driver::render_lowered`, née render_ir; both were stubbed "pending rewrite" and
www/assets/page.js calls them); `talk lower` (plain function-syntax
rendering; `talk ir` now prints the VM bytecode listing) and `talk
hover`; wasm
`hover` (new `analysis/hover.rs` over `TypeOutput.node_types`/
`schemes`; the Workspace now keeps the checker's tables); and
`open_path`/File.tlk (rewritten in pure Talk — copy the path with a NUL
into fresh zeroed memory, then `_io_open`; verified against a real file
through libc). The wasm crate builds for wasm32-unknown-unknown.

The deltas found in the first audit are closed: the REPL and
playground render values Talk-style (`2`, `1.5`, `"hi"`,
`Point(x: 1, y: 2)`, `Optional.some(5)` — `interp::run_displayed`
renders while the machine is alive, since strings point into its byte
memory, with names from the checker's catalog via `value_names`);
hover renders imported names (`Showable`, not a raw symbol — the
checker's merged display map is exported as
`TypeOutput::display_names`); and hover-by-node-id works in both the
playground and `talk hover --node-id` ("index" or "file:index").

Two non-deltas, for the record: the old async executor (tasks/wakers)
was unfinished work no example or test ever exercised — resumable
handlers (M9) are the foundation its replacement will build on; and
the old `benches/` files were already disabled (renamed `.rs.txt`) in
the old tree, so there is no benchmark harness to restore.

### Test-coverage parity (docs/parity-test-audit.md)

Every test of the old tree is dispositioned in
`docs/parity-test-audit.md`: the 127 interpreter tests are each
covered/ported/adapted (45 new two-engine tests, including the five
scripted HTTP `handle()` tests and a real-socketpair StdioIO check),
and 164 of the 183 old type-checker cases replay verbatim in
`previous_checker_suite_behaviors_hold`. The audit drove a round of
real fixes — every one was silent or a compiler panic before:

- **Explicit `func main`** runs as the entrypoint (top-level
  statements first, main's value is the program's).
- **Anonymous-record member access** (reads, assignment, and *nested*
  assignment `a.b.c = 2`): records are λ_G tuples, so members are
  extracts and functional updates rebuild the tuple (`field_get`/
  `field_set`); struct paths keep GetField/SetField.
- **Functions mutating top-level bindings** (`top_level_cells`: the
  cell is a free variable of main; closure conversion carries it,
  exactly like handler capabilities).
- **Block/main value types come from the FINAL node only** — a
  trailing loop or assignment yields Void (the old rev-scan typed
  main's return from an earlier expression and panicked the IR
  builder).
- **Unannotated lets take the rhs's inferred type** (value-directed),
  so variant patterns on the binder see a concrete enum.
- **Self-contained handlers** (`@handle` + performs inside one
  function) no longer force the abort-capable convention on the
  function or its callers (`handlers_defined` subtraction +
  `Ctx::local_handlers`).
- **Solver-inferred associated-type bindings are written back** to
  conformance rows, so protocol defaults specialize correctly when the
  witness has no return annotation (the pet-food example).
- **Parametered trailing blocks** (`transform(10) { n in n * 2 }`) —
  the closure's shape comes from the callee's declared parameter.
- **Negative io counts pass through** (the chat client's
  errno-into-write loop) instead of trapping.
- **let-else / if-let / or-patterns pinned**; or-pattern lets desugar
  through the match machinery, and or-alternatives' binders must agree
  in type; generic effects instantiate per perform site; extra
  explicit type args and handler-block arity mismatches are errors
  again.

Four of the audit's gaps were since promoted to features and built:
**generic methods** (declared generics ride member schemes,
instantiated per call and monomorphized per instantiation), **methods
on enums** (registered like struct methods, dispatched in the solver's
member lookup, owner-θ'd in the lowerer), and **row-polymorphic record
projections** (`func f(r) { r.a }`): a member constraint that no
nominal or protocol owns defaults its receiver to an open record row
at the solver's improvement step (presence constraints as row
unification — Gaster & Jones, POPL 1996; Leijen, Trends in FP 2005);
the row tail generalizes into the scheme's row parameters, row
instantiations are recorded per call site, and `Ty::substitute`
splices each concrete row into the signature so monomorphization
computes field indices per specialization. And **scheme-carried
member constraints** (true qualified types — Jones 1994):
`func g(x) { x.someMethod() }` generalizes; a member use stuck on a
group-owned receiver is held through generalization and attached to
every scheme quantifying it (`Scheme.member_constraints`), each
instantiation re-emits it as a fresh wanted against the call's
receiver, and the lowerer resolves the member per specialization by
label (struct/enum methods, then protocol witnesses). Unique-owner
improvement no longer commits inside binding groups — it survives
only as last-resort defaulting in the final solve (`Solver::
defaulting`), so a receiver owned by one struct stays polymorphic and
a record with the same field also discharges the constraint. Schemes
render the qualification (`<T0, T1>(T0) -> T1 where T0.val: T1`). All
four run on both engines. When two conformed protocols (or two
bounds) both provide a label, plain `x.m()` is an **ambiguity error**
— committing to either would make meaning depend on table order
(overlapping instances, Jones 1994 §2.4) — and the message names the
explicit protocol-static forms (`Aa.m(…)` or `Bb.m(…)`), which is the
disambiguation syntax (the shape operators already desugar to). The
LSP additionally offers one quick-fix per candidate rewriting
`x.m(args)` into `P.m(x, args)`. Pinned by `ambiguous_member_*` and
`protocol_static_call_steers_an_ambiguous_member` in types_tests,
`ambiguous_member_quick_fix_offers_each_protocol` in lsp tests, and
the matching vm test. `(x as P).m()` does not steer resolution: `as`
with a protocol annotation is part of the existentials gap below.

Known gaps still documented rather than fixed (each loud, none silent
— see the audit doc): Showable for function values, protocol-typed
values (existentials), and partially-concrete inherent extends.

---

## 2. House rules (non-negotiable)

These come from the project owner and are standing policy:

1. **TDD.** Write the failing test first. Every behavior change carries a
   meaningful test; every bug fix carries the test that would have caught it.
2. **Cite the research, liberally.** Every component is a faithful
   implementation of published work. Module docs name the papers; functions
   cite paper + section; *deviations are explicitly flagged in comments*.
   No ad-hoc reinvention.
3. **Correctness beats implementation simplicity.** When in doubt, do the
   sound thing and leave the optimization documented.
4. **No TODOs.** Unsupported constructs surface as lowering diagnostics or
   runtime `Trap` instructions with a milestone note — honest, not silent.
5. **Negative diffs preferred.** Before adding code: remove duplication, use
   existing utilities, simplify.
6. **The assistant does not run git write operations.** Commits are the
   owner's. (Read-only git is fine.)
7. `cargo test` must be green before any task is called complete. Never add
   `#[ignore]`.
8. Crate-level lints **deny `unwrap`/`expect`/`panic` outside tests** — all
   runtime code is `Result`-based. The one sanctioned exception:
   `Program::app()` panics via `unreachable!` on ill-typed IR construction,
   because that is by definition a lowerer bug (the checker accepted the
   program; preservation through lowering is our obligation).
9. **Plain language, no insider jargon** in docs, comments, and names: say
   "reference evaluator", not "oracle"; "expected-output file", not
   "golden"; "runs on both engines and must agree", not "differentially
   tested". Paper citations are required (rule 2); cryptic vocabulary is
   not. If a standard term earns its place, introduce it once with its
   meaning spelled out.

---

## 3. The canonical ssa spec: `ssa-paper.md`

The IR is **λ_G** from Leißa & Griebler, *SSA without Dominance for
Higher-Order Programs* (arXiv:2604.09961v2). The full text lives in the repo
at **`ssa-paper.md`** and is the canonical reference for `src/lambda_g/` —
when code comments cite "§3.1.1" or "Fig. 8", that's the document. Read §2–§4
before touching the IR. The one-paragraph version:

A program is a flat map *label → function*. Each function has exactly **one
variable** (`var ℓ`, tuple-typed for multi-param). Bodies may be temporarily
unset (↑) to tie recursive knots. There is no dominance: well-formedness is
free-variable **nesting** (Thm. 1: nesting ⟹ dominance). Functions whose
codomain is ⊥ are continuations = basic blocks = join points. Inlining,
monomorphization, and loop peeling are all the same operation:
dependency-aware β-reduction. Expressions are immutable and hash-consed —
**sharing IS let-binding**.

The approved backend plan (with the foundations table mapping every
component to its paper) is inlined in the repo at
`docs/backend-plan.md`.

---

## 4. Subsystem tour

### 4.1 `src/types/` — OutsideIn(X) (complete, ~6.4k lines)

- `generate.rs` — constraint generation per binding group (own
  free-variable dependency analysis à la THIH §11.6.2 — the resolver's SCC
  graph lacks method-body edges, which once caused `_io_write` to be
  exported monomorphic; don't regress this).
- `solve.rs` — the solver: equalities over types-with-rows, `Conforms`,
  `HasMember` (Gaster & Jones); records `member_resolutions` at constraint
  origin nodes. Rémy levels for generalization (and future GADT
  untouchability).
- `output.rs` — **the contract with the lowerer**: `TypeOutput { catalog,
  node_types, schemes, instantiations, member_resolutions }`. The lowerer
  never asks the checker questions; it only reads these tables.
- `catalog.rs` — structs (ordered fields!), enums (`VariantInfo.result` is
  the GADT hook), protocols/requirements, conformances (with `context` for
  conditional conformance), effect signatures.

GADTs (type-system M8) are architected-for but not built: levels, `Implic`
constraints, and `VariantInfo.result` are the prepared hooks.

### 4.2 `src/lambda_g/` — the calculus (B-M0, ~2.5k lines)

- `expr.rs` — `TyKind` (incl. `Boxed(Symbol)` records, `Variant(Symbol)`
  enums, `Cell(TyId)`), `Const` (incl. `Slot` cell handles, `StaticPtr`
  addresses, `Byte`), `Op` (the full `@_ir` dialect + `Br`/`Switch` as
  primops — a flagged deviation from the paper's builtin `br_T`),
  `ExprKind`. Every expr stores its type and LV/LF sets at construction.
- `program.rs` — interned types/exprs, function table with unset bodies,
  users-set invalidation, `static_mem: Vec<u8>`, typed builders
  (`app` panics on lowerer type errors — see §2.8).
- `fv.rs` — mark/run FV fixed point, exactly §3.1.1 (Table 1 is a test).
- `subst.rs` — dependency-aware substitution + β (Eqs. 14–18; stubs for
  recursion).
- `nest.rs` — nesting tree + sibling SCCs (Fig. 8, Tarjan).
- `check.rs` — T-rules + WF verifier. Primops carry their result type, so
  new ops need no verifier changes.
- `eval.rs` — the reference evaluator. **Trampolined**: a CPS spine's depth equals
  execution length, so tail `App`/`Br`/`Switch` iterate (`Step::Done/
  Continue`) instead of recursing. Machine state (cells, byte memory)
  lives in the Evaluator; values reify back into the term language as
  constants/`RecordNew`-of-values (values are a sub-grammar of expressions —
  this is load-bearing for E-β).
- `print.rs` — paper-style text (`hi ↦ λ int → ⊥. …`); future `show_ir`.

### 4.3 `src/lower/` — AST + TypeOutput → λ_G (~1.9k lines)

One file (`mod.rs`) so far. The shape:

- **Worklist monomorphization** (MLton/rustc collector; Jones PEPM 1994):
  `demand(symbol, θ)` interns a specialization label keyed
  `(Symbol, ThetaKey)` and queues the body; `θ` composes per-call-site
  `instantiations` with the enclosing specialization (monomorphic recursion
  inherits bindings — THIH §11.6.3).
- **Everything is CPS**: a Talk function `(T…) -> R` becomes
  `Fn([T…, Fn(R,⊥)], ⊥)`; `ret_k = Extract(var F, arity)`. Returns apply
  `ctx.ret_k`; calls chain arguments through `arg` continuations
  (left-to-right, impure args only).
- **Assignment conversion** (ORBIT, Kranz 1986): mutated locals/params →
  cells, bound through continuations (`with_cells`) so each `CellNew`
  occurs exactly once. `Ctx.cellable` = resolver's `mutated_symbols` ∪
  receivers of mutating-method calls (found by an AST scan in
  `cellable_symbols` — **the resolver only tracks assignments**, so
  `c.bump()` would otherwise leave `c` un-celled).
- **Witnesses**: `member_resolutions` → `Direct(symbol)` or
  `ViaConformance{protocol, witness}`; the latter resolves through the
  conformance table to a witness fn or a protocol default body demanded at
  `θ{Self := head, assoc bindings}`.
- **Records are pure values**: construction = `RecordNew`, reads =
  `GetField`, update = functional `SetField`; mutation exists *only* via
  cells.
- **Enums mirror records** (M4): construction = pure `VariantNew(enum, tag)`
  (tag = declaration index), projection = `GetTag`/`GetPayload(i)`.
  `.some(x)`/`Optional.some(x)`/bare `.none` resolve through
  `member_resolutions` (checked at the *call* node for leading-dot calls,
  the *member* node otherwise — `variant_target` looks at both); the
  lowerer intercepts variant symbols before `lower_call`, so no function is
  demanded. `map_ty` sends enum nominals to `TyKind::Variant` (type args
  erased — already monomorphized).
- **Anonymous records are tuples** in canonical label-sorted order
  (`Row::closed` sorts; `map_ty` on a closed `CheckTy::Record` and literal
  lowering agree on the layout). Fields evaluate in source order, then
  permute into row order. Open rows are diagnosed.
- **Inits**: `Person(args…)` resolves (checker's `member_resolutions` on the
  callee node) to an init symbol whose AST has `self` prepended (the
  resolver synthesizes memberwise inits as real ASTs). Lowering passes a
  **blank record** (all fields Void — honest poison) as self;
  the init body fills fields and returns self.
- **Inout self** (Racordon JOT 2022): `mutating` set = methods whose
  `params[0]` is named `self` and is in `mutated_symbols` (inits excluded).
  Their ret continuation carries `[result, Self]`; `lower_function` wraps
  `ret_k` to attach `CellGet(self_cell)`; `lower_call` installs a
  `writeback` adapter continuation that `CellSet`s the receiver and passes
  the result on.
- **Strings**: literals unescape via `crate::parsing::lexing::unescape`,
  intern (deduped) into `Program::static_mem`, and build
  `RecordNew(String, [StaticPtr, len, len])`.
- **`@_ir` splices**: binds (`$n`) must be pure; `%n` = enclosing params;
  type args (`load Element`) resolve through θ (`splice_ty`).
  **The checker does not type-check `@_ir` binds** (trusted, fresh-var
  result) — so field reads inside binds resolve *by name* against the
  receiver's λ_G `Boxed` type (`field_read`'s fallback path).
- **Constant globals** (`public let STDOUT_FD: Int = 0`): indexed into a
  `globals` table and inlined at use sites (literals only; computed globals
  are an M8 problem).
- **Match** (`patterns.rs`, M4): the full Maranget decision-tree compiler
  (ML 2008). Variant columns → `Switch` over `GetTag` (one continuation
  per declared tag; absent tags and the switch default point at a shared
  *bodyless* `match_failed` function, which both engines surface as a
  trap); literal columns → equality chains; or-patterns → row expansion;
  tuple/record columns expand in place. Arm bodies lower exactly once,
  as join-point continuations taking the arm's binders as a tuple
  (binder types come from occurrence λ_G types at the first leaf).
  Occurrences carry their *checker* types alongside λ_G values — payload
  types come from `VariantInfo.payloads` substituted with the scrutinee's
  enum args. Note: `{ y: pat }` binds `y` *and* matches `pat` (the
  checker binds both). The checker proves coverage *before* lowering:
  `src/types/exhaustiveness.rs` (Maranget JFP 2007 usefulness) errors on
  non-exhaustive matches with example values and warns on unreachable
  arms (`Severity::Warn` — the first warning-severity diagnostic), so
  `match_failed` really is unreachable from checked code.
- **Destructuring lets** (M4): irrefutable record/tuple lhs patterns bind
  via `collect_irrefutable_binds` (Extract chains). The checker routes
  top-level destructuring lets through `check_local_decl` with the phase-2c
  statements (they bind monomorphically — no scheme, no binding group).
- **θ recovery for owners** (M5, `owner_theta`): methods/inits of a generic
  struct and inherent-extend members range over their *owner's* rigid
  params, which the checker discharges by head substitution (solve.rs
  `try_member`) — no instantiation is recorded. The lowerer re-derives the
  bindings by matching the declared self type against the concrete head
  (`bind_param_pattern`, shared with the solver). Same move in
  `resolve_witness` for conditional conformance rows: `self_args` matched
  against head args gives the witness θ (instances with contexts — Hall et
  al., TOPLAS 1996; the context needs no re-check, the checker proved it).
- **Inits return self** (M5): whatever the body's final value, `demand`
  rewrites an init's signature ret to Self and `lower_function` wraps its
  ret continuation to deliver self's current state (cell read) — core
  inits don't end in `self`.
- **Array literals** (M5): `[1, 2, 3]` allocates `count · mem_size(elem)`
  bytes (alloc bound through a continuation — it must run exactly once),
  stores each element through its own continuation (source order), then
  builds the `Array` record {storage, count, capacity}. `_alloc<Element>`
  is generic; `alloc`/`gep` splices scale by `TyKind::mem_size`; `gep`
  lowers to pure pointer arithmetic (no runtime op).
- **Derived Showable** (M5, `derive.rs`): no conformance row exists for
  auto-derived protocols, so `resolve_witness` falls back to synthesizing
  the `show` body directly in λ_G (switch over tags / fields folded
  through the `String: Add` witness). Format matches the old
  implementation: `Name.variant(payloads…)`, `Name(field: v…)`,
  `Name {}`.
- **Function values** (M6): a literal lowers to a λ_G function whose body
  sees the enclosing environment — free variables ARE the captures; the
  reference evaluator runs them by dependency-aware substitution (subst.rs
  Eq. 17/18 specializes nested functions at E-β — no evaluator changes
  were needed). The lowerer marks literals/trailing blocks `escaping`
  (they join `entry_funcs` as chunks); calls through local bindings or
  literals apply the value directly (`lower_value_call`). Trailing blocks
  are zero-param closures appended as the final argument (parametered
  trailing blocks need checker-recorded block signatures — flagged).
  Known-call optimization (η-expansion for mixed known/unknown
  occurrences, paper §3.5) is deliberately skipped: every literal is a
  closure, correctness first.
- **Performs**: one routed to a lexical handler by the resolver calls
  the handler's capability closure (`lower_routed_perform` — M7, §7).
  An unhandled `'io(.op(…))` whose request is a *syntactic* variant
  routes statically to its io primop (`lower_perform` — all twelve
  IORequest operations as of M8). Both engines marshal through the
  same `IO` trait (StdioIO = libc/host, CaptureIO = simulated
  descriptors; the evaluator owns a CaptureIO).
- **`lower_main`**: synthesizes `main : [Fn(R,⊥)] → ⊥` from the entry
  unit's top-level statements (all files of the unit, in source order);
  `R` = the final top-level expression's type (block-final if/else counts).

Output: `LoweredProgram { program, main, result_ty, entry_funcs,
diagnostics }`. **`entry_funcs`** (demanded specializations + main) is
producer knowledge the scheduler depends on.

### 4.4 `src/vm/` — scheduler, bytecode, interpreter, IO

- `schedule.rs` — λ_G → `Module`. Each entry func = a **chunk**; its
  reachable continuations = **blocks** sharing one register frame (one
  param register per continuation). Call/return reconstruction per Thorin
  (CGO 2015): `App(chunk_fn, Tuple[args…, k])` → `Call`+`Jump` (k = owned
  block) or `Call`+`Ret` (k = ret continuation; **no TCO yet** — flagged);
  `App(cont, v)` → `Move`+`Jump`; `App(ret_k, v)` → `Ret`; `Br` →
  `Branch`; `Op::Switch` → a jump-table `Insn::Switch` whose targets live
  in `Module::switch_pool` (default last; per-chunk offset patching walks
  each instruction's pool range). Value trees emit per block with **pure-only value numbering**
  (`memo`): cell/memory/IO ops re-emit per occurrence, matching the
  reference evaluator's re-evaluation of shared occurrences. **Flagged deviation**:
  block ownership is Func-reference *reachability* from each chunk, not
  the paper's §4 FV nesting tree — closed continuations (constant-bodied
  thunks) have empty FV and would float to the forest root. A continuation
  referenced by two chunks is a hard error.
- `mod.rs` — `Insn` (unpacked fixed-shape enum, resolved jump targets,
  pooled consts/args/traps), `Chunk`, `Module` (carries the statics image).
  `MemKind` (M5) picks one memory access per λ_G type: Byte = 1 byte,
  scalar words = 8 bytes little-endian, aggregates = 8-byte handles into
  the machine's boxed arena (`Machine::boxed` here, `Evaluator::boxed` in
  the reference evaluator — Leroy POPL 1992's mixed representation;
  byte-packing Bool is a flagged later optimization). Closures (M6) are
  flat (Cardelli LFP 1984): `schedule` precomputes every chunk's sorted FV
  list (`env_of` — one layout shared by `MakeClosure` capture sites and
  the chunk's own `EnvGet` reads, so `schedule` now takes `&mut Program`
  for the FV caches); `Value::Closure(chunk, Rc<env>)`, frames carry the
  env, unknown callees go through `CallIndirect` (the old computed-call
  trap is retired). Capturing a chunk's own params materializes their
  tuple; capturing a *return continuation* stays out of reach until M9.
  Register-bytecode semantics per VEE 2005 / Lua 5.0; byte-packing is a
  later mechanical step.
- `interp.rs` — frame-stack interpreter, `match` dispatch (Ertl & Gregg).
  `Value`: scalars + `Ptr(u32)` into one byte memory (statics ++ bump
  heap), `Record`/`Tuple` as CoW `Rc`s, `Cell(usize)` into a slot arena.
  Frames are plain data (M9 continuation capture will copy them — Hieb,
  Dybvig & Bruggeman 1990). `MAX_FRAMES` bounds runaway recursion.
- `io.rs` — the IO boundary: `trait IO { write(fd, bytes) }` with
  `StdioIO` (talk run) and `CaptureIO` (tests, REPL). The reference evaluator always
  captures into `Evaluator::out` instead.

### 4.5 Entry points

- `src/bin/talk.rs` — `Run` walks the full pipeline and prints non-Void
  results / diagnostics.
- `src/repl.rs` — eval via `run_vm_with_output()`; `/type` via the checker.
- `src/compiling/core.rs` — caches the typed core prelude
  (`CoreTyped { asts, types, resolved_names }`) so user compiles get
  core as lowering unit 0.

---

## 5. Testing strategy (and how to extend it)

1. **Paper fixtures** (`src/lambda_g/lambda_g_tests.rs`): the calculus is
   tested against the paper's own worked examples. If you touch
   fv/subst/nest, these are your guard rails.
2. **Two-engine tests** (`src/vm/vm_tests.rs`):
   `run_on_both_engines(code)` and `run_on_both_engines_io(code)` run a
   source on both engines and assert equal value + stdout. **Every new
   construct gets one of these first.** Both harnesses (and the example
   tests) also run the **post-lowering verifier** (`Program::verify`:
   T-Prog + WF) on every program. Ordering rule: run the VM before
   the evaluator — the evaluator mutates the Program (substitution adds
   functions).
3. **Example expected-output tests** (`tests/examples.rs` +
   `examples/expected/*.stdout`): each runnable example executes on both
   engines and must match the frozen stdout file. Grow the list every
   milestone; the end state is all 27.
4. **Lowering unit tests** (`src/lower/lower_tests.rs`): evaluator-only
   tests from M1 (arithmetic, branches, mono, fib, loops).
5. The formatter smoke test iterates `examples/*.tlk` — it skips non-`.tlk`
   entries (that's why `examples/expected/` must hold only expected-output
   files).

Debugging tips that paid off:
- `Program::try_app`'s error now renders types and exprs — a T-App panic
  message like `argument type () does not match domain int (callee arg#33)`
  almost always means a lowering path delivered the wrong value to a
  continuation; check for an unhandled `ExprKind` falling into a
  `k(void)` diagnostic arm.
- Lowering diagnostics print at the *end*; a construction panic preempts
  them. If diagnosing blind, run the same source through
  `./target/debug/talk run` (rebuild the CLI first — stale-binary confusion
  cost us an hour in M3).
- `splice` names the exact failing bind (`@_ir bind $1 is not pure …`).

---

## 6. Gotchas / invariants (read before coding)

- **Hash-consing means structurally-equal exprs are the same node.** Any
  side-effecting primop must be (a) bound through a continuation by the
  lowerer if it must execute exactly once (cells), or (b) consistently
  re-emitted per occurrence by both engines (IO/memory ops). Never memoize
  impure ops in the scheduler.
- **Parenthesized expressions parse as 1-tuples.** Both `try_pure` *and*
  `lower_expr` need the unwrap arm; `()` is the empty tuple = Void.
- **Statement-position `@_ir` has an unconstrained tyvar.** `map_ty`
  defaults residual `CheckTy::Var` to Void (sound: the checker accepted the
  program, so the value is unconstrained), and `discard_then` types its
  drop continuation from the *lowered value*, not the checker residue.
- **Methods and inits have explicit `self`** in their resolved ASTs
  (`PrependSelfToMethods`); `func.params[0]` is self. Operator expressions
  (`-x`, `a + b`) are desugared to method calls before typing — the lowerer
  never sees `Unary`/`Binary`.
- **Continuation conventions**: real functions take
  `Tuple[params…, Fn(R,⊥)]`; continuations take a single value and are
  entered only via `Func` refs (or as a call's k). The scheduler's
  `is_ret_k` recognizes `Extract(var F, arity)`.
- **`parser requires a newline after `continue`** (it tries to parse an
  expression otherwise) — test sources must put `continue` on its own line.
- **Don't trust `mutated_symbols` for receivers** (assignments only); use
  `cellable_symbols`.
- The dead-function path in `demand` (no callable signature) produces a
  bodyless chunk that schedules as a `Trap` — diagnostics stay attached to
  the `Lowered` phase either way.

Current performance debts, in payoff order (all flagged in code):
β-inline trivial witness wrappers (M0's subst does this), TCO, register
reuse, packed bytecode + threaded dispatch.

---

## 7. Roadmap

Milestone table from the approved plan; per-milestone detail below.

| M | Contents | Unlocks |
|---|---|---|
| M4 | enums (variant/get_tag/switch), Maranget trees, record patterns, Optional | **Done** — MatchBind, StructuralTyping |
| M5 | generic structs, Array (+`_alloc` fix), conditional conformance, iterators, slot arena, derived show | **Done** — Array, Sum, Iteratin, ForLoop, Protocols |
| M6 | closure conversion + trailing blocks + statically-routed sleep | **Done** — AnonFunc, Capture, TrailingBlock, Show, Sleep |
| M7 | abort effects via capability-passing CPS | **Done** — Effects |
| M8 | full io dialect; scripted loopback tests; servers run for real | **Done** — FileIO, ChatClient (+ Chat/Http/WebApi/Website served live) |
| M9 | one-shot resumable handlers (resumption reified at the perform; `continue v` resumes) | **Done** — groundwork for yield / 'async |

### M4 — done

Everything landed as planned (see §4.3/§4.4 for where it lives):
runtime variants on both engines, construction lowering, the Maranget
compiler in `src/lower/patterns.rs` (M3's single-column chain deleted),
the jump-table `Insn::Switch`, record/tuple patterns in arms *and*
destructuring lets (which needed a small checker change: top-level
destructuring lets check with the phase-2c statements), tuple literals,
anonymous record literals, and the post-lowering verifier folded into
every test harness. One scope note: match exhaustiveness is *not yet
checked* — a non-exhaustive match compiles, and the uncovered paths hit a
bodyless `match_failed` function (VM `Trap`, evaluator `UnsetBody`).
Checker-side exhaustiveness (Maranget's usefulness algorithm) is a good
M5+ companion piece.

### M5 — done

All landed (see §4.3/§4.4): generic `_alloc<Element>` (Net/Http callers
made explicit `<Byte>`; core also gained `_store<Element>`), sized
`Load`/`Store` + `gep` splices, the aggregate arena (Array-of-struct
round-trips on both engines), array literals, conditional conformance
through `self_args` matching, iterators over the existing inout machinery,
and derived show synthesized in λ_G. Scope notes: **`for` statements are
still not lowered** (no target example uses one — ForLoop.tlk iterates
manually; wire the desugar onto Iterable when an example needs it), and
the checker still can't match variant patterns on an *unannotated*
assoc-projection scrutinee (`match it.next()` — annotate a let binding;
checker-side fix is deferring variant-pattern resolution to the solver).
Exhaustiveness checking also remains open from M4.

### M6 — done

All landed (see §4.3/§4.4): function literals, mutable capture through
cells, flat VM closures + `CallIndirect`, trailing blocks, and a
statically-routed `sleep` perform (an M8 slice TrailingBlock/Sleep
needed). Scope notes: the parser does NOT chain a call onto a literal
(`func(x){…}(123)` is a declaration plus a parenthesized statement —
AnonFunc.tlk's value is 123); parametered trailing blocks and computed
callee *expressions* (e.g. `f()()`) are diagnosed, not lowered; every
literal is a closure (the known/unknown occurrence split of paper §3.5 is
a flagged optimization).

### M7 — done (abort effects, capability-passing CPS)

Landed entirely in `src/lower/mod.rs` — zero new VM instructions, zero
evaluator changes, zero scheduler changes, exactly as the design
predicted. Effects.tlk runs on both engines (frozen "whoops"); the
two-engine tests in `src/vm/vm_tests.rs` pin the load-bearing cases:
abort skipping the rest of the scope, the perform two call levels below
the scope (the Ret chain), the normal path running the reified rest
exactly once, the handler's value becoming the scope's value, and a
handler capturing a local.

**As built** (names in code):

- **Capability tables** — the checker *discharges* routed performs from
  effect rows (the lexical-handler reading: a handled effect is not part
  of a function's interface — Brachthäuser et al., OOPSLA 2020), so rows
  cannot tell the lowerer which calls can abort. Instead the checker
  records the facts as it discovers them, exported in `TypeOutput`:
  `performs_into` (binder → handlers, written at the discharge),
  `binder_refs` (binder → referenced symbols, written in
  `lookup_symbol_ty` — a conservative superset of calls), and
  `handler_payload_tys` (zonked at finalize, so unannotated effect
  parameters get the types the perform sites taught them). The lowerer's
  `collect_abortable` is just a transitive closure over those tables:
  `abortable: symbol → handler symbols`. Method-call edges are not in
  `binder_refs` (member resolution happens in the solver, not at name
  lookup); calls to abort-capable methods are diagnosed at the call
  site, which is also the M7 support boundary.
- **Abort-capable shape**: a specialization in `abortable` takes
  `[params…, normal_k, slot]`, where `normal_k : Fn([R, Fn(S,⊥)], ⊥)`
  is an explicit normal-return continuation and `slot : Fn(S,⊥)` is the
  function's own machine return, reserved for abort propagation (S =
  the handler scope's value type). The body's `ctx.ret_k` is wrapped to
  `App(normal_k, [v, slot])`; `ctx.raw_ret_k` keeps the raw slot.
- **`@handle` → `lower_handling`**: the handler block becomes an
  escaping capability closure `handler : Fn([payloads…, slot], ⊥)`
  whose body delivers the handler's value along its own slot — so the
  handler's value is the scope's value (Plotkin & Pretnar, LMCS 2013).
  The capability is registered in `handler_caps`; the handled scope
  (the rest of the enclosing block) lowers in place.
- **Routed performs → `lower_routed_perform`**:
  `App(cap, [payloads…, own slot])`. The capability closure reference
  is embedded directly (routing is lexical and static) and the M6
  FV/escaping machinery carries any captured locals; nothing after the
  perform is emitted (the effect returns Never).
- **Call sites → `try_abortable_call`**: a statement-spine call to an
  abort-capable function reifies the rest of the block as an escaping
  closure `after_abortable : Fn([result, slot], ⊥)` and becomes
  `App(callee, [args…, after_abortable, own slot])` — Call+Ret in the
  VM. On normal completion the callee enters the closure exactly once;
  on abort the closure is skipped entirely and the handler's value
  rides the machine Ret chain back through every intermediate frame.
  The Ret chain IS the abort path: no unwinder, no handler stack
  (abort as unwinding — Hillerström et al., FSCD 2017 §4.5).
- `rebase_into_closure` — code moved into one of these closures has its
  return linkage rebased onto the closure's own slot (re-pointed at the
  enclosing function's `normal_k` where there is one, captured as an
  ordinary value). This keeps the scheduler's "no foreign ret
  continuations" rule (`captured_value`) intact.

**Deltas from the pre-implementation sketch** (research record below):
capabilities did not become hidden *parameters* — lexical routing means
each perform references its handler's closure directly, and closure
conversion does the rest. What every abort-capable function does thread
is the explicit normal-return continuation, with the machine-return
slot doubling as the abort linkage. The scope-split closure J vanished:
with the M7 scope running to the end of the enclosing function,
"everything after the scope" is just the return slot.

**M7 scope limits — all diagnosed, none silent**: `@handle` in a nested
block (the scope must run to the enclosing function's end);
abort-capable calls off the statement spine (nested expression
positions, if-branches, loop bodies); abort-capable inits, inout
methods, and method receivers; trailing blocks on abort-capable calls;
performs inside function values (their call sites are indirect, so the
abort linkage cannot thread through); abort-capable functions used as
values; more than one handler per function; resumable (non-Never)
effects → M9. One frontend gap remains: the checker does not yet
require the handler block's value type to equal the scope's — the
lowering's types make the verifier catch a mismatch; a checker rule
would be friendlier.

#### The compilation-strategy landscape (researched June 2026)

Four families, all with peer-reviewed correctness stories:

1. **CPS translation** — Hillerström, Lindley, Atkey & Sivaramakrishnan,
   *Continuation Passing Style for Effect Handlers* (FSCD 2017): handlers
   compile to plain λ-calculus with "no special support in the target
   language's runtime"; the naive curried translation is fixed by
   uncurrying (tail recursion) and a higher-order one-pass translation
   (administrative redexes), proven by simulation (Thm. 7). §4.5 is the
   abort precedent: "raising an exception need only unwind the stack and
   need not capture the continuation … computations which raise
   exceptions but do not perform other effects may be retained in
   direct-style in a selective CPS translation."
2. **Evidence passing** — Xie & Leijen, *Generalized Evidence Passing for
   Effect Handlers* (ICFP 2021; Koka): handlers ride down as an evidence
   vector parameter; performs become local lookups; non-tail resumptions
   *bubble* up through a monadic translation (every effectful call's
   result is checked Pure-vs-Yield, kept cheap by bind-inlining and
   join-point sharing). Targets any platform (C, Wasm, JVM) with no
   runtime machinery. Two results matter to us even though we don't
   adopt the monad: the **tail-resumptive optimization** (§2.6, Thm. 5 —
   a clause `op ↦ λx.λk. k e` with `k ∉ fv(e)` runs *in place* as a
   direct call; ~10× on their counter benchmarks, and they argue most
   operations in practice have this shape), and the warning that the
   optimization's interaction with non-scoped resumptions is what forces
   the "generalized" machinery (§2.12).
3. **Capability-passing / iterated CPS for *lexical* handlers** —
   Schuster, Brachthäuser & Ostermann, *Compiling Effect Handlers in
   Capability-Passing Style* (ICFP 2020) and Schuster, Brachthäuser,
   Müller & Ostermann, *A Typed Continuation-Passing Translation for
   Lexical Effect Handlers* (PLDI 2022; the Effekt lineage, with Lexa —
   Zhou et al., OOPSLA 2024 — as a recent member). The PLDI 2022 result:
   typed lexical handlers "do not need the full power of multi-prompt
   delimited control" and translate to **pure System F with no runtime
   labels and no handler search** — each handler-delimited stack segment
   becomes its own continuation argument (functions take *several*
   continuations), capabilities become ordinary CPS functions. ICFP 2020
   adds: when capabilities are second-class (never stored or returned —
   Talk's situation), handler clauses inline at perform sites and the
   handler abstraction is *gone* in generated code.
4. **Runtime stacks** — Hieb, Dybvig & Bruggeman, *Representing Control
   in the Presence of First-Class Continuations* (PLDI 1990; segmented
   stacks, constant-time capture) with the one-shot refinement of
   Bruggeman, Waddell & Dybvig (PLDI 1996; one-shot resume = reinstate
   the segment and mark it shot — no copying); Sivaramakrishnan, Dolan,
   White, Kelly, Jaffer & Madhavapeddy, *Retrofitting Effect Handlers
   onto OCaml* (PLDI 2021; OCaml 5): heap-allocated fibers per handler,
   perform = stack-pointer switch, continuations one-shot (second resume
   raises — `Effect.Continuation_already_resumed` in shipped OCaml 5),
   exceptions kept as the separate cheaper unwinding mechanism, mean 1%
   overhead on handler-free code. WasmFX (Phipps-Costin et al., OOPSLA
   2023) standardizes the same shape — three instructions (`cont.new`,
   `suspend`, `resume`), one-shot enforced by trapping.

One claim was adversarially **refuted** during research and must not
shape the plan: one-shot continuations canNOT be "promoted" to
multi-shot by a cheap segment walk — multi-shot genuinely requires
fiber/segment *copying* machinery (PLDI 1996 eliminates copying *only*
for one-shot). Plan multi-shot as real work or skip it. (In a
closure-based CPS design resumptions are immutable closures, so calling
twice is structurally possible — the hazard moves to linear resources
and cells, which is why OCaml and WasmFX still enforce one-shot
dynamically.)

#### Why capability passing won

Two facts made family 3 the fit, and both are unusual: **performs are
already lexically routed** at name resolution (exactly the premise of
the PLDI 2022 translation — no evidence vectors, no handler stacks, no
runtime search, no markers), and **the IR is already CPS with the M6
closure runtime built** (flat closures, `MakeClosure`/`EnvGet`/
`CallIndirect`). The usual objection to CPS-family designs — pervasive
transformation cost on effect-free code, the reason OCaml 5 chose
runtime fibers — doesn't apply: λ_G is the transformation, effect-free
code keeps its shape entirely, and the evidence-passing monad's
per-call Pure/Yield checks are skipped because our continuations are
real. Costs as built: one closure per `@handle`, one per statement-spine
call to an abort-capable function, two extra parameters on
abort-capable functions; aborts cost a Ret chain linear in call depth
(bounded by `MAX_FRAMES`; fine without TCO).

**Milestone ladder from here** (each step is additive):
- **M9 (one-shot resumable)**: **done** — exactly as predicted (the
  same split applied at the perform; no VM changes; see "M9 — done").
  One-shot landed *by construction* rather than by dynamic enforcement:
  `continue` is a tail transfer, so a second resume is unwritable.
- **Tail-resumptive fast path** (the big win): when a handler
  clause immediately resumes (`k ∉ fv(e)` — Xie & Leijen Thm. 5; the
  λλCap inlining of ICFP 2020), β-inline the capability at the perform
  site — `subst.rs` is the β engine and monomorphization already
  specializes per handler. This is where "zero-cost" lives; it is an
  optimization, not a correctness requirement, so it waits.

**Documented fallback** (if M9 hits an unforeseen wall): OCaml-style
machine support — a handler stack in the `Machine` plus an `Abort`
instruction that pops frames to the scope and jumps to a handler
*block* of the scope's chunk (FSCD 2017 §4.5's
exceptions-as-unwinding; stock OCaml's linked handler frames). It is
less code than it sounds but splits the semantics across two engines,
which is why it lost for M7.

### M8 — done (the full io dialect)

All twelve `IORequest` operations route end to end (`lower_perform`'s
name→Op table → one parametric `Insn::Io` → the `IO` trait), and the
server examples serve real sockets: `talk run examples/WebApi.tlk` then
`curl localhost:3000/health` answers "ok"; ChatServer echoes over nc.

**As built:**
- **The `IO` trait** (src/vm/io.rs) carries the whole POSIX surface
  (read/write/open/close/ctl/poll/socket/bind/listen/connect/accept/
  sleep), ported from the previous backend: `StdioIO` is libc-backed
  (unix-only dependency; non-unix targets get -EPERM stubs, which is
  what the wasm build sees), `CaptureIO` simulates descriptors as byte
  buffers — writes append, reads advance a cursor, so a test that
  writes to a connection reads the same bytes back. That loopback is
  how the scripted server tests work (vm_tests' socket/accept scripts).
- **Both engines run the same IO.** The reference evaluator now owns a
  `CaptureIO` and marshals through it (its bespoke stdout capture and
  sleep no-op are gone), so two-engine io agreement is by construction.
- **One parametric instruction**: `Insn::Io { op: IoOp, a, b, c }`
  replaced the dedicated IoWrite/IoSleep insns. Pointer operands
  marshal against byte memory at execution: read fills it, open scans
  a NUL-terminated path, poll round-trips 8-byte (fd:i32, events:i16,
  revents:i16) records.
- **`_alloc(n)` with an unconstrained element is a byte buffer** (the
  raw buffers in ChatServer/ChatClient): map_ty defaults residual
  variables to Void, which cannot live in memory, so the alloc splice
  sizes a residual-variable element as bytes — the previous backend's
  alloc semantics for exactly these uses.
- **Calls through function-typed record fields** dispatch indirectly
  (`is_field_value_callee` — HTTP.Server's `route_handler0.invoke()`),
  completing M6's value-callee set.
- **Diagnostic fallbacks are typed now** (`dead_end`): an abandoned
  lowering path used to deliver `void` to whatever continuation was at
  hand, which trips the λ_G constructor's T-App panic the moment the
  continuation expects anything else (this was why the server examples
  crashed the compiler instead of reporting "socket not yet routed").
  A dead end is a call to a bodyless function — Trap on the VM,
  UnsetBody on the evaluator, well-typed everywhere.

**Deferred, honestly:** computed `'io(request)` values (every perform
routes statically by variant name; a computed request is diagnosed —
dynamic dispatch wants a story for matching on the request at the
boundary); `open_path`/File.tlk (the `io_open` *splice* passes a Talk
String whose bytes are not NUL-terminated — supporting it needs a
path-marshaling decision: copy-with-NUL at the splice, or a
length-carrying open; nothing demands it today); wasm
`run_program`/`show_ir` bindings (the workspace member exists,
untouched this milestone); computed globals (still literal-only — no
example needs one). CaptureIO's `accept` always succeeds, so server
loops never terminate under tests — the four server examples are
compile-verified in tests and exercised for real by hand.

### M9 — done (resumable handlers)

`continue v` inside a handler block resumes the perform with v; a
handler that completes without continuing keeps M7's abort semantics
(its value becomes the scope's value). Zero VM and zero evaluator
changes, again — the milestone is one new closure shape plus the
frontend's typing of `continue`.

**As built:**
- **Surface form**: `continue <expr>` is the resume (the previous
  backend's convention; the AST already carried the payload). The
  checker types the payload against the effect's declared return type
  (`handler_ret_stack`, pushed around handler-block checking, cleared
  inside nested function literals — they cannot resume) and rejects
  continue-with-value outside a handler.
- **The resumption is the same split, applied at the perform.** A
  resuming handler's capability domain grows a resumption parameter:
  `handler : Fn([payloads…, resume_k, slot], ⊥)` with
  `resume_k : Fn([effect return, slot], ⊥)`. A statement-spine perform
  reifies the rest of its block as that closure (`rest_closure`, shared
  with abort-capable calls) and passes it with its own return slot.
  `continue v` tail-transfers: `App(resume_k, [v, own slot])` — the
  performer continues as if the perform returned v, and the eventual
  value rides the same Ret chain home. Functions performing resumable
  effects already had the abort-capable shape (the capability tables
  don't care about Never), so callers were already split.
- **One-shot by construction**: `continue` is a divergent tail
  transfer, so a handler run can execute at most one resume, and the
  resumption is never first-class — stronger than the dynamic one-shot
  enforcement OCaml 5 and WasmFX use (trapping on second resume).
  Multi-shot remains real future work (the adversarially-refuted claim
  below: it genuinely requires copying machinery, and the cells story
  must be designed first).
- **Deep handlers** (Plotkin & Pretnar semantics): the capability stays
  installed for the whole scope; every perform reifies a fresh
  resumption and runs the handler again (pinned by the
  repeated-performs test).

**M9 limits, all diagnosed**: resumable performs live on the statement
spine (statement / let / final-expression positions; expression
positions are rejected, mirroring abort-capable calls), and the M7
limit list still applies. One frontend quirk found while testing: a
function sharing its name with an effect (`func ask` vs `'ask`)
confuses resolution into "calling an undeclared effect" — the tick
namespace isn't fully separate yet.

**Type-system M8 (GADTs)** is queued independently; hooks are in place.

---

## 8. Known warts (deliberate, documented)

- `Float.show` prints `1.229999999999999` for `1.23` — core's epsilon-loop
  algorithm, both engines agree, expected output frozen. Real fix: Ryū-style dtoa in
  core, post-backend.
- No TCO (tail calls = Call+Ret; `MAX_FRAMES` ≈ 1M bounds recursion).
- Fib's expected-output test is VM-only — fib(24) exceeds the reference evaluator's
  budget; the recursion scheme is covered on both engines at lower depth.
- Only *literal* globals inline; computed globals await the M8 static-init
  story.
- Registers are never reused within a chunk; instructions unpacked.

---

## 9. Key references by subsystem

Full table in `docs/backend-plan.md`. The ones cited
most in code: Leißa & Griebler (λ_G; `ssa-paper.md`); Thorin — Leißa,
Köster & Hack, CGO 2015 (CPS soup, call/return reconstruction); Maurer,
Downen, Ariola & Peyton Jones, PLDI 2017 (join points stay free); Kranz et
al., ORBIT 1986 (assignment conversion); Racordon et al., JOT 2022 (mutable
value semantics / inout); Leroy, POPL 1992 (unboxed scalars in raw bytes);
Maranget, ML 2008 (decision trees); Vytiniotis et al., JFP 2011
(OutsideIn(X)); Plotkin & Pretnar, LMCS 2013 (handlers); Shi, Casey, Ertl &
Gregg, VEE 2005 + Ierusalimschy et al., J.UCS 2005 (register bytecode);
Hieb, Dybvig & Bruggeman, PLDI 1990 (frame capture); Cardelli, LFP 1984
(flat closures); Reynolds 1972 (definitional interpreter as the trusted
reference implementation).

Effect compilation (M7 as built and the M9 plan — see §7):
Schuster, Brachthäuser, Müller & Ostermann, PLDI 2022 (lexical handlers →
pure System F, no runtime labels — the theoretical anchor); Schuster,
Brachthäuser & Ostermann, ICFP 2020 (capability passing; second-class
capabilities inline to zero cost); Hillerström, Lindley, Atkey &
Sivaramakrishnan, FSCD 2017 (CPS translation of handlers; §4.5 abort =
unwinding, no capture); Xie & Leijen, ICFP 2021 (generalized evidence
passing; tail-resumptive optimization, Thm. 5); Sivaramakrishnan, Dolan,
White, Kelly, Jaffer & Madhavapeddy, PLDI 2021 (OCaml 5 fibers; one-shot;
exceptions separate; the pay-only-when-used yardstick); Bruggeman,
Waddell & Dybvig, PLDI 1996 (one-shot continuations — no copying);
Phipps-Costin et al., OOPSLA 2023 (WasmFX — minimal suspend/resume
instruction set, one-shot by trapping); Zhou et al., OOPSLA 2024 (Lexa —
recent lexical-handler compilation).
