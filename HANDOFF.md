# Talk Compiler — Handoff Guide

*Last updated: June 11, 2026. Branch: `no-types-no-lowerer` (the old ~41k-line
type system and backend were deleted in 6a602348 "let's get a fresh start";
everything described here was rebuilt after that commit. All backend work is
uncommitted in the working tree.)*

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
| B-M4 enums + Maranget decision trees + Optional | **Next** (§7) |
| B-M5..M9, type-system GADTs | Planned (§7) |

**Examples running today** (both engines, expected stdout frozen):
HelloWorld, Strings, Struct, Identity, Loop, Imports(+Exports), Fib. Test
counts: 423 lib tests + 7 example tests, 0 failures (5 pre-existing
ignores).

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
  cells. Do the same for enums.
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
- **Match** (M3 scope): literal/wildcard/bind arms as a comparison chain —
  the degenerate single-column case of Maranget; M4 replaces this with the
  real decision-tree compiler (delete the chain code — negative diff).
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
  `Branch`. Value trees emit per block with **pure-only value numbering**
  (`memo`): cell/memory/IO ops re-emit per occurrence, matching the
  reference evaluator's re-evaluation of shared occurrences. **Flagged deviation**:
  block ownership is Func-reference *reachability* from each chunk, not
  the paper's §4 FV nesting tree — closed continuations (constant-bodied
  thunks) have empty FV and would float to the forest root. A continuation
  referenced by two chunks is a hard error.
- `mod.rs` — `Insn` (unpacked fixed-shape enum, resolved jump targets,
  pooled consts/args/traps), `Chunk`, `Module` (carries the statics image).
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
   construct gets one of these first.** Ordering rule: run the VM before
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
| **M4 (next)** | enums (variant/get_tag/switch), Maranget trees, record patterns, Optional | MatchBind, StructuralTyping |
| M5 | generic structs, Array (+`_alloc` fix), conditional conformance, Iterable/for, slot arena | Array, Sum, Iteratin, ForLoop, Protocols |
| M6 | closure conversion + trailing blocks; derived Showable | AnonFunc, Capture, TrailingBlock, Show |
| M7 | abort effects (handler refs + scope-end continuations) | Effects |
| M8 | full IO; scripted server tests; wasm run_program/show_ir; computed globals | FileIO, Sleep, Chat*, Http, WebApi, Website |
| M9 | resumable handlers / yield / 'async | future async stdlib |

### M4 in detail (start here)

1. **Failing tests first** (`run_on_both_engines_io`): enum construction +
   `match` dispatch, payload binds, nested variant patterns, or-patterns,
   wildcard default, Optional some/none, then expected-output tests for `MatchBind.tlk`
   and `StructuralTyping.tlk`.
2. **Runtime variants** mirroring records exactly: pure
   `VariantNew(Symbol, tag)` / `GetTag` / `GetPayload(i)` (already in
   `Op`); `EvalValue::Variant(symbol, tag, fields)` reifying as
   `VariantNew` of reified payloads; VM `Value::Variant(symbol, tag,
   Rc<Vec<Value>>)`.
3. **Construction lowering**: `.some(x)` / `Option.some(x)` resolve via
   catalog `EnumInfo.variants` (tag = declaration index, θ from the call
   node for generic enums like Optional).
4. **Maranget compiler** (`src/lower/patterns.rs`; ML 2008): pattern
   matrix over the scrutinee vector; first-column heuristic; specialize on
   variant columns → `switch` over `GetTag` (one continuation per tag,
   payloads extracted into bind envs), literal columns → comparison
   chains; or-patterns by row expansion; default row → next; empty matrix →
   trap (checker exhaustiveness is the real guard). Delete the M3
   single-column chain.
5. **Scheduler/VM switch**: evaluator already runs `Op::Switch`; scheduler
   emits a jump-table `Insn::Switch` (or Branch chain for ≤3 arms); VM
   dispatch accordingly.
6. **Record/tuple patterns** in `let` and arms via GetField/Extract binds.
7. Consider folding in the **post-lowering verifier run** (T-Prog + WF on
   the whole program in tests) — cheap insurance the plan calls for.

### M5 sketch

θ-specialized struct layouts; `_alloc` made generic (fix the latent
byte-sizing bug — Array calls `_alloc<Element>(capacity)` but `_alloc`
allocates bytes); `Load{width}`/`Store{width}` (Byte=1, I64/F64/Ptr=8);
**slot arena for aggregates stored in raw memory** (records in Arrays =
8-byte handles; flagged seam — test Array-of-struct round-trips on both
engines first); conditional conformance = discharge `Conformance.
context` at witness-demand; `for` desugars onto Iterable;
`ArrayIterator.next()` exercises the existing inout machinery.

### M6 sketch

Closure-convert only functions with *unknown* occurrences (flat closures,
Cardelli; environments read off FV sets; mutable captures already cells);
η-expansion for mixed known/unknown (paper §3.5); VM closure values
(chunk id + env) + `CallIndirect` — retires the "computed call target"
trap; trailing blocks = final closure args; derived `show` synthesized
from catalog fields.

### M7/M8/M9 sketch

M7: perform = direct call to the statically-routed handler label, then the
handling scope's end continuation (sound in CPS; Effects.tlk's frozen
expected output pins the semantics). M8: rest of the `io_*` dialect through the IO trait;
`io_perform` total dispatch over `IORequest` (needs M4 enums); CaptureIO fd
loopback for scripted Chat/Http server tests; wasm `run_program`/`show_ir`.
M9: pass the perform's continuation (already first-class) to the handler;
one-shot per Bruggeman et al.; frame-stack copy for capture.

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
Hieb, Dybvig & Bruggeman, PLDI 1990 (frame capture); Reynolds 1972
(definitional interpreter as the trusted reference implementation).
