# Lean backend rebuild: wave reports

Per-wave accounting required by
[the rebuild plan](lean-backend-rebuild-plan.md#wave-report). Sizes come from
`scripts/size_report.sh` (non-blank, non-comment Rust lines).

## Reset checkpoint (2026-07-16)

- Working tree restored to the `a1d20d27` frontend-only base for all backend
  and TypedProgram-contract code; parity assets, docs, and the LIT-01
  signed-integer-literal validation kept (re-applied to the reverted typing
  files with new boundary tests in `types_tests.rs`).
- Deleted: `src/mir`, `src/talk_ir`, `src/bytecode`,
  `compiling/contracts.rs`, `typed_program/contract.rs` + `serde_test.rs`,
  `lsp/borrow_provenance.rs`, `talk-runtime/src/scalar.rs`.
- ADR 0034 records the architecture and the 13,400-line full-parity budget
  (50% of the archived baseline's 26,798).
- Note: the plan's tag/branch steps (`git tag`, branch from `a1d20d27`) are
  git write operations left to the repository owner; everything is
  recoverable from committed `65c93acf`.

## Wave 2: Copy aggregates and patterns (2026-07-16)

- **Restored**: tuple construction/projection/destructuring (including
  borrowed tuple parameters and nested positional access), enum construction
  with declaration-order tags, payload extraction, match compilation to
  branch chains (literal, bool, bind, wildcard, tuple, variant, or-patterns),
  Talk-style tuple and enum result rendering via catalog-derived display
  names.
- **Reference**: archived aggregate `Value` representation reused per the
  runtime audit (Tuple/Variant/Record over `Rc<Vec<Value>>`).
- **Tests**: 5 black-box `talk run` tests. All layout stays inside the
  bytecode adapter (`runtime_symbol` is the only identity bridge).
- **Unsupported adjacent (fail closed)**: record literals, struct patterns,
  bindings inside or-patterns, linear enums.

## Wave 3 + managed strings (2026-07-16)

- **Restored**: structs (explicit and memberwise initializers, stored-field
  projection and assignment), affine ownership with structural drops
  (ADR 0017/0030 model: scope exits, statement-boundary temporaries,
  replacement destroys old values exactly once, `break`/`continue`/`return`
  path cleanup, path-sensitive drops when a value moves on only some arms),
  use-after-move rejection, `clone()` for Copy and CheapClone (structural
  buffer retain), managed byte buffers through the core `@_ir` memory
  intrinsics (alloc/free/retain/is_unique/load/store/copy/take/gep), string
  literals as immortal statics, string concatenation, `print` through
  `io_write`, ambient core effects ('alloc/'io/'async) executing directly
  against runtime intrinsics, literal core globals (STDOUT_FD) inlined.
- **Corpus at parity** (byte-exact stdout, zero-leak counted execution):
  `tuple_access`, `conditional_moves`, `clone_method`.
- **Semantic rule owners**: drop placement — `FunctionBuilder` scope/temp
  machinery; buffer classification — `contains_buffer`/`needs_drop`;
  RawPtr-field-is-a-buffer rule mirrored from the archived teardown
  (`96249e71` statements.rs); result-footprint leak accounting —
  `backend::execute`.
- **Unsupported adjacent (fail closed)**: enums with owned payloads, `Deinit`
  hooks, 'heap structs, linear types, mutable borrows, effect handlers,
  closures/indirect calls, non-literal globals.

## Wave 4: managed values and core collections (2026-07-16)

- **Restored**: string-literal patterns as byte-equality chains over static
  data (with escapes and unicode escapes), `Substring` view patterns, `for`
  iteration through the elaborated Loop+Match (variant patterns resolve by
  name for synthesized nodes), `mut func` receivers via a private
  tuple-return writeback convention (`(result, final self)`), the full
  grapheme segmentation stack (core Unicode source compiling as-is),
  associated-type projections normalized through a merged canonical catalog,
  conformance-row substitutions for generic implementations
  (instance-head matching), generic struct initializers, array literals
  (alloc + stores + core Array layout), `Deinit` hook dispatch before
  structural teardown (with `self`-drop suppression inside the hook), enums
  with owned payloads (tag-dispatched drops), and `'heap` structs: object
  regions, merge-on-store, claim-per-binding accounting
  (acquire on bound-handle copies, release on scope exit, containment
  replaces stored claims), cyclic teardown balanced.
- **Corpus at parity now** (byte-exact, zero-leak): `tuple_access`,
  `conditional_moves`, `clone_method`, `string_building`, `string_patterns`,
  `graphemes`, `iterate_and_match`, `heap_graph` — 8 of 16. The remaining 8
  are the effects corpus (wave 6).
- **Size**: backend 3,721 production lines; total ≤8,998 of the 13,400
  budget.
- **Unsupported adjacent (fail closed)**: user effects and handlers,
  closures/indirect calls, explicit initializers on 'heap structs,
  bindings inside or-patterns, mutable borrows/`mut` args beyond receivers.

## Waves 5 + 6: closures and deep one-shot effects (2026-07-16)

- **Restored (wave 5)**: anonymous and named function values (captureless
  and capturing — free locals capture by value into runtime closure
  environments), indirect calls through function-typed locals and
  parameters.
- **Restored (wave 6)**: `@handle` installs deep handlers with dynamic
  nearest-handler routing (ADR 0032): the runtime gained a frame-tied
  handler stack (`PushHandler`/`FindHandler`/`GetFloor`/`SetFloor`, tags
  51–54; entries invalidate with their installing frame, no pop hooks) —
  the clause runs outside its own handler via a search floor (CHG-01).
  Handler clauses compile as closures over `[delimiter continuation,
  captures…]`; `continue v` is one-shot Resume (resume-as-return,
  Bruggeman–Waddell–Dybvig 1996); a clause's finite value is structural
  Discontinue (CHG-03) delivered by `CallCont` through the existing ADR
  0027 unwind walk. Every suspendable call gets an unwind cleanup block
  (scope-exit drops + `UnwindRet`) so aborted frames release everything.
  Generic effect payloads pass opaquely through registers (one clause per
  effect handles every instantiation).
- **Corpus**: **all 16 programs at byte-exact parity** — `handlers` against
  the reviewed TOOL-06 rendering (`0`, not the baseline CLI's `I64(0)`);
  the other 15 against frozen baseline stdout. Zero-leak counted execution
  everywhere, including cross-frame aborts.
- **Fixed along the way**: value-carrying tail `if` statements; per-arm
  statement-temp isolation at joins; join-time move accounting (an arm
  whose value IS a binding moves it); path-divergent moves now drop on the
  paths that still own the value instead of rejecting.
- **Size**: backend 4,128 production lines + runtime 5,270 (handler stack
  +129) + seams ≤283; total ≤9,681 of the 13,400 budget.
- **Unsupported adjacent (fail closed)**: existentials and dynamic witness
  dispatch (D1 — no corpus program needs them), cells/mutable captures,
  multi-shot resumption (one-shot by construction), effectful cleanup.

## Wave 7: modules, packages, IO, and tools (2026-07-16)

- **Restored**: multi-file scripts (every file's top-level statements as
  one unit) with real program globals — 8-byte static slots, initialized
  in statement order, guarded teardown at exit, read-before-init traps
  (LINK-02) — so handler clauses and closures share them without
  captures; trailing-block closures; indirect calls through any
  function-typed value (fields included); `mut`-receiver writebacks to
  globals; the implicit clone rule for consuming a place read that cannot
  move (owned by MIR now that the old flow checker is gone); `store`
  intrinsics donating their value; REPL evaluation with captured IO
  (TOOL-09, three new pinned behavior tests); the full `.test.tlk`
  harness ported from the archive over the new seam — human and JSON
  output, filters (TOOL-07); `talk build` / `run-image` / `bytecode`
  (TOOL-12/13/14; images validate before execution); package binary
  execution over the locked dependency graph with per-package module
  compilation and whole-graph body supply (TOOL-08 run); talk-c program
  and package execution (TOOL-16), wasm via the shared program path
  (TOOL-18), talk-static already consuming validated images (TOOL-15).
- **Module identity**: stdlib bodies supplied per-module; re-export
  aliases unify by stable module id (a compile-scoped alias map).
- **Open**: package-aware `talk test` inside a package graph; TOOL-10/11
  inspection surfaces; IO-02 socket/poll/sleep paths.

## Wave 8: parity closure (2026-07-16)

- All 16 corpus programs replay at byte parity in `tests/talk_tests.rs`
  (15 frozen baselines + reviewed `handlers`); 907 workspace tests pass;
  clippy clean except one pre-existing typed-tree size lint.
- Ledger updated with the rebuild status; the obsolete implementation
  status document of the deleted rewrite was removed; debug
  instrumentation stripped.
- **Final size**: backend 4,466 production lines + reused runtime 5,270
  (+129 handler stack) + seams ≤900 ⇒ ≤10,636 of the 13,400 budget —
  ~60% smaller than the 26,798-line archived implementation, with one
  public seam (`Driver::compile_executable` / `execute_module` /
  `execute_image`).

## Soundness closure, group A (2026-07-16)

Three correctness gaps recorded at parity, now closed (one failing
black-box test each in `tests/talk_tests.rs`):

- **Owned captures rejected (CHG-06).** Function values and trailing
  blocks that capture a buffer- or region-owning local fail closed
  ("capturing owned values in function values is not supported yet");
  the environment copy could outlive its owner. Handler clauses keep
  their handler-extent shared-borrow captures.
- **Guarded teardown survives Discontinue.** The script entry split into
  an outer frame (global teardown, result delivery) and an inner frame
  (statements and handler installs, the abort delimiter), so a clause's
  finite value no longer skips global teardown. Known corner: a global
  returned as the program's value is skipped by teardown, so an abort
  path leaves that one slot to the result-footprint accounting.
- **Owned payloads through generic effects rejected.** One clause body
  serves every instantiation over rigid payload types and cannot drop an
  owned payload; perform sites whose generic-position argument owns
  buffers or handles fail closed.

Size after group A: backend 4,546 production lines; total ≤10,716 of the
13,400 budget. 910 workspace tests.

## Adversarial hardening, group G (2026-07-16)

Three writeback bugs in a row shared one shape: the convention crossing
a dynamic boundary at feature intersections the feature-by-feature tests
never crossed. This round makes those intersections systematically
hostile instead of waiting for the next probe:

- **Found and fixed by probing first**: `mut` arguments on performs were
  silently ignored — the clause mutated its copy and the performer's
  binding never changed. Clauses now register exclusive-borrow declared
  parameters as writebacks and performs land evolved values through the
  shared machinery, so effects follow the same convention as every other
  call shape.
- **Writeback matrix test**: one table-driven black-box test crosses
  call shapes (direct, method, closure, global function value,
  rigid dictionary, existential, perform) with mutation shapes (mut
  receiver, one/two mut params, both, projected places) and owned-value
  transfer; every cell makes two calls and observes the evolved state,
  and the runtime's allocation balance checks the ownership half of
  each cell.
- **Convention validator**: instances record their writeback width at
  compile time; named call sites and requirement-closure selections
  record the width they expect; after the worklist drains, any
  disagreement is a compile error. The receiver-mutation bug class
  (declared shape vs implementation shape skew) is now unrepresentable
  silently — it either agrees or fails the build.

Size after group G: backend 6,432 production lines; total ≤12,927 of
the 13,400 budget. 932 workspace tests plus 4 Swift tests.

## Full gap closure, group F (2026-07-16)

Every reachable backend rejection either executes or carries a
soundness argument. Closed this round, each from a probe program that
typing accepts:

- **Witness edges**: closures (function values and trailing blocks)
  inherit their frame's witnesses and dictionaries through their
  environments; glue for compound rigid types (`Array<T>` re-performed
  under a fresh generic) captures inner witnesses in its closure
  environment.
- **Constrained effect generics (conformance dictionaries)**: `effect
  'show<T: Showable>` passes the constraint's requirement closures
  after `[drop, retain]` — full dictionary passing (Wadler & Blott,
  POPL 1989). One clause body calls requirements on every
  instantiation, packs its rigid value into `any P` from the same
  dictionary, and instances thread dictionaries like witnesses.
  `mut func` requirements execute through both dynamic paths: the
  requirement's declared scheme (an exclusive-borrow receiver) marks it,
  so every implementation returns `(result, final self)` — rigid
  dispatch writes the evolved receiver back through its place chain,
  and existential dispatch rebuilds the value around the evolved
  payload with its own witness table. Constructions coerce directly
  into existentials (the construction builds the pack's payload type,
  not the coercion target). `mut` parameters land through the same
  shared machinery on every path — direct, indirect, rigid dictionary,
  and existential dispatch all collect targets with
  `writeback_targets` and land them with `apply_writebacks`, and owned
  arguments transfer to dynamic callees the same way direct calls do.
- **Enum retains**: CheapClone of payload-carrying enums dispatches on
  the tag, one arm per buffer-carrying variant (`drop_enum_value`'s
  mirror).
- **Place chains**: assignment through nested projections
  (`o.inner.v = 5`) and `mut` arguments naming projected places
  (`bump(mut b.n)`) resolve to a base binding plus a projection spine;
  copy-on-write records write back up the value links, stopping at
  `'heap` links (objects mutate in place).
- **Record rows**: closed rows lay out as label-sorted tuples — field
  reads, field assignment (tuple rebuild), structural drop/retain/copy
  glue, and witness walks. Open rows and row-spread stay with the
  checker (spread currently fails inference).
- **Named-entry globals**: `--entry` programs get the script's LINK-02
  slot discipline — ordered initialization (non-literal initializers
  included), mutation from any function, destructured components in
  their own slots, guarded teardown.
- **Function values in globals** call indirectly through their slot.

Confirmed out of backend scope by probing (each fails in parsing or
typing before reaching the backend): struct patterns, record spread
inference, `let` without an initializer (typing accepts
use-before-assignment, so executing it would read garbage — the
rejection is load-bearing until the checker gains definite-assignment
analysis), effect-generic annotations inside clause bodies, and
cross-function reads of destructured top-level components under a
named entry (typing leaves unsolved variables).

Size after group F: backend 6,247 production lines; total ≤12,742 of
the 13,400 budget. 931 workspace tests plus 4 Swift tests.

## Witness passing for generic effects, group E (2026-07-16)

Nested generic payload positions (`(Int, T)`, `Array<T>`, enum payloads)
now execute, replacing group D's per-value packaging with the design the
modern-compiler survey converged on — value-witness-table passing
(Swift's unspecialized-generics ABI; Go's generics dictionaries,
Griesemer et al., OOPSLA 2022; dictionary passing, Wadler & Blott,
POPL 1989):

- **Convention**: payloads travel in native layout; the perform site
  appends one `[drop, retain]` glue-closure pair per effect generic
  (from the checker's recorded instantiation, else solved structurally
  from argument types). The clause binds them as hidden trailing
  parameters; `drop`/`retain` of a rigid-param-typed value dispatches
  through them. Because values stay native, the existing structural
  glue handles every aggregate shape with zero per-constructor code —
  the reason this design beat deep packaging (Leroy-style coercions).
- **Threading**: an instance whose substitution mentions a rigid
  generic takes the witnesses as hidden parameters, appended by every
  caller in an order recorded at demand time (Go's sub-dictionary
  rule). This carries witnesses through generic calls inside clause
  bodies and through Array's deinit instantiated at a rigid element.
  Pinned: drop-on-floor, continue-back, discontinue cleanup, Copy
  instantiations, nested tuple/Array/enum payloads, clause-to-generic
  handoff, and re-perform forwarding.
- **Deleted**: the packaging build/unwrap at perform sites and the
  nested-position skip in structural glue (with its bug class — the
  package-or-raw ambiguity fixed in 3ea4f4dd no longer exists).
- **Bug found by the failing tests, fixed**: binding or storing a
  global's value into an owning destination (a tuple element, a `let`,
  a field) transferred nothing and retained nothing — the destination
  and the global slot both claimed the buffers, a double free
  reachable without effects (`let t = (1, s)` at script scope). All
  binding/store sinks now transfer through `consume_binding`, which
  donates a reference for unmovable place reads and takes no ownership
  for borrow-typed destinations.
- **Fail-closed edges**: a closure defined inside a clause cannot carry
  the frame's witnesses (unnamed locals do not capture); existentials
  over rigid payloads; re-performing a compound rigid payload
  (`Array<T>` re-sent under a fresh generic) — each rejects explicitly.

Size after group E: backend 5,512 production lines; total ≤12,007 of
the 13,400 budget. 925 workspace tests plus 4 Swift tests.

## Parity gap closure, group D (2026-07-16)

Re-audit of every remaining rejection against the ledger's Required
rows. Two were genuine gaps; both now execute:

- **EFF-03 owned generic payloads**: a perform argument in a
  directly-generic effect position travels as an existential-shaped
  `[drop, retain]` package (the DYN-01 value convention without protocol
  requirements), so one clause body serves every instantiation: an
  unconsumed payload releases through slot 0 at clause exit, `continue
  payload` hands the package back for the perform site to unwrap, and a
  discontinue's abort cleanup drops it like any owned local. Copy
  instantiations use the same convention (one clause, one calling
  convention). Clause binders take their ownership types from the
  effect's declared signature (they are usually unannotated — this also
  closed a payload leak for unannotated owned clause binders). Nested
  generic positions (`Array<T>`) would need deep packaging and stay
  rejected.
- **CLO-02 `mut` parameters on function values**: indirect calls now
  compile through the same path as every other function-value call, and
  both sides derive the `(result, final mut values…)` writeback from the
  function type alone.
- **Linear globals** get a precise rejection ("consume linear values
  within function scopes") instead of a teardown-artifact diagnostic:
  exactly-once consumption cannot be proven across every reader plus
  guarded teardown, so the rejection is principled, not provisional
  (OWN-03's finite-exit checking is a per-frame judgment).
- **Confirmed spec-required rejections** (ledger rows demand them):
  CHG-06 owned/mutable handler captures ("only Copy and handler-extent
  shared borrows in v1"), and with it assignment to captured values;
  user handlers over ambient core effects (IO-02 makes the runtime their
  implicit handler).

Size after group D: backend 5,339 production lines; total ≤11,834 of the
13,400 budget. 925 workspace tests plus 4 Swift tests.

## Ergonomics and hardening, group C (2026-07-16)

Surface forms beyond the Required rows, each from a failing test:

- **Character literals**: a literal compiles to a borrowed grapheme view
  (`Character { storage, start, byte_count }`) over immortal static
  bytes, the same statics mechanism string literals use.
- **Or-pattern bindings**: alternatives bind the same names (agreed by
  the checker), so all alternatives share one local per name.
- **`mut` arguments**: the receiver writeback convention generalizes —
  a callee returns `(result, final mut values…)` for its `mut`
  (exclusive-borrow, ADR 0018) parameters in declaration order, and the
  caller stores each back into the argument's place (local or global
  slot). Both sides derive the order from parameter types, so direct
  calls through any callable agree; `mut` parameters on function values
  (indirect calls) fail closed.
- **Recursive nested functions**: nested `func` declarations index like
  top-level ones, so calls to them — including self-recursion — resolve
  to compiled bodies. Capturing nested functions keep their explicit
  CHG-06 rejection.
- **Fail-closed fixes for silent misbehavior**: assignment to a captured
  value used to write the closure's environment copy and drop the
  mutation on the floor — now a compile error; a user `@handle` over an
  ambient core effect ('io, 'alloc, 'async) used to be silently bypassed
  by the runtime's implicit handler — now a compile error.
- **CHG-01 pinned**: a perform inside a handler clause searches from
  below the clause's own delimiter (the search floor), reaching the next
  handler out — covered by a black-box routing test.
- **talk-c inspection + Swift smoke**: the frontend-only stubs for
  package tests, lowered render, bytecode render, and bytecode compile
  now execute through the backend; `talk-swift` gained a Package.swift
  so `swift test -Xlinker -L../target/release` runs on any host with a
  Swift toolchain, and its XCTest suite now asserts program execution,
  package run, and package test through the C ABI (4 tests pass).
- **Nothing owed for loops**: `continue` with a value outside a handler
  clause is rejected by the type checker, not the backend.

Size after group C: backend 5,246 production lines; total ≤11,741 of the
13,400 budget. 925 workspace tests plus 4 Swift tests.

## Required-row closure, group B (2026-07-16)

Every remaining Required ledger row, each from a failing black-box test:

- **TOOL-08 tests**: package-aware `talk test` compiles `.test.tlk`
  suites against the locked dependency graph (dependency bodies supplied
  through `DriverConfig::libraries`); `talk test` inside a package uses
  it automatically.
- **IO-02**: `'io(request)` performs lower to a tag dispatch over the
  core request enum, one host operation per variant in declaration order
  (which matches the runtime's operation table one-to-one); the
  round-trip test opens, writes, reads, closes, and sleeps. User
  handlers over ambient effects remain out of scope for v1.
- **DYN-01/02**: existential coercions pack the payload behind a witness
  table with fixed slots (0 drop, 1 retain — the archived convention —
  requirements from 2, selected from the payload's conformance exactly
  like a static call, defaults included); member calls on `any P`
  dispatch through the table; drops and retains of existential values
  dispatch through slots 0/1. Arrays of existentials and owned payloads
  covered.
- **OWN-03**: strict-linear values (`'linear`) must be consumed exactly
  once on every finite path — an implicit drop point (scope exit, join,
  abort cleanup) raises a compile error; destructuring a linear
  scrutinee counts as its consumption (CHG-07's whole-aggregate rule).
  Consuming linear globals stays conservatively rejected.
- **BOR-03 / CHG-04**: a borrowed (or `Borrowed`-view) return of one of
  the frame's own named owned bindings is rejected — the loan would
  escape its owner (previously it silently leaked). CHG-05's
  loan-across-suspension reject is deliberately not implemented: with
  one-shot resumption (stack intact on resume, frame dead on abort) and
  no mutable borrows in the v1 surface, the hazard it guards against
  cannot arise; revisit with multi-shot or `mut` loans.
- **TOOL-10**: `talk mir` renders the backend's middle representation;
  with `talk bytecode` these are the two inspection surfaces (TOOL-11's
  separate Talk IR has no successor artifact under ADR 0034).

Size after group B: backend 5,020 production lines; total ≤11,390 of the
13,400 budget. 916 workspace tests.

## Wave 1: scalar kernel (2026-07-16)

- **Observable behavior restored**: `talk run` (new subcommand) executes
  scalar scripts and zero-parameter entries through validated in-memory
  bytecode: Unit/Bool/Int/Float, locals, assignment, `if`/`loop`/`break`/
  `continue`, direct calls, recursion, and normal operator syntax including
  protocol-default bodies (`<=` via `Comparable.lte`). Talk-style result
  rendering, Unit suppression, clean traps with live-resource counts, and
  explicit fail-closed rejection of unsupported forms.
- **Archived reference used**: E1 scalar semantic contract
  (`docs/e1-scalar-execution-plan.md`) for arithmetic, comparison,
  conversion, trap, and rendering behavior; talk-runtime reuse per
  `docs/e1-talk-runtime-reuse-audit.md`.
- **Production lines added**: backend modules 1,461 code
  (src/backend/{mod,mir,lower}.rs); seam additions ≤135 (CLI `Run`,
  `Driver::compile_executable`/`execute_module`, core typed-program cache).
  Runtime reused unchanged (5,141). Total ≤6,963 of the 13,400 budget.
- **Test lines added**: 13 black-box tests in `tests/talk_tests.rs` (~150
  lines) through the public CLI; 3 LIT-01 typing tests.
- **Documentation**: ADR 0034; this report.
- **Modules added**: `src/backend` (private `mir`, `lower` behind
  `compile`/`execute`). Modules deleted in reset: 8.
- **Interfaces**: two public seam functions
  (`Driver::compile_executable`, `compiling::driver::execute_module`).
- **Semantic rules and owners**:
  - scalar value/arithmetic semantics — talk-runtime interpreter (reused);
  - scalar type gate and borrow-of-Copy erasure — `mir::scalar_ty`;
  - monomorphic instance identity — `mir::ProgramBuilder::demand`
    (substitution pruned to scheme parameters);
  - conformance-witness dereference (typing's selection) —
    `mir::ProgramBuilder::conformance_witness`;
  - cross-module symbol identity — `mir::canonical`.
- **Special cases removed**: none pre-existing (kernel wave).
- **Unsupported adjacent behavior** (all fail closed with "not supported
  yet"): strings/characters/aggregates, destructuring patterns, non-scalar
  values, effects and handlers, closures/indirect calls, `mut` arguments,
  trailing blocks, globals across modules, generic calls whose instantiation
  stays open.
- **Commands validated**: `cargo test --workspace` (874 tests, 0 failures),
  `cargo clippy --workspace`, `talk run` spot checks for `Int::MIN / -1`
  wrap, `Float` division by zero (IEEE `inf`), and `Int::MAX + 1` wrap.
