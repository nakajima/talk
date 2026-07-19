# Backend parity ledger

Status: living parity inventory (2026-07-16: lean rebuild parity pass)

## Lean rebuild status (2026-07-16)

The backend was rebuilt per
[the lean backend rebuild plan](lean-backend-rebuild-plan.md) and
[ADR 0034](adr/0034-lean-bytecode-backend-architecture.md). The per-phase
gate columns below (TypedProgram / CheckedMir / Talk IR / Bytecode, G0–G5)
describe the removed implementation and are superseded: phases are private
inside one `compile`/`execute` seam, and every row's evidence is a
black-box test through `talk run`, `talk test`, or the embeddings
(`tests/talk_tests.rs`, `src/testing.rs`, crate suites).

- **Complete-program corpus: all 16 rows at parity.** Byte-exact stdout
  against the frozen baseline (`handlers` against the reviewed TOOL-06
  rendering in `tests/parity/reviewed-programs`), empty stderr, exit 0,
  and counted execution balanced to the result footprint on every run.
- **Capability rows**: EXE-01..06, INTR-01, LIT-01, GEN-01, WIT-01/02,
  AGG-01..03, PAT-01, OWN-01..04, BOR-01/02, MEM-01..05, HEAP-01/02,
  CLO-01/02, DYN-01/02, EFF-01..04, CORE-01..03, IO-01/02 restored
  through the one backend as exercised by the corpus and tool tests:
  existentials pack/dispatch/tear down through fixed-slot witness tables;
  strict-linear values must be consumed exactly once on every path;
  host IO (`'io` requests: files, sockets, poll, sleep, environment)
  dispatches from perform sites to the runtime's implicit handler.
  BOR-03's rejected side lands as MIR diagnostics (escaping borrowed
  returns, use-after-move, linear accounting); UNSAFE-01's trusted
  inline-IR surface executes for compiled source. Character literals,
  or-pattern bindings, `mut` arguments (exclusive-borrow writeback,
  direct calls), recursive capture-free nested functions, and CHG-01
  clause-perform routing all execute with pinned tests; user handlers
  over ambient core effects and assignments to captured values fail
  closed (both silently misbehaved before). Owned payloads through
  generic effects execute in full — direct AND nested positions
  (EFF-03): payloads travel in native layout and the perform site
  appends one `[drop, retain]` witness pair per effect generic
  (value-witness-table passing: Swift's unspecialized-generics ABI;
  Go's generics dictionaries, Griesemer et al. OOPSLA 2022; dictionary
  passing, Wadler & Blott POPL 1989). Instances whose substitution
  mentions a rigid generic take the witnesses as hidden trailing
  parameters, so a clause can hand its value to generic functions,
  through Array/enum teardown glue, and to re-performs. `mut`
  parameters on function values follow the direct-call writeback
  convention (CLO-02). Two rejections formerly listed here as
  principled were falsified by the 2026-07-17 reference test audit
  and are open work under the reopened wave 5 of the rebuild plan:
  owned/mutable captures in function values and assignment to
  captured values (cells) are pinned reference behavior. The
  remaining rejections stand: user handlers over ambient core effects
  (the runtime is their implicit handler), linear globals
  (exactly-once consumption cannot be proven
  across every reader plus teardown), and uninitialized `let` bindings
  (typing accepts use-before-assignment, so the rejection is
  load-bearing until definite-assignment analysis lands in the
  checker). Constrained effect generics carry conformance dictionaries
  (requirement closures after `[drop, retain]`); closures inherit
  witnesses through their environments; record rows, nested place
  assignment, `mut` projections, enum retains, named-entry global
  slots, and global function values all execute with pinned tests.
- **Tools**: every Required tool row executes through the same
  compile/execute pair — `run` (script/entry/package), `test`
  (standalone and package-aware, filters, JSON events),
  `build`/`run-image`/`bytecode`/`mir` (TOOL-10; the separate Talk IR of
  TOOL-11 has no successor artifact under ADR 0034's private phases),
  REPL, talk-c program/package execution plus its test, lowered-render,
  bytecode-render, and bytecode-compile entry points, Swift via talk-c
  (`talk-swift` now carries a Package.swift and its XCTest suite runs
  run/test/inspection through the C ABI), wasm via the shared program
  path, talk-static over validated images.
- **Sizes** (`scripts/size_report.sh`): backend 5,020 production lines,
  runtime 5,270 (reused; +129 for the handler stack), seam additions
  ≤1,100 — total ≤11,390 against the 13,400 budget (archived baseline
  26,798).

Execution plan: [Backend feature-parity plan](backend-parity-plan.md)

Semantic authority: [ADR 0032](adr/0032-single-artifact-ownership-and-lowering-pipeline.md)

Implementation status: [Lean rebuild wave reports](lean-rebuild-wave-reports.md)

E1 design: [E1 scalar execution plan](e1-scalar-execution-plan.md)

E1 runtime audit: [E1 talk-runtime reuse audit](e1-talk-runtime-reuse-audit.md)

Historical baseline: `pre-backend-reset-2026-07-13` at `96249e71`

This ledger tracks restoration of source behavior and user-facing tools. It does
not define language semantics. ADR 0032 wins if this ledger disagrees with it.

## Classification vocabulary

| Classification | Meaning |
| --- | --- |
| Required | Baseline source or tool behavior that the new pipeline must restore |
| Changed | An accepted ADR deliberately defines different behavior |
| Reject | The baseline behavior was unsafe; parity requires a diagnostic or safe implementation |
| Internal | Test or behavior was tied only to deleted implementation machinery |
| Expansion | Capability was not provided by the baseline and does not gate feature parity |

## Implementation vocabulary

| State | Meaning |
| --- | --- |
| Integrated | Real producer and consumer support is on `bigdiff` and has passed the applicable gates |
| Partial | A narrower subcase is integrated |
| Contracted | The artifact can represent the row, but the real producer or consumer rejects it |
| Fixture-only | Validated test fixtures exercise the row; production input remains rejected |
| Rejected | Production fails closed before publishing the next artifact |
| Not connected | No implementation crosses this seam |
| Decision required | Semantics or ownership must be settled before implementation |
| N/A | The phase does not apply to this row |

## Gate vocabulary

- **G0** - contract, validator/verifier, printer, and ledger
- **G1** - real producer
- **G2** - validated consumer fixture and negative verifier
- **G3** - real producer-consumer handshake and cross-artifact law
- **G4** - rebased integrated-head validation
- **G5** - black-box execution through every backend claiming the row

`Pass` means the gate passed on `bigdiff`. `Pending` means the row cannot claim
support. `Not connected` is not a waiver of G5.

## Baseline inventory status

| Inventory | Baseline source | Current accounting |
| --- | --- | --- |
| Canonical frontend and LSP | Current workspace suites | Integrated at `03128941` |
| Complete program corpus | 16 files under `tests/programs` | All 16 pass `talk check`; byte-exact stdout, exit, stderr, and baseline balance observations are frozen under `tests/parity/programs` |
| Old flow suite | `src/flow/flow_tests.rs` at the baseline tag | All 151 tests have exact dispositions in `tests/parity/baseline-test-disposition.tsv` |
| Old lowering suite | `src/lower/lower_tests.rs` at the baseline tag | All 53 tests have exact dispositions in `tests/parity/baseline-test-disposition.tsv` |
| Old VM suite | `src/vm/vm_tests.rs` at the baseline tag | All 293 tests have exact dispositions in `tests/parity/baseline-test-disposition.tsv` |
| Old real-program runner | `tests/programs.rs` at the baseline tag | Each program has an individual row below |
| Old CLI | `src/bin/talk.rs` at the baseline tag | Command rows below |
| Runtime direct tests | `talk-runtime` | Still active, but not proof of compiler-to-runtime parity |
| Embeddings | `talk-c`, `talk-swift`, `wasm` | Frontend-only errors today; restoration rows below |
| External repositories | `talk-syntax`, `talispk` | Frontend smoke pass; executable parity not yet applicable |

### P0 inventory result

P0 is complete for the reset baseline:

- all 16 complete programs have frozen output, exit, stderr, and baseline
  resource observations;
- all 497 archived flow, lowering, and VM tests appear exactly once in
  `tests/parity/baseline-test-disposition.tsv`;
- 430 tests preserve required source, diagnostic, runtime-safety, or observable
  behavior;
- 67 tests are tied to deleted flow, lowering/lambda-G, or evaluator shapes and
  name the canonical ledger rows that replace their semantic purpose;
- every disposition references at least one existing capability row.

No archived test directly requires an ADR 0032 Changed row. The changed and
conservative-v1 rows below remain mandatory negative coverage when their slices
land. TOOL-06 deliberately replaces the baseline CLI implementation detail
`I64(0)` with Talk-syntax `0`; the frozen baseline remains unchanged and the
reviewed replacement is `tests/parity/reviewed-programs/handlers.stdout`.

## Current pipeline intersection

| ID | Capability | Class | TypedProgram | CheckedMir | Talk IR | Bytecode | Primary blocker |
| --- | --- | --- | --- | --- | --- | --- | --- |
| FND-01 | Canonical semantic frontend artifact | Required | Integrated | N/A | N/A | N/A | None |
| FND-02 | Stable callable identity and exact external supply plan | Required | Integrated | Integrated | Integrated | Not connected | Linker and backend |
| FND-03 | Copy evidence selected once and erased after MIR | Required | Integrated | Integrated for verified subset | Integrated erasure | Integrated consumer sees no evidence | None |
| EXE-01 | Scalar constants and returns | Required | Integrated | Integrated | Integrated | Integrated for Unit, Bool, Int, and Float | None for E1 |
| EXE-02 | Scalar local binding and Copy reads | Required | Integrated | Integrated | Integrated | Integrated as target-local registers | None for E1 |
| EXE-03 | Branch, switch, loop, goto, unreachable CFG | Required | Integrated | Integrated | Integrated | Integrated, including edge adapters and copy-cycle temporary | None for E1 |
| EXE-04 | Local and external direct calls | Required | Integrated | Integrated | Integrated | Local calls integrated; imports reject fail closed | E2 linker for external calls |
| INTR-01 | Canonical checked scalar intrinsic identity | Required | Integrated operation, operands, producer-selected Copy evidence, and exact exported scalar implementation recipes; deferred families use a payload-free unsupported marker | Integrated direct generation, imported-recipe materialization, and exact signature verification | Integrated identity, ordered operands, origin, evidence erasure, and exact signature verification | Integrated exhaustive operation-to-opcode mapping | None for E1 |
| EXE-05 | Int/Float arithmetic, comparison, and conversion through trusted intrinsics | Required | Integrated checked operation and operands | Integrated for direct trusted scalar intrinsic bodies | Integrated for verified scalar operations | Integrated source execution and clean traps | None for E1 |
| EXE-06 | Byte comparison and Byte-to-Int conversion | Required | Integrated checked operation identity; executable Byte creation still depends on memory | Integrated for source parameter operations | Integrated for verified parameterized operations | Fixture-only mapping and validated runtime profile | R1/K1 concrete Byte producer |
| LIT-01 | Signed 64-bit Int literal range | Required | Integrated `i64` value and `InvalidInt` recovery with boundary diagnostics | Integrated `i64` constant | Integrated `i64` constant | Integrated boundary and wrapping execution | None |
| LINK-01 | Link verified Talk IR modules | Required | Integrated exact source supplier/import identities, immutable scalar global readers, and direct package interfaces | Integrated exact external callable identity, generated readers, and generated initializer bodies | Integrated real scalar source-module linking with deterministic package graph orchestration and output re-verification | Linked package calls and immutable Unit/Bool/Int/Float dependency globals execute through validated bytecode | Mutable globals, writes, aggregates, managed storage, and precompiled-only readers |
| LINK-02 | Globals and deterministic module initialization | Required | Integrated source declaration order and exact generated reader relation | Integrated constants, dynamic initializer functions, external reads as reader calls, and dense order | Integrated scalar globals, exact actions, reader-import dependency ordering, initialized-read checks, and cycle rejection | Dedicated validated scalar global slots and once-before-entry execution | Mutable/written dependency globals and non-scalar storage |
| GEN-01 | Generic function execution and monomorphization | Required | Integrated with complete ordered recursive identity substitutions | Partial for local unqualified scalar bodies/calls with substituted-signature verification | Partial: private canonical-key worklist emits monomorphic recursive/deduplicated local scalar specializations | Partial: admitted Int and Bool specializations execute with zero resources | Predicate witnesses and cross-module specialization supply |
| WIT-01 | Static witness and protocol-default dispatch | Required | Integrated for explicit conformance resolutions and exact exported scalar recipes; protocol-default calls still fail to publish an implementation | Partial: exact selected local/imported scalar implementation and conformance-row agreement integrated; unselected defaults reject | Partial: selected local bodies and imported scalar recipes materialize without search | Partial for local and imported Core scalar implementations | Frontend-selected protocol defaults and general external generic supply |
| WIT-02 | Selected witness for direct protocol-requirement/operator calls | Required | Integrated unique conformance, requirement, implementation, and audited scalar recipe selection with validation | Integrated exact implementation preservation and row verification without search | Partial for locally defined implementations and imported scalar recipes; general external generic demand rejects with signature | Partial for covered arithmetic/comparison implementations | General external generic module ABI |
| AGG-01 | Tuple and closed-record values | Required | Integrated | Rejected | Forms exist but unverified | Not connected | Anonymous aggregate contract |
| AGG-02 | Value structs and projections | Required | Integrated | Rejected | Forms exist but unverified | Not connected | L2 representation and lowering |
| AGG-03 | Enums, tags, and payloads | Required | Integrated | Rejected | Forms exist but unverified | Not connected | L2 representation and lowering |
| PAT-01 | Literal, aggregate, variant, wildcard, and or-pattern CFG | Required | Integrated resolutions | Rejected | N/A after MIR compilation | Not connected | L2 MIR pattern compiler |
| OWN-01 | Narrow affine local move and cleanup | Required | Integrated modes | Partial | Rejected | Not connected | O1 Talk IR and backend cleanup |
| OWN-02 | Affine arguments, results, temporaries, joins, and loops | Required | Integrated modes | Rejected outside narrow subset | Rejected | Not connected | O1 producer and verifier widening |
| OWN-03 | Strict-linear finite-exit checking | Required | Integrated grade | Not implemented | Rejected | Not connected | O1 analysis and verification |
| OWN-04 | Assignment replacement and drop flags | Required | Integrated mutability | Partial in MIR | Rejected | Not connected | O1 lowering and execution |
| BOR-01 | Shared and mutable borrows | Required | Integrated modes and types | Shared Copy-scalar parameters and call arguments integrated; mutable and non-Copy borrows reject | Verified shared scalar loans erase after MIR | Shared scalar calls execute with zero resources | Mutable writeback and non-Copy storage |
| BOR-02 | Reborrow, projection, call transfer, and endings | Required | Integrated facts | Shared scalar call transfers and finite-path endings integrated; reborrow/projection remain fixture-only | Shared scalar transfer facts erase after verification | Shared scalar calls integrated | Aggregate projection and mutable borrow support |
| BOR-03 | Successful and rejected provenance queries | Required | Contracted query vocabulary | Successful source-backed shared scalar graphs derive from structural CheckedMir; rejected graphs remain fixture-only | N/A | N/A | Rejected source diagnostics and production reborrow/capture provenance |
| MEM-01 | Allocation and managed storage | Required | Integrated effects/types | Rejected | Forms exist but unverified | Not connected | Accepted R1 design; coordinated G0 contract stack |
| MEM-02 | String and byte storage | Required | Integrated | Rejected | Rejected | Not connected | R1 storage and intrinsic semantics |
| MEM-03 | Array, Storage, and Dict | Required | Integrated | Rejected | Rejected | Not connected | R1 managed storage and glue |
| MEM-04 | Type-specific clone and CoW | Required | Integrated explicit coercions | Clone contracted; execution rejected | Rejected | Not connected | R1 generated clone and runtime support |
| MEM-05 | Destroy and Deinit glue | Required | Integrated contracts | Partial affine destroy only | Rejected | Not connected | O1/R1 generated glue |
| HEAP-01 | Heap objects and graph mutation | Required | Integrated representation facts | Rejected | Accepted merge-only region design; G0 forms pending | Not connected | R1 coordinated G0 stack and implementation |
| HEAP-02 | Cyclic heap graph teardown | Required by baseline corpus | Integrated source typing | Rejected | Accepted direct object-cycle and two-phase teardown semantics; G0 forms pending | Not connected | R1 region implementation and exact resource oracles |
| CLO-01 | Closure environments and checked captures | Required | Integrated | Rejected | Forms exist but unverified | Not connected | H1 capture verification and conversion |
| CLO-02 | Indirect calls, local recursion, and trailing blocks | Required | Integrated | Indirect calls rejected | Rejected | Not connected | H1 closure calling convention |
| DYN-01 | Existential pack/unpack and owned payload | Required | Integrated coercions | No explicit executable pack | Rejected | Not connected | D1 MIR contract gap |
| DYN-02 | Dynamic witness dispatch and associated bindings | Required | Integrated | Contracted; production rejected | Rejected | Not connected | D1 witness representation |
| EFF-01 | Dynamic deep handler installation and perform | Required with ADR 0032 semantics | Integrated contracts | Rejected | Forms exist but unverified | Not connected | C1 implementation |
| EFF-02 | One-shot Resume and Discontinue | Required with ADR 0032 semantics | Integrated behavior | Not implemented | Forms exist but unverified | Not connected | C1 control-linearity and runtime |
| EFF-03 | Generic effect instantiations | Required | Integrated | Rejected | Rejected | Not connected | L1/H1/C1 |
| EFF-04 | Abort cleanup across frames and finalizers | Required | Integrated effects | Not implemented | Rejected | Not connected | C1 discontinue cleanup |
| CORE-01 | Unicode grapheme behavior | Required | Integrated frontend/core | Rejected | Rejected | Not connected | R1/K1 runtime core |
| CORE-02 | Iteration and `for` execution | Required | Integrated desugaring/types | Rejected downstream forms | Rejected | Not connected | L2/O2/R1/H1 |
| CORE-03 | Character borrowed grapheme view | Required | Integrated type and source operations | Rejected | No scalar representation by design | Not connected | O2/R1/K1 borrowed aggregate representation |
| IO-01 | stdout and captured IO | Required | Integrated core effect | Rejected | Rejected | Not connected | K1 host import contract |
| IO-02 | file, socket, poll, and sleep operations | Required | Integrated core contracts | Rejected | Rejected | Not connected | K1 stable host imports |
| UNSAFE-01 | Unsafe raw memory and inline IR | Required only behind unsafe source gate | Integrated source gate | Rejected | Rejected | Not connected | R1/K1 explicit intrinsic contract |

## Integrated gate rows

| Slice | G0 | G1 | G2 | G3 | G4 | G5 | Commit / note |
| --- | --- | --- | --- | --- | --- | --- | --- |
| Canonical TypedProgram cutover | Pass | Pass | Pass | Pass | Pass | N/A | `03128941` |
| Copy-scalar CFG through Talk IR | Pass | Pass | Pass | Pass | Pass | Not connected | Through `b73ad318`, validated on current head |
| Affine MIR subset | Pass | Pass | Pass | Pass to MIR; Talk IR rejects | Pass | Not connected | MIR integrated; not an executable parity row |
| E1 executable scalar core | Pass | Pass | Pass | Pass | Pass | Pass | Source-to-validated-bytecode handshakes and complete integration matrix passed |
| E2 module linking and globals | Pass for scalar callable/global contract, exact immutable scalar reader relation, and ephemeral package build plan | Pass for direct scalar source modules, package interfaces, exact locked-source validation, generated reader suppliers, and generated initializer suppliers | Pass for exact selected-graph linker inputs, missing/incompatible reader supply, unreachable/mismatched package supply, global schedule, and cycle negatives | Pass for stable global identity, exact Unit/Bool/Int/Float type, immutable access, one supplier, frontend-interface erasure before linking, and dependency-before-consumer initialization | Pass for the real package, linker, and CLI paths | Pass for linked immutable scalar dependency reads with zero-resource execution | Mutable globals, writes, aggregates, managed storage, and precompiled-only readers remain |
| L1 monomorphization and static witnesses | Pass for existing contract, local unqualified scalar keys, and audited exported scalar recipes | Pass for canonical generic production/validation, local generic calls, exact selected local implementations, and imported scalar recipe materialization | Pass for unexpected monomorphic and missing/duplicate/unknown/reordered mappings, malformed recipes/MIR arity, residual type, mismatched implementation, deduplication, recursion, and stable general external-demand rejection | Pass for local specialization and imported scalar-recipe erasure laws | Pass on combined primary checkout, including package-root specialization and Core scalar operators | Pass for Int/Bool identity, recursive Int, selected scalar implementations, and P3 with zero-resource balance | Protocol-default selection, predicate witnesses, and general cross-module generic bodies remain |
| L2 Copy aggregates and patterns | Pending | Pending | Pending | Pending | Pending | Pending | Contract audit required |
| O1 affine and strict-linear values | Partial | Partial | Partial | Pending | Pending | Pending | Narrow MIR subset only |
| O2 borrows and provenance | Contracted | Pending | Fixture-only | Pending | Pending | N/A until backend erasure | Parallel correctness lane |
| R1 managed storage and heap | Accepted design; G0 pending | Pending | Pending | Pending | Pending | Pending | ADR 0033 accepted at P7; implementation remains blocked on the coordinated G0 contract stack |
| H1 closures and indirect calls | Contracted | Pending | Pending | Pending | Pending | Pending | Depends on R1/O2 |
| D1 existentials and dynamic dispatch | Partial contract | Pending | Pending | Pending | Pending | Pending | MIR contract gap likely |
| C1 deep one-shot effects | Contracted | Pending | Pending | Pending | Pending | Pending | Depends on O1/O2/R1/H1 |
| K1 Core and host IO | Contracted | Pending | Pending | Pending | Pending | Pending | Depends on executable core rows |
| T1 tool parity | N/A | Pending | Pending | Pending | Pending | Pending | Restored incrementally |

## Complete-program corpus

All 16 baseline corpus files remain in `tests/programs`. On 2026-07-14 each
file passed the current frontend command independently:

```text
talk check tests/programs/<name>.tlk
```

The same day, every program was executed with the immutable baseline compiler.
All commands exited 0 with empty stderr. Their byte-exact stdout is frozen under
`tests/parity/programs`. The archived 17-test corpus suite also passed under its
VM/evaluator agreement and allocation/object balance policy. The current
`every_parity_program_has_a_frozen_stdout_oracle` test enforces a one-to-one
source/oracle inventory, and `parity_programs_still_pass_frontend_checking`
keeps every source accepted by the current frontend.

Frontend acceptance does not advance MIR, Talk IR, or backend gates. Baseline
output does not override an accepted ADR 0032 semantic change.

| ID | Program | Class | Principal required slices | Baseline oracle | Current state |
| --- | --- | --- | --- | --- | --- |
| CORP-01 | `tuple_access.tlk` | Required | L2, O2, E1 | Frozen: `tests/parity/programs/tuple_access.stdout`; exit 0, empty stderr, baseline balance pass | Frontend passes; MIR unsupported |
| CORP-02 | `conditional_moves.tlk` | Required | O1, R1, E1 | Frozen: `tests/parity/programs/conditional_moves.stdout`; exit 0, empty stderr, baseline balance pass | Frontend passes; MIR/Talk IR unsupported |
| CORP-03 | `string_building.tlk` | Required | E1, R1, O1 | Frozen: `tests/parity/programs/string_building.stdout`; exit 0, empty stderr, baseline balance pass | Frontend passes; managed values unsupported |
| CORP-04 | `string_patterns.tlk` | Required | L2, O2, R1, K1 | Frozen: `tests/parity/programs/string_patterns.stdout`; exit 0, empty stderr, baseline balance pass | Frontend passes; patterns/storage unsupported |
| CORP-05 | `clone_method.tlk` | Required | L1, O1, R1 | Frozen: `tests/parity/programs/clone_method.stdout`; exit 0, empty stderr, baseline balance pass | Frontend passes; clone execution unsupported |
| CORP-06 | `iterate_and_match.tlk` | Required | L1, L2, O1, O2, R1, H1, K1 | Frozen: `tests/parity/programs/iterate_and_match.stdout`; exit 0, empty stderr, baseline balance pass | Frontend passes; downstream unsupported |
| CORP-07 | `heap_graph.tlk` | Required pending R1 decision | L2, O1, R1 | Frozen: `tests/parity/programs/heap_graph.stdout`; exit 0, empty stderr, baseline balance pass | Frontend passes; heap semantics unresolved |
| CORP-08 | `graphemes.tlk` | Required | L1, L2, O2, R1, H1, K1 | Frozen: `tests/parity/programs/graphemes.stdout`; exit 0, empty stderr, baseline balance pass | Frontend passes; downstream unsupported |
| CORP-09 | `handlers.tlk` | Required with ADR 0032 routing | O1, R1, H1, C1 | Frozen baseline: `tests/parity/programs/handlers.stdout`; reviewed Talk-rendering replacement: `tests/parity/reviewed-programs/handlers.stdout` | Frontend passes; effects unsupported |
| CORP-10 | `caller_locals_handler.tlk` | Required with ADR 0032 routing | O1, R1, H1, C1 | Frozen: `tests/parity/programs/caller_locals_handler.stdout`; exit 0, empty stderr, baseline balance pass | Frontend passes; effects unsupported |
| CORP-11 | `nested_handlers.tlk` | Required with ADR 0032 routing | O1, R1, H1, C1 | Frozen: `tests/parity/programs/nested_handlers.stdout`; exit 0, empty stderr, baseline balance pass | Frontend passes; effects unsupported |
| CORP-12 | `resume_across_frames.tlk` | Required | O1, R1, H1, C1 | Frozen: `tests/parity/programs/resume_across_frames.stdout`; exit 0, empty stderr, baseline balance pass | Frontend passes; effects unsupported |
| CORP-13 | `multi_effect_handlers.tlk` | Required | L1, O1, R1, H1, C1 | Frozen: `tests/parity/programs/multi_effect_handlers.stdout`; exit 0, empty stderr, baseline balance pass | Frontend passes; effects unsupported |
| CORP-14 | `generic_state.tlk` | Required | L1, O1, R1, H1, C1 | Frozen: `tests/parity/programs/generic_state.stdout`; exit 0, empty stderr, baseline balance pass | Frontend passes; generic effects unsupported |
| CORP-15 | `generic_two_instantiations.tlk` | Required | L1, O1, R1, H1, C1 | Frozen: `tests/parity/programs/generic_two_instantiations.stdout`; exit 0, empty stderr, baseline balance pass | Frontend passes; generic effects unsupported |
| CORP-16 | `effectful_closures.tlk` | Required | L1, O1, R1, H1, C1 | Frozen: `tests/parity/programs/effectful_closures.stdout`; exit 0, empty stderr, baseline balance pass | Frontend passes; effectful closures unsupported |

### Corpus completion rule

A corpus row moves to parity only when:

- its expected output and result are frozen and reviewed;
- it passes through real TypedProgram, CheckedMir, and Talk IR producers;
- it executes through bytecode;
- all allocations and external resources balance;
- any changed behavior is tied to an accepted ADR rather than an implementation
  accident.

## Archived suite disposition

This table summarizes the exact per-test audit in
`tests/parity/baseline-test-disposition.tsv`.

| Archived suite or family | Class | Current destination |
| --- | --- | --- |
| Source acceptance and rejection | Required / Changed / Reject per case | Frontend producer tests plus parity ledger disposition |
| Move, initialization, affine cleanup, linearity | Required | MIR producer diagnostics, verifier negatives, O1 handshakes |
| Borrow conflicts and escape | Required under ADR 0032 restrictions | O2 producer diagnostics, provenance tests, verifier negatives |
| Old flow facts, candidate states, and annotation snapshots | Internal | No port; replace with artifact-interface tests |
| Aggregate and pattern execution | Required | L2 source, MIR, Talk IR, and backend tests |
| Monomorphization and static witnesses | Required | L1 lowerer and backend tests |
| Existentials and GADT payloads | Required | D1 contract, lowering, and backend tests |
| Closures, cells, indirect calls, trailing blocks | Required | H1 vertical tests |
| Handler resume/abort/unwind | Required with ADR 0032 semantics | C1 vertical tests |
| Allocation, deinit, CoW, arrays, heap graphs | Required or Decision required | R1 vertical and resource-balance tests |
| IO, sockets, poll, sleep, HTTP examples | Required | K1 host import and black-box tests |
| Lambda-G structure and printing | Internal | No port |
| Old scheduler chunk/register shape | Internal | No port; new bytecode adapter has its own target tests |
| VM versus evaluator equality | Internal as written | Freeze expected outputs, then bytecode; later bytecode versus Wasm differential tests |
| Old evaluator leak fence | Internal implementation, Required invariant | Reference runtime resource accounting on every G5 test |
| Raw VM safety tests | Required runtime invariant where representation still applies | New bytecode decoder/interpreter negative tests |
| Bytecode rendering and serialization | Required tool behavior | T1 tests over the new bytecode format |
| Old runtime direct tests | Supporting evidence only | Keep active; do not count as compiler parity |

## Tool parity

| ID | Surface | Class | Baseline behavior | Current state | Restoration point |
| --- | --- | --- | --- | --- | --- |
| TOOL-01 | `talk parse` | Required | Parse-tree inspection | Integrated | Complete |
| TOOL-02 | `talk hover` | Required | Position and node hover | Integrated | Complete |
| TOOL-03 | `talk format` | Required | Source formatting | Integrated | Complete |
| TOOL-04 | `talk html` | Required | HTML highlighting | Integrated | Complete |
| TOOL-05 | `talk check` | Required | Frontend diagnostics | Integrated | Package-awareness remains separate frontend work |
| TOOL-06 | `talk run` | Required | Compile and execute source | Integrated for E1 scalar source, local unqualified scalar generic specializations, audited imported Core scalar operators, direct immutable scalar package-global reads, and explicit `--entry`; explicit filename behavior remains unchanged while no-filename dispatch can select a locked package; Talk-style results, Unit suppression, clean traps, and fail-closed unsupported forms are preserved | Widen with each parity slice; package behavior is tracked by TOOL-08 |
| TOOL-07 | `talk test` | Required | Discover and execute Talk tests | Not connected | T1 after executable harness |
| TOOL-08 | package run/test | Required | Package-aware compilation and execution | Partial: locked scalar package binaries support package-only `--bin`/`--offline`, `--entry`, exact selected-graph linking, immutable Unit/Bool/Int/Float dependency-global reads, Talk rendering, and zero-resource execution; package tests remain unconnected | E2 scalar package run integrated; package tests at T1 |
| TOOL-09 | executable REPL evaluation | Required | Evaluate entered source | Frontend-only | R1/H1/T1 |
| TOOL-10 | MIR inspection | Expansion replacement | Replaces old semantic-lowering inspection | Not exposed | E1/T1 |
| TOOL-11 | Talk IR inspection | Required replacement | Replaces old lambda-G `lower` output | Not exposed | E1/T1 |
| TOOL-12 | bytecode inspection | Required | Render target bytecode | Not connected | E1/T1 |
| TOOL-13 | emit bytecode image | Required | Serialize executable module | Not connected | T1 |
| TOOL-14 | run bytecode image | Required | Validate and execute image | Not connected | T1 |
| TOOL-15 | standalone C-launcher build | Required | Bundle bytecode with static runtime | Not connected | T1 after runtime interface audit |
| TOOL-16 | `talk-c` embedding | Required | Compile/execute through C-facing interface | Explicit frontend-only error | T1 |
| TOOL-17 | Swift embedding | Required | Swift wrapper over accepted runtime interface | Explicit frontend-only behavior | T1 |
| TOOL-18 | wasm embedding | Required | Browser/wasm host uses accepted execution path | Explicit frontend-only error | T1; distinct from Wasm target backend |
| TOOL-19 | old lambda-G `lower` output | Internal | Print deleted IR | Deliberately absent | Replaced by MIR/Talk IR inspection |

## Deliberate ADR 0032 changes and conservative restrictions

These rows must not be mistaken for missing parity when an archived case depends
on the old semantics.

| ID | Behavior | Classification | Required new behavior |
| --- | --- | --- | --- |
| CHG-01 | Handler clause performs the effect it handles | Changed | Route to the nearest outer handler; the clause is outside its own handler |
| CHG-02 | Multi-shot continuation use | Changed | Reject; v1 resumptions are one-shot |
| CHG-03 | Returning from a handler clause without Resume | Changed | Structural Discontinue on finite return |
| CHG-04 | Borrowed return or stored borrowed value | Reject | Source diagnostic under v1 restrictions |
| CHG-05 | Ordinary loan across suspension | Reject | Source diagnostic with complete provenance |
| CHG-06 | Mutable or owning handler capture | Superseded 2026-07-17 | The reference pins mutable captures in function values (cells); see the reopened wave 5 in the rebuild plan. The handler-clause classification is re-derived from the reference's handler-locals pins, not carried forward |
| CHG-07 | User-visible partial move | Reject | Reject unless a consuming whole-aggregate operation accounts for every payload |
| CHG-08 | Effectful cleanup | Reject | Cleanup cannot expose an unhandled user effect in v1 |
| CHG-09 | Liveness selects Copy, Move, Borrow, or clone | Changed | Type checking selects the operation before MIR |
| CHG-10 | Uniform reference counting | Changed | Remains rejected; use explicit ownership and type-specific storage policies |
| CHG-11 | Old lambda-G or reference evaluator as semantic authority | Internal | Neither returns |

## Baseline defects that do not define parity

The baseline's known residual defects remain tracked as correctness work. A false
rejection in the baseline is not a required rejection, and an unsafe acceptance
is not required acceptance.

| ID | Baseline residual | Parity treatment |
| --- | --- | --- |
| BASE-B11 | Field writes through some generalized inferred receivers fail late | Track as frontend or MIR correctness when the source row is reached |
| BASE-B12 | Some inferred let schemes retain an unsolved result meta | Fix before the affected row can pass G1 |
| BASE-FD | Pattern constraints on some operator-call results reject falsely | Fix when L2 pattern parity reaches the fixture |
| BASE-FUNC-SHOW | Showable for function values absent in baseline rewrite | Expansion unless separately adopted; does not gate parity against the reset tag |
| BASE-CONCRETE-EXTEND | Some partially concrete inherent extends absent in baseline rewrite | Expansion unless separately adopted |

## Backend breadth after feature parity

These rows do not gate bytecode feature parity.

| ID | Adapter | Class | Entry condition | Current state |
| --- | --- | --- | --- | --- |
| BACK-01 | Bytecode | Required | E1 common subset | Integrated reference adapter, validated execution, driver seam, and E1 CLI run surface |
| BACK-02 | WebAssembly target | Expansion | Calls, aggregates, cleanup, and managed storage stable | Not connected |
| BACK-03 | C translation | Expansion | Bytecode and Wasm agree on shared Talk IR rows | Not connected |
| BACK-04 | Cranelift | Expansion | Two simpler adapters have validated representation and calling conventions | Not connected |
| BACK-05 | LLVM | Expansion | Same as Cranelift plus a demonstrated optimization or platform need | Not connected |

The old C launcher around bytecode is TOOL-15, not BACK-03. The old wasm
embedding path is TOOL-18, not BACK-02.

## Resource and runtime invariants

Every executable row that owns resources must eventually record these
observations:

| Invariant | Required evidence |
| --- | --- |
| No leaked owned value | Runtime live allocation/object count returns to the accounted result footprint |
| No double destroy | Runtime rejects duplicate destruction; source fixtures balance |
| No use after destroy | Runtime rejects invalid bytecode access; MIR verifier prevents source path |
| CoW clone correctness | Shared buffer clone retains each owned element exactly as required |
| Replacement correctness | Old destination is destroyed once before initialization |
| Deinit ordering | Hook and structural field teardown follow the adopted order |
| Abort cleanup | Every abandoned affine frame value is destroyed in reverse initialization order |
| Linear control | Every finite exit consumes each strict-linear value exactly once |
| External resource balance | Files, sockets, and host handles close or transfer according to their contract |
| Bytecode safety | Decoder rejects invalid versions, indices, lengths, opcodes, and signatures |

There are no anonymous resource-test exemptions. A temporary expected failure is
named in this ledger with an owner and removal condition.

## Next ledger actions

Follow the detailed lane ownership and checkpoints in the
[parallel implementation plan](backend-parity-plan.md#parallel-implementation-plan-after-e2-scalar-globals).

1. Lane A scalar package graphs, Lane B local L1 specialization, their P3
   coexistence handshake, and audited imported scalar implementation recipes are
   integrated. Keep arbitrary cross-module generic bodies fail-closed until a
   real module-ABI slice defines their supply.
2. Lane C Prov-1 fixture-backed provenance is integrated, but source production
   stays pending until Prov-2/P5 lands against the merged MIR generator.
3. The P6 immutable Unit/Bool/Int/Float source-dependency read slice is
   integrated through generated callable suppliers. Keep mutable globals,
   writes, aggregates, managed storage, and precompiled-only reader supply
   fail-closed. P7 accepted ADR 0033; managed-storage implementation remains
   blocked on the coordinated R1 G0 contract stack.
4. Split newly discovered user behavior into its own capability row and advance
   rows only in the same commit that integrates their support.
