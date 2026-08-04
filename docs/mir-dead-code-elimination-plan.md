# MIR dead-code elimination plan

Status: partially implemented - Stage 1 complete; narrow Stage 2 experiment implemented under proposed ADR 0049

Baseline: `3ef0f6d9` (2026-07-31)

## Summary

Deepen the compiler-owned MIR optimization module in two deliberately separate
steps:

1. add whole-program function reachability elimination after inlining and local
   simplification;
2. investigate effect-aware handler elimination behind an ADR gate before
   attempting to remove the host fallback machinery from pure programs.

The first step is a conventional, semantics-preserving optimization over the
closed MIR module. The second touches ADR 0039's explicit decision that every
core-backed program carries `_with_host`, so it is not treated as ordinary DCE
or smuggled into the first change.

## Baseline behavior

At the baseline, the optimization pipeline in `src/compiling/mir/optimize/`
simplified each function, forwarded direct calls, inlined small primitive
functions, and then simplified each function again. Its `dead_code` pass
removed unused local `Copy`, `Field`, and non-trapping `Scalar` instructions,
but did not remove whole functions.

MIR construction is demand-driven, but optimization can make a previously
reachable function unreachable. For example, inlining `add` into a caller and
folding the result leaves the original `add` function in `Module.functions`.
All target adapters then carry and lower that dead function because finalized
MIR is their shared public seam (ADR 0047).

At the baseline commit:

```text
printf '1 + 2\n' | talk mir
    348 lines
    12 functions

printf '1 + 2\n' | talk mir --no-opt
    438 lines
    12 functions
```

The optimized module still contains `script`, `add`, and `shared_drop` after
their last references disappear. It also contains `_with_host`, `_io_host`,
the fallback clauses, and `write_string`; those remain referenced under the
current entry design and are not function-DCE bugs.

## Implementation progress

Stage 1 is implemented in `src/compiling/mir/optimize/dead_functions.rs`. The
pass runs after inlining and the final local simplification, retains entry and
export roots, follows direct calls and closure constructions, compacts function
IDs, and reports its removal count as `dead_functions`.

Stage 1 reduced `1 + 2` from 12 functions and 348 optimized-MIR lines to 9
functions and 338 lines. The narrow Stage 2 experiment now reduces it to 3
functions and 21 lines; raw MIR remains 12 functions and 438 lines. Together
the passes reduce `bootstrap/frontend.tbc` from 764,456 to 758,130 bytes and
generated C from 182,832 to 180,153 lines.

## Goals

1. Remove every function not transitively reachable from the module entry or a
   host-callable export after the existing inlining and simplification passes.
2. Keep all `FuncId` references valid after compacting `Module.functions`.
3. Preserve deterministic relative ordering among retained functions.
4. Run the pass before escape summaries, register allocation, and frame
   shaping, so those analyses only process retained functions.
5. Report removed functions in compiler-owned optimization statistics.
6. Preserve raw MIR: `talk mir --no-opt` continues to show the builder output.
7. Validate the finalized result through the bytecode, C, and LLVM adapters.
8. Establish a separate, explicit decision path for effect-aware host-handler
   elimination rather than weakening ADR 0039 implicitly.

## Non-goals

- Do not add effect names or host operation knowledge to the compiler.
- Do not identify functions by debug names such as `_with_host` or `_io_host`.
- Do not remove a side-effecting or trapping instruction merely because its
  result local is unused.
- Do not add MIR serialization, a second MIR verifier, or a generic pass
  framework.
- Do not change source semantics, effect routing, bytecode format, or target
  adapter interfaces.
- Do not make the raw `--no-opt` rendering smaller.
- Do not claim that function DCE alone removes the host dispatcher.

## Invariants

### Reachability roots

The roots are:

- `Module.entry`;
- every function referenced by `Module.exports`.

Exports are roots even when the inert service entry does not call them.

### Reachability edges

The current public MIR has exactly two instruction positions that contain a
`FuncId`:

- `Inst::Call.func`;
- `Inst::MakeClosure.func`.

Both are graph edges. `CallIndirect` does not name a function; its possible
code enters the module through a reachable `MakeClosure`, which retains that
closure body. A `MakeClosure` inside an unreachable function does not retain
its target.

Any future MIR form that carries a `FuncId` must update this pass in the same
change.

### Compaction

Compaction must rewrite:

- `Module.entry`;
- each `Module.exports[*].1`;
- every retained `Inst::Call.func`;
- every retained `Inst::MakeClosure.func`.

Retained functions keep their original relative order. Layout IDs, globals,
display metadata, block IDs, local IDs, and frame facts are unaffected.

## Stage 1: Whole-program function DCE

### Implementation

1. Add `src/compiling/mir/optimize/dead_functions.rs`.
2. Starting from all roots, walk direct calls and closure-construction edges to
   a fixed point. Use an indexed worklist and one boolean reachability vector;
   no call-graph abstraction is needed.
3. Build one old-to-new `FuncId` map while retaining reachable functions in
   original order.
4. Rewrite the entry, exports, calls, and closure constructors through that
   map, then replace `Module.functions` with the compacted vector.
5. Return `PassResult::applied(removed_function_count)`.
6. Invoke the pass once at the end of `optimize::run`, after the second local
   simplification loop. A single graph traversal is sufficient because all
   edge-removing passes have already run.
7. Add a `dead_functions` row to `OptimizationStats`. Update the bootstrap test
   that currently pins eight compiler passes to expect nine while retaining
   its stage-1/stage-2 equality assertion.

### Focused tests

Add unit tests at the optimization module interface for:

1. an unreferenced function being removed;
2. a transitive direct-call chain being retained;
3. a closure body referenced only by `MakeClosure` being retained;
4. a closure body referenced only from a dead function being removed;
5. every export being retained even when the ordinary entry cannot reach it;
6. compaction remapping entry, export, direct-call, and closure IDs correctly;
7. stable relative ordering of retained functions;
8. an already-closed module reporting zero changes.

Prefer small hand-built `talk_mir::Module` values in the pass tests. Test the
optimization interface rather than introducing a public builder or verifier.

### End-to-end tests

Extend CLI coverage so that:

- optimized `talk mir` omits a helper made unreachable by inlining;
- `talk mir --no-opt` still renders that helper;
- an exported function survives even when the service entry is inert.

Run representative programs through all three adapters after compaction. The
shared finalized-MIR seam means this is one compiler change, not three target
implementations, but all adapters index `Module.functions` and therefore need
regression coverage.

### Acceptance

For `1 + 2`, function DCE is expected to remove the now-unreferenced `script`,
`add`, and `shared_drop` functions. The test should assert semantic facts, not
pin the full rendered output or an exact line count.

The following must hold:

- optimized execution still evaluates to `3`;
- optimized MIR has no dangling function IDs;
- raw MIR remains unchanged;
- bytecode, C, and LLVM executions agree;
- compiler optimization statistics report the removed-function count;
- the self-hosted frontend fixed point remains valid after intentionally
  regenerating any compiler-produced artifact changed by function compaction.

## Stage 2 experiment: Effect-aware handler elimination

Function DCE cannot remove `_with_host` support while handler installations
retain their clause closures. [Proposed ADR 0049](adr/0049-proof-gated-effect-handler-elimination.md)
now governs a narrow implementation experiment rather than requiring a
read-only prototype first.

The implemented proof runs after function DCE and collects every effect named
by `FindHandler` in the reachable module. It removes a handler only when:

1. its effect has no `FindHandler` anywhere in that module;
2. its setup is the adjacent `MakeCont`, `MakeClosure`, `PushHandler` triple
   emitted by the builder;
3. the clause closure captures only that continuation.

The module-wide absence requirement is conservative across direct calls,
indirect calls, recursion, closures, module initialization, and exports because
all retained function bodies are scanned. Capturing handlers remain installed
to avoid disturbing ownership preparation for their environments. The rewrite
uses no host names, effect list, Core identity, or IO operation knowledge.

After removal, local simplification and function DCE run again so unreachable
clauses, `_io_host`, and support functions disappear through ordinary graph
reachability. Closure devirtualization, hidden-result-slot removal, layout-table
compaction, and more precise dynamic-extent analysis remain separate work.

This experiment is accepted or reverted based on semantic and differential
tests. A failure narrows the proof; it does not justify host-specific
exceptions.

## Validation commands

Run at minimum:

```sh
cargo test -p talk
cargo test -p talk-mir
cargo test -p talk-bytecode
cargo test -p talk-c
cargo test -p talk-llvm
cargo test --test talk_tests
cargo test --test c_backend_tests
cargo test --workspace
cargo run --bin talk -- bootstrap --check
printf '1 + 2\n' | cargo run --quiet --bin talk -- run
printf '1 + 2\n' | cargo run --quiet --bin talk -- mir
printf '1 + 2\n' | cargo run --quiet --bin talk -- mir --no-opt
```

If function compaction intentionally changes the checked-in frontend artifact,
regenerate it first, review the generated C and manifest diff, then require
`bootstrap --check` to pass. Do not weaken the fixed-point check.

## Completion and documentation

Stage 1 is complete when whole-program function DCE is tested, reported, and
validated across every target. Record durable optimizer ordering or semantic
rules in an ADR only if they become architectural decisions; otherwise keep
them next to the pass implementation.

The narrow Stage 2 experiment remains governed by proposed ADR 0049. Once the
ADR is accepted or the experiment is reverted, update this plan accordingly.
Once all retained stages are complete, remove this implementation plan in
accordance with `docs/README.md`; Git history remains the archive.
