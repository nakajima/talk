# ADR 0049: Proof-gated elimination of unused effect handlers

Status: proposed; experimental implementation passes current validation

Amends ADR 0039 only if accepted. ADR 0039's source semantics, ordinary handler
routing, source-owned host behavior, and ban on compiler-known effect policy
remain unchanged. This ADR would amend only the requirement that every compiled
core-backed program physically carries every host fallback frame.

Implementation plan: [MIR dead-code elimination plan](../mir-dead-code-elimination-plan.md).

## Context

ADR 0039 made host fallbacks ordinary Talk handlers in `core/Host.tlk`. The
compiler knows `_with_host` as the entry supplier but knows no host effect
identities, IO request cases, or fallback policies. This restored one routing
model:

```text
nearest user handler -> next outer user handler -> core fallback
```

The entry builder therefore wraps every core-backed script, named entry, and
host export in `_with_host`. Even a closed pure program such as `1 + 2` carries
four handler installations, their clause closures, the complete IO request
dispatcher, panic reporting, and a hidden result slot.

Whole-program function DCE removes functions made unreachable by inlining and
local simplification, but it cannot remove this machinery while `_with_host`
still constructs every clause. Those functions remain graph-reachable; this is
not a function-DCE defect.

ADR 0038 assigns semantic authority to typing. MIR may optimize already-valid
checked code, but it may not reconstruct effect legality or invent runtime
policy. Any handler removal must therefore be a conservative erasure proof over
explicit whole-program MIR, never a second effect checker.

## Proposed decision

### 1. The initial proof is module-wide absence

After whole-program function DCE removes unreachable functions, collect every
effect named by `FindHandler` in the remaining module. A handler for effect `E`
may be considered unused only when no reachable function contains
`FindHandler(E)`.

This is deliberately stronger and less precise than a dynamic-extent analysis.
It does not need to solve indirect-call targets: every function body retained
through a direct call or reachable `MakeClosure` is scanned whether or not that
body is eventually invoked. An effectful closure carries `FindHandler(E)` in
its body, where invocation-scoped routing resolves it (ADR 0051). Recursion,
delegation, module initialization, and export bodies likewise leave their
explicit requests in the retained module.

Failure to establish module-wide absence keeps every handler for that effect.
The optimizer may miss removable handlers, but it cannot infer purity from a
missing local call edge or unresolved `CallIndirect`.

The proof affects optimization only. It cannot accept a source program typing
rejected, reject a source program typing accepted, change an inferred effect
row, or change which handler a reachable perform selects.

### 2. The analysis is generic over ordinary effects

The analysis compares only `MirSymbol` identities already carried by
`PushHandler` and `FindHandler`. It may not:

- name `_with_host`, `_io_host`, or any function by its debug name;
- recognize Core module IDs as policy;
- contain a list of host effects;
- inspect IO request tags or host operation numbers;
- treat a handler differently because its source lives in core; or
- add a host-only MIR instruction or runtime bypass.

The same proof and rewrite apply to a captureless user handler with the same
MIR shape.

### 3. The initial rewrite is ownership-narrow

The builder emits a captureless handler setup as one adjacent instruction
triple:

```text
MakeCont continuation
MakeClosure clause, env: [continuation]
PushHandler effect, clause, continuation
```

When the effect is absent module-wide, the optimizer may erase this exact
triple. The IDs and operands must agree structurally. The clause environment
must contain only the continuation.

A clause closure that captures any additional value is retained even when its
effect appears absent. Captured user values may have retain, release, region,
or unwind preparation outside the triple; deleting only the closure could
change ownership. Supporting such handlers requires a separate ownership-aware
proof and is not part of the initial implementation.

The optimizer does not declare `MakeCont` or `MakeClosure` generally pure or
removable. It removes them only as part of the proven handler setup.

### 4. Existing simplification removes the support graph

The pass runs after the first whole-program function-DCE pass. If it removes a
handler triple, local simplification runs again and function DCE runs a second
time. Clause bodies and support functions such as `_io_host` disappear only
when their ordinary `Call` and `MakeClosure` references are gone.

The pass reports the number of removed installations as `dead_handlers` in
compiler optimization statistics.

Closure-call devirtualization, hidden-result-slot removal, unused layout-table
compaction, and forwarding-frame elimination are separate optimizations. This
ADR does not fold `_with_host` itself merely because all of its handlers vanish.

### 5. Finalized MIR remains the one target seam

The analysis and rewrite remain compiler-owned and run before escape summaries,
register allocation, and frame shaping. Bytecode, C, and LLVM consume the same
finalized `talk_mir::Module` without target-specific effect logic or new adapter
interfaces.

Raw `talk mir --no-opt` continues to show every source and synthesized handler.
Optimized `talk mir` shows only handlers retained by the proof.

## Experimental implementation

The proposal is evaluated by implementing the narrow production rewrite and
running the existing semantic and differential suites. There is no separate
read-only classification phase.

The experiment must cover:

- a pure scalar script;
- direct IO, allocation, async, and panic performs;
- nested user handlers and same-effect delegation;
- resumable and abortive clauses;
- discontinue through cleanup frames;
- effectful closure bodies with invocation-site handler lookup;
- closures stored in globals, aggregates, existentials, and cells;
- direct, recursive, mutually recursive, and indirect calls;
- module initialization;
- host exports; and
- the self-hosted frontend fixed point.

Acceptance requires all of the following:

1. The full workspace test suite passes with the rewrite active.
2. Existing effect-corpus behavior is unchanged across routing, results,
   output, cleanup, and failure paths.
3. Bytecode, C, and LLVM differential suites pass.
4. The implementation contains no function names, host-effect list, Core
   policy identity, or IO operation knowledge.
5. Capturing clauses fail closed by remaining installed.
6. Raw MIR remains unchanged.
7. The self-hosted frontend artifacts regenerate to a stable stage-1/stage-2
   fixed point and `bootstrap --check` passes.
8. Reduction is measured for `1 + 2` and the self-hosted frontend.

A failing semantic test is evidence to narrow or reject the rewrite, not to add
host-specific exceptions.

## Experimental results

The narrow rewrite passes the full workspace suite, including the effect corpus
and bytecode, C, and LLVM differential tests. `bootstrap --check` passes after
artifact regeneration.

For `1 + 2`, optimized MIR falls from Stage 1's 9 functions and 338 lines to 3
functions and 21 lines. Raw MIR remains 12 functions and 438 lines. Relative to
the pre-DCE baseline, `bootstrap/frontend.tbc` falls from 764,456 to 758,130
bytes and generated C from 182,832 to 180,153 lines.

No host-specific exception was needed. The implementation remains conservative:
any module-wide request retains all handlers for that effect, and any clause
capturing more than its continuation is left unchanged.

## Alternatives rejected by this proposal

### Omit `_with_host` from entries whose source appears pure

The top-level ambient row describes permitted effects, not necessarily a
minimal execution summary. Special-casing entry construction also optimizes one
source pattern instead of the ordinary handler mechanism.

### Match `_with_host` or `_io_host` by name

This contradicts ADR 0039's source-owned policy, makes debug names semantic,
and creates a host-only optimization path.

### Teach the compiler the host effect list

ADR 0039 explicitly removed that duplicate policy table. Reintroducing it for
code size would allow core source and compiler policy to drift.

### Infer absence within one function

Effects can occur through direct calls, closures, recursion, and delegation.
The initial implementation instead requires absence
from the entire reachable module.

### Remove capturing clause setup

This may strand ownership preparation or change cleanup. The initial rewrite
retains every clause whose environment contains more than its continuation.

### Rely on function DCE alone

Function DCE follows existing `Call` and `MakeClosure` edges. It correctly
retains handler support until the installation and clause-construction edge are
removed.

### Add a primitive host fallback instruction

That recreates the second routing model ADR 0039 rejected and prevents ordinary
user interception and delegation.

## Consequences if accepted

- ADR 0039's routing semantics remain unchanged, but its statement that every
  program carries all `_with_host` frames becomes a pre-optimization
  construction rule rather than a finalized-code requirement.
- Effects absent from the entire reachable module lose captureless handler
  setup and support functions reachable only from those handlers.
- Capturing handlers and any effect requested anywhere remain conservative
  misses, even if a more precise extent analysis could remove them.
- Core remains the sole owner of ambient effects and fallback behavior.
- No target adapter or runtime learns host effect policy.
- Optimization complexity stays behind the compiler's MIR optimization
  interface; no new public MIR seam is introduced.
- The self-hosted frontend artifact changes and must continue satisfying its
  fixed-point and manifest checks.
- More precise dynamic-extent or ownership-aware removal requires a later
  decision backed by new tests and measurements.
