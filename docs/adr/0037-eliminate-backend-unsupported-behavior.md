# 0037 - Eliminate backend capability rejections

Status: accepted; implementation in progress

Historical planning inventory: [backend unsupported inventory](../backend-unsupported-inventory.md)

## Context

The bytecode backend exposes the deep `compile`/`execute` interface adopted by
ADR 0034. After the MIR responsibility cleanup in ADR 0038, it still contains
58 calls to `BackendError::unsupported`: 52 in `mir/mod.rs`, four in
`mir/glue.rs`, and two in `mir/entries.rs`.

Those calls do not all mean the same thing. They include:

- valid source behavior whose runtime representation is incomplete;
- duplicate guards for one missing mechanism;
- source behavior that should have received a frontend diagnostic;
- CFG-sensitive ownership or initialization errors owned by MIR analysis;
- missing external implementations owned by linking; and
- recovery forms or violated compiler invariants that should be internal
  compiler errors.

The motivating example remains an ordinary method receiver captured by a
trailing block:

```talk
self.peek().map { ch in
    self.char_at(self.current + ch.utf8_count())
}?
```

Typing accepts the closure and now publishes its structural frame facts, but
the backend has no owning lifecycle for the receiver's closure-environment
slot. MIR therefore rejects a valid capture instead of generating environment
retain and drop operations.

ADR 0038 changed where the remaining work belongs. Before that cleanup, MIR
reconstructed source semantics from parser forms, checker side tables, catalog
searches, names, and runtime representation properties. The cleanup established
one owner for each class of decision:

| Decision | Owner |
| --- | --- |
| Syntax, spelling, and spans | parser |
| Canonical identity and lexical resolution | resolver |
| Source legality, finalized types, value-use modes, captures, patterns, effects, conformances, literals, and trusted operations | type checker |
| Immutable publication of frontend decisions | `TypedProgram` |
| Rigid substitution and evidence genuinely deferred until specialization | backend specialization |
| CFG, places, ownership dataflow, runtime representation, cleanup, and glue | MIR |
| External implementation supply | linker |
| Serialized bytecode validity | bytecode validator |

The refactor already moved canonical literals, checked pattern types and slots,
effect contracts, checked inline IR, committed conformance dictionaries,
callable ownership facts, frame structure, and absolute symbol identity to
their owning modules. The remaining capability work must preserve that
separation. Eliminating an unsupported branch by making MIR rediscover a
frontend fact would regress the architecture even if the branch disappeared.

The current companion inventory predates ADR 0038. Its 65-site count and source
line references are historical and do not satisfy this ADR's admission rule.
It must be regenerated before capability implementation resumes.

## Decision

The reference bytecode backend has executable semantics for every
frontend-valid, MIR-valid, closed Talk program. It may not reject such a program
because a source form, checked operation, runtime value shape, generic boundary,
or representation has not been implemented.

A source module may still fail before execution for a stable reason owned by the
appropriate module:

1. the type checker rejects an invalid source construct or checked operation;
2. MIR analysis rejects a CFG-sensitive ownership, exclusivity, linearity,
   initialization, or writeback violation;
3. the linker rejects a missing, duplicate, or incompatible external supplier;
4. bytecode validation rejects an untrusted or malformed serialized module; or
5. a violated compiler invariant produces an internal compiler error.

A successfully linked program that has passed the frontend and MIR analyses
must not encounter a compile-time capability rejection.

Every current `BackendError::unsupported` site must end in exactly one of these
states:

- valid behavior is implemented through the bytecode backend;
- invalid source receives a structured frontend diagnostic;
- invalid control-flow ownership receives a structured MIR diagnostic;
- missing external supply receives a structured linker diagnostic; or
- a proven-unreachable recovery form or violated invariant becomes an internal
  compiler error.

Moving an unsupported message into a generic frontend `Unsupported` error does
not satisfy this decision unless the language rule actually declares the form
invalid and the diagnostic identifies that rule.

## Error taxonomy

`BackendError { message, span }` currently conflates source diagnostics,
capability gaps, linking failures, and internal failures. Removing only the
`unsupported` constructor would allow the same rejection to survive under
`BackendError::new`, so constructor spelling is not the final invariant.

The compile seam will distinguish at least:

```text
CompileFailure
  frontend diagnostic
  MIR ownership or initialization diagnostic
  linker diagnostic
  internal compiler error
```

Runtime failures after execution begins remain a separate result of `execute`.
Each source-facing category has a stable diagnostic kind and source origin.
Internal compiler errors are never rendered as ordinary source diagnostics.

Completion still requires:

```text
rg "BackendError::unsupported" src/backend
```

to return no matches, but that grep is only one gate. Review must also prove
that no former capability rejection was renamed into another unstructured
error path.

## Admission rule: stable executable inventory

No capability wave begins from source line numbers. Every remaining unsupported
site first receives a stable identifier and one disposition:

- `VALID` - implement executable behavior;
- `DUP` - duplicate guard closed by another identified mechanism;
- `FRONTEND` - source-invalid under a named frontend rule;
- `MIR` - invalid under a named CFG-sensitive ownership rule;
- `LINKER` - missing or incompatible external supply;
- `ICE` - recovery-only form or violated compiler invariant.

The inventory records for each identifier:

- the triggering checked form;
- its owning module;
- its final behavior or diagnostic kind;
- one minimal source fixture or invariant test by path and test name; and
- the implementation mechanism that removes the site.

A repository test extracts the stable identifiers from the source and requires
an exact match with the inventory. Adding, deleting, or reclassifying a site
therefore changes the test. Source line numbers may be included for convenience
but are not identities.

A catch-all is not presumed unreachable. An `ICE` disposition requires a test
showing that successful `TypedProgram` construction cannot publish the form, or
that exhaustive matching over a checked enum excludes it.

## 1. Checked uses, captures, and writable-place facts

Before expanding runtime representation, the frontend seam must finish
publishing the source decisions that MIR still reconstructs.

Every call argument, receiver, capture, and other value-use edge carries its
checked semantic operation:

```text
borrow shared
borrow exclusive
consume
proven copy
selected clone
writeback
```

Copy and clone uses carry the evidence that made them legal. A checked writeback
use identifies a source-valid writable expression. A checked capture records:

- the canonical captured symbol;
- the finalized capture type;
- the checked capture operation;
- required Copy or clone evidence;
- whether assignment conversion requires a cell; and
- the capture's source origin.

`FrameFacts` already publishes the structural capture, cell, and nested-reference
sets. This step completes that publication with semantic use facts. MIR stops
interpreting `ArgMode`, `CaptureMode`, and runtime properties such as
`needs_release` as proof of source legality.

A true rvalue is not a writable `mut` argument. Typing reports that source error.
MIR may materialize internal temporaries for evaluation, but it does not turn an
invalid source rvalue into a writeback place whose evolved value is silently
discarded.

## 2. Places and initialization

MIR deepens the existing private place module rather than adding syntax-specific
assignment paths. A place identifies a storage root and a runtime projection
spine:

```text
Place
  root: local | global | cell
  projections: field | tuple element | record slot | payload
```

Captured mutable bindings use the cell representation selected by checked frame
facts. Internal temporaries may participate in MIR operations but are not a new
source category of writable place.

The place module owns:

```text
load
initialize
replace
move or take
borrow shared
borrow exclusive
write back
```

It supports:

- `let` declarations without initializers;
- definite-assignment checking before every read;
- assignment to globals, cells, and nested projections;
- replacement with exactly-once destruction of the displaced value;
- checked `mut` arguments and requirements over writable places; and
- generic or existential projection using published layout evidence.

Uninitialized storage has no default value. MIR computes initialization and
ownership over the CFG and reports structured diagnostics for reads before
initialization or invalid path joins.

A projection spine addresses a portion of storage for reading or writing. It
does not by itself reintroduce source-visible partial moves or field-granular
initialization. Root-level ownership and initialization remain consistent with
the implicit-sharing decision in `docs/ownership.md`; consuming
destructure accounts for every payload explicitly.

## 3. Runtime value operations and evidence transport

The backend has one private authority for runtime operations on a resolved value
representation:

```text
retain
destroy
invoke equality evidence
invoke show evidence
invoke a committed requirement entry
```

This authority does not select source conformances. Typing commits every
concrete decision it can make:

- conformance dictionaries in protocol requirement order;
- selected implementation symbols and writeback widths;
- associated evidence;
- derived-operation recipes;
- effect contracts and instantiations; and
- declared bounds on rigid parameters.

Backend specialization performs only the selection genuinely deferred because
a receiver remained rigid during typing. Coherence makes that operation a
forced dereference of a committed dictionary, not general conformance search.

Rigid generic values receive value-operation witnesses and required protocol
dictionaries through one hidden evidence block. The block is transported
consistently through:

- direct and indirect generic calls;
- closure and handler environments;
- existential packages;
- generic effects;
- imported generic implementations; and
- generated retain, drop, show, and equality glue.

Nested rigid positions such as `Array<(Int, T)>` carry the evidence needed by
the generated operation. Once evidence population is total, lookup failures
for a well-formed checked instance become internal compiler errors with fixture
coverage, not capability diagnostics.

Derived equality and show consume frontend-published derivation recipes. The
backend generates runtime code for every checked recipe and never infers
structural conformance from a runtime type shape or requirement name.

## 4. Owning closure environments

Closure environments become type-aware owning runtime values. Each environment
contains the slots and checked capture operations published by typing, inherited
generic evidence, and captured effect capabilities.

The runtime representation supports:

- implicit method-receiver capture;
- Copy captures;
- implicit-sharing snapshot captures;
- consuming captures;
- shared and exclusive borrowed captures where their checked lifetime permits;
- ownership-sensitive mutable cells;
- recursive closures and mutually recursive local functions;
- generic local functions that capture; and
- named functions with explicit capture lists.

MIR owns environment layout and lifecycle, not capture legality. Capturing a
shareable managed value retains a snapshot under the implicit-sharing decision.
A consuming capture moves a strict-linear value. A stored borrowed capture must
already have a checked non-escaping lifetime or an owning stored-view
representation.

Closure retain and destruction use generated environment glue. The last closure
reference releases every owning slot exactly once on normal return, early
return, handler resume, and discontinue paths. Generic slots carry the evidence
needed for cleanup. Cells and recursive environments use the same lifecycle and
are not exempt from resource accounting.

This mechanism closes the motivating `self` capture after the checked-capture
publication in section 1.

## 5. Pattern ownership and runtime projection

Typing now publishes pattern occurrence types, binder types, canonical variant
identity, struct slots, record slots, and instantiated payload types including
GADT refinements. MIR consumes those facts; it does not resolve source labels,
search declarations, instantiate pattern types, or parse pattern literals.

The pattern compiler owns decision-tree CFG and runtime ownership settlement.
On every arm, every payload is one of:

- moved to a binder;
- borrowed;
- retained as a snapshot;
- copied using checked evidence; or
- destroyed because it is unbound.

The outer aggregate is never a second implicit owner after its payloads have
been transferred.

Remaining executable cases include:

- or-pattern alternatives with different unbound owned payloads;
- patterns binding a whole field and inspecting its interior;
- float pattern tests;
- open-row record patterns;
- generic and existential field projection; and
- positional projection where the checked language form permits it.

Closed and monomorphized rows use published static slots. If the language admits
a genuinely open runtime row, typing publishes checked row-layout evidence and
MIR uses it for dynamic projection. MIR does not reconstruct a label-to-slot map
from source names. If no such checked evidence exists, typing must reject the
operation under a named language rule.

A pattern binding both a whole owning field and an interior value must express
one ownership relation: the interior is borrowed from the whole, copied with
checked evidence, or retained as a snapshot. Two binders never independently
claim the same ownership reference.

## 6. Globals and external implementations

Every executable global has stable storage, an initializer thunk,
initialization state, move state, type-aware teardown, and deterministic module
ordering. Literal shape does not decide whether a global receives storage.

The backend supports aggregate globals, non-literal initializers,
function-valued globals, global closures, general reads, and replacement where
the declaration permits mutation.

Absolute symbol identity and frontend-published initialization order from ADR
0038 are the identities used by storage and linking. MIR does not reconstruct
module aliases or source import order.

Strict-linear globals require a separate accepted static rule defining the
decidable analysis, summary domain, recursion treatment, indirect-call target
policy, and diagnostics. This ADR does not claim an exact semantic analysis of
all finite paths in arbitrary programs. It does require that linear globals end
in one stable state: supported under that rule or rejected by that rule, never
rejected because the backend lacks a representation.

Every callable reference resolves to exactly one supplier:

- a source body in the compiled graph;
- a linked bytecode implementation;
- a declared host function; or
- a trusted intrinsic.

Separately compiled modules use absolute symbol identity and a validated
callable interface. Missing, duplicate, or incompatible supply is a structured
linker error. It is not a MIR capability diagnostic.

## 7. Typed ambient effects

ADR 0039 owns the runtime policy and host-supply design for ambient effects. It
distinguishes interceptable typed requests from raw host primitives and unsafe
intrinsics, installs host implementations as ordinary outer fallback handlers,
and requires safe request contracts before user interception is enabled.

For this ADR, completion means the current blanket Core-handler rejection is
removed according to ADR 0039: checked ambient performs use ordinary capability
routing, raw IO and allocation remain non-interceptable, closure environments
capture only effects whose published policy permits handlers, and missing host
supply is a structured linker diagnostic.

## 8. Trusted inline IR

The ADR 0038 refactor completed the backend ownership change for trusted inline
IR. Typing publishes `CheckedIrKind`: a closed set of canonical operations,
checked types, and validated operands. MIR lowers that enum exhaustively and
performs only instance substitution and runtime memory-kind selection.

Parser-only operand variants do not automatically become valid checked IR.
`uninit`, `poison`, aggregate constants, raw pointer literals, and static raw
buffers currently have no checked value semantics. Until a separate language
decision defines those semantics, typing rejects them with specific diagnostic
kinds; they do not reach MIR and are not represented by a generic capability
error.

The unsafe effect gate remains mandatory and is owned by typing. Supporting a
checked trusted operation does not make it safe or remove bytecode validation
at the serialized-module trust seam.

No new backend implementation wave is required for the currently checked inline
IR enum. Future checked operations must add frontend validation and exhaustive
MIR lowering in the same change.

## 9. Exhaustive backend lowering

After the shared mechanisms land, remaining generic fallbacks are audited
against checked typed-tree and checked-operation enums, not parser enums.

Every checked variant is one of:

- exhaustively lowered;
- erased by a documented frontend transformation;
- rejected before `TypedProgram` publication under a named language rule; or
- recovery-only and asserted unreachable in compilation.

Generic unsupported messages are not retained as defense in depth. A violated
construction invariant is an internal compiler error carrying the checked form,
instance, and source origin needed to debug its producer.

## Implementation order

Work lands in dependency order:

```text
0. regenerate the stable executable inventory and add its repository gate
1. introduce typed compile-failure categories
2. publish checked value-use, writable-place, and capture facts
3. deepen places and definite initialization
4. finish value-operation and evidence transport totality
5. implement owning closure environments
6. finish pattern ownership and runtime projection
7. implement general globals and structured linking
8. route ambient core effects through the handler stack
9. remove exhaustive fallbacks and demote proven invariants to ICEs
```

Trusted inline IR is not a pending backend wave; its checked lowering is already
exhaustive. Its parser-only operands remain a frontend language-design question.

Each wave is driven by inventory fixtures and removes its identified sites in
the same change. A wave may not replace an unsupported branch with a broader
fallback, a generic frontend `Unsupported` diagnostic, or an untyped
`BackendError::new` path.

Places and runtime value operations are shared foundations. Closure
environments, patterns, globals, and effects reuse their projection, evidence,
retain, and destruction conventions rather than creating parallel modules.

## Validation

Every implemented family requires black-box tests through the public backend
interface. Tests cover, where applicable:

- frontend diagnostics without invoking backend semantic reconstruction;
- `talk check` and `talk run` agreement for MIR ownership diagnostics;
- concrete and generic values;
- direct and indirect calls;
- local, cell, global, and imported storage;
- normal return, early return, loop exit, handler resume, and discontinue;
- exact allocation, object, cell, closure-environment, and host-resource
  balance;
- no duplicate destruction or use after move;
- source and linked module suppliers; and
- bytecode encode, decode, validation, and execution for new target forms.

The existing parity programs, Core and stdlib suites, `talk-syntax`, package
execution, REPL, C and Swift embedding, and browser embedding remain regression
surfaces.

The final gate requires:

1. every stable inventory identifier has a reviewed disposition and fixture;
2. source identifiers and inventory identifiers match exactly;
3. no `BackendError::unsupported` constructor or call remains;
4. no former site survives as an unstructured error or generic capability
   diagnostic;
5. checked declarations, expressions, patterns, calls, captures, effects, and
   inline-IR operations are exhaustively accounted for;
6. malformed source fails in its owning frontend module;
7. CFG-sensitive ownership failures use structured MIR diagnostics;
8. missing external supply fails through structured linking;
9. violated typed facts produce internal compiler errors; and
10. all resource-balance fences pass.

## Relationship to earlier decisions

This ADR preserves ADR 0034's deep backend interface, private implementation
phases, trust policy, bytecode reference target, and prohibition on a second
evaluator.

It adopts ADR 0038's semantic ownership table. `TypedProgram` is the complete
frontend seam; specialization is the only backend type-resolution operation;
MIR does not become a second type checker.

It preserves the ownership, deterministic-cleanup, generic-evidence, and
one-shot-effect semantics retained by ADRs 0032 and 0034, as amended by the
implicit-sharing decision in `docs/ownership.md`.

It supersedes blanket implementation restrictions in the parity ledger only
where this ADR supplies executable behavior: owning captures, generic capturing
local functions, uninitialized bindings with definite-assignment analysis,
general globals, and user handling of typed ambient core effects. Invalid
instances remain ordinary source, ownership, initialization, unsafe, or linking
errors under named rules.

## Size accounting

ADR 0038 performed the architecture review required after crossing ADR 0034's
13,400-line trigger and removed substantial duplicated MIR responsibility. The
current size report remains above that budget. This ADR does not silently widen
it.

Before a large runtime wave expands production code, the project must record
either a revised reviewed budget or an accepted burn-down target. Every wave
continues to report backend, runtime, frontend-seam, test, and documentation
lines separately. Growth stops if a wave duplicates places, value operations,
dictionaries, checked semantic facts, or lifecycle rules.

## Consequences

- Backend completeness becomes an invariant over checked, linked programs.
- Source semantics remain local to the frontend; MIR gains no fallback semantic
  authority while capabilities are implemented.
- The remaining backend work is narrower than before ADR 0038: runtime places,
  evidence transport, closure lifecycle, ownership settlement, global storage,
  linking, and handler routing.
- Structured error categories make unsupported behavior harder to hide by
  renaming a constructor.
- The inventory survives refactoring because stable identifiers and fixtures,
  not line numbers, define it.
- New source features must publish complete checked facts and add executable
  lowering in the same change, or define a stable frontend rejection. An
  open-ended capability diagnostic in either frontend or backend is contrary to
  this decision.
