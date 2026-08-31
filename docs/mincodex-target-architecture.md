# Mincodex target architecture

Status: approved design reference

This document defines the destination recovered from the `mincodex` branch. It
is intentionally not an implementation plan. Ordered implementation tickets,
current-tree owners, gates, and status live in
[`mincodex-salvage-plan.md`](mincodex-salvage-plan.md).

## Compiler pipeline

```text
Talk source
    -> parse, expansion, and name resolution
    -> type checking and finalization
    -> Core<Nested>
    -> Core<Flat>       (pattern decisions realized)
    -> Core<Closed>     (closure environments explicit)
    -> Core<Mono>       (all executable instances sealed)
    -> MIR lowering     (no typing or specialization decisions)
    -> CFG ownership placement
    -> finalized MIR
    -> existing target adapters
```

## Semantic owners

- `patterns` owns exhaustiveness, unreachable-arm reporting, and match decision
  trees through one matrix recursion.
- `Core` owns every per-occurrence semantic decision required downstream.
- `MonoPlanner` owns executable reachability and specialization closure.
- MIR lowering realizes `Core<Mono>` and cannot demand or infer instances.
- `Cfg`, liveness, and `OwnershipPlacement` own flow-derived ownership.
- The balance verifier proves finalized MIR in debug builds; it is not a second
  planner.
- `Semantics` owns shared editor queries over syntax and checked facts.
- The syntax package owns formatting and highlight classification.
- The artifact image module owns stable cross-session identity and wire
  determinism.
- The VM retains the bytecode interface while adopting independent hot-path
  improvements.

## Core phases

### Core<Nested>

Type finalization emits this phase once. It contains checked nested functions,
typed binders and expressions, checked match matrices, and mandatory semantic
operations. Clean-file editor facts are derived from it. Blocked files receive
partial `NodeFacts` from finalization.

### Core<Flat>

The pattern module's decision product has become explicit control structure.
No later phase performs usefulness analysis or chooses match strategy.

### Core<Closed>

Nested functions and handlers carry exact value and witness environments in
deterministic order. Construction and prologue read the same environment
product.

### Core<Mono>

The phase owns executable roots, a deterministic callable arena, handlers,
static-effect instances, derived bodies, concrete call edges, explicit witness
arguments, constructor arguments, and graded operands. Its lint proves
transitive closure.

## Mandatory Core operations

Semantic operations are ordinary mandatory nodes, not optional decision side
fields. Core represents:

- selected methods and initializers;
- type application evidence;
- existential pack evidence;
- explicit and implicit clone operations;
- witness arguments;
- concrete instance edges in `Core<Mono>`;
- concrete constructor and effect instantiations;
- match decision products;
- consume, borrow, and copy operand modes.

`NodeID` remains source identity and editor lookup only. Semantic call edges
live on occurrences because synthesized wrappers and inner nodes may share a
source id.

## Pattern decisions

The pattern module accepts a checked matrix, scrutinee types, source arm
identity, and catalog queries. It returns:

```text
PatternResult {
    tree: DecisionTree,
    report: MatchReport,
}
```

One recursion produces both values. It handles enums, GADTs, tuples, records,
structs, literals, binders, wildcards, or-patterns, guards, borrowed
scrutinees, reference-carrying payloads, labels, duplicate binders, missing
cases, and unreachable arms. Projection provenance and binding ownership are
explicit.

## MIR and ownership

Every local MIR operand is consume, borrow, or copy. MIR also publishes
explicit definitions, replacements, borrow boundaries, spends, and drops where
source order matters.

One `Cfg` provides stable indexing, normal and unwind successors, predecessor
edge positions, forward traversal, and backward bitset traversal to every
consumer.

One backward liveness computes:

- source-use liveness for donation, exclusivity, and displacement;
- any-use liveness for release placement;
- projection provenance and view birth points.

One forward `OwnershipPlacement` computes initializedness, moves,
replacements, loans, non-lexical loan death, retains, displaced values,
first-dead releases, unwind-live sets, writeback obligations, and joins.
Lowering publishes operations but never merges ownership state.

## Editor semantics

One `Semantics` module owns document lookup, position ancestry, node extent,
symbol declarations, occurrences, checked node types, member resolution,
source-callable lookup, and signature rendering. Ordinary editor analysis ends
at checked Core. Explicit CLI checking retains backend diagnostics.

## Deterministic artifacts

Serialized hash containers use canonical wire order. Durable symbols use
stable module identity, never session module integers. Core, library, and
workspace products use one framed image format with dependency interface
fingerprints. Stale, malformed, and trailing data fail closed.

## VM destination

- Flat aggregate storage is `Rc<[Value]>`.
- Unique in-place field writes call `Rc::make_mut` without first cloning the
  `Rc`.
- Distinct-destination writes preserve the source.
- Aggregate construction avoids an unnecessary intermediate vector.
- Allocation lookup has a provenance-aware one-entry bounds cache.

## Formatting and highlighting

Talk code in `packages/syntax` owns document layout, formatting policy,
comment attachment, precedence, syntax coverage, and highlight
classification. Rust owns transport, ABI validation, DTO conversion, and
presentation rendering only.

## Scope exclusions

This architecture does not:

- replace bytecode with executable MIR;
- make `talk-vm` depend on `talk-mir`;
- import native stack segments or unified suspend runtime work;
- import record-row, overload, or effect-annotation language changes;
- require the complete flat syntax arena migration;
- add third-party dependencies.

Generated bootstrap artifacts and MIR goldens are regenerated from resulting
source. They are never copied from the quarry.

## Source quarry

The quarry is evidence, not a patch series.

| Commit | Relevant evidence |
| --- | --- |
| `29b9e79b` | Pattern decisions, initial CFG and ownership work, typed program move |
| `e2a151d5` | Formatter, highlighter, frontend schema |
| `c27a327c` | Expansion and desugaring behavior informing Core emission |
| `309fdfd6` | Ownership action publication and replay |
| `71a4eb44` | Typed tree to Core transition |
| `716b9d81` | Core and MIR lowering restructuring |
| `e99fb801` | Formatter/highlighter integration and ownership regressions |
| `16cc0c7f` | MIR validation and VM changes; direct-MIR VM is excluded |
| `03091232` | Flat syntax and formatter integration details |
| `51cf0739` | Narrow generated frontend ABI views |
| `d3ea4662` | Final Core, ownership, semantics, images, VM optimizations, tests |
| `a2ff7f1f` | Generic-global mutable writeback regression |
