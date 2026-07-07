# 0019 - Type checking returns TypedProgram; lowering consumes CheckedMir

Status: accepted (2026-07-05)

## Context

ADR 0010 moved ownership analysis onto the MIR CFG, and ADR 0015 made the
checker publish facts lowering must not recompute. The current compiler still
violates the spirit of both decisions because ownership and typing facts are
copied through several shallow representations:

```text
resolved AST + TypeOutput
-> HIR copy with baked type facts
-> MIR with embedded HIR expression copies
-> flow side maps / HIR annotations / MIR annotations
-> lowering re-derives some ownership effects
```

The result is a side-table disagreement problem. A fact can be correct in one
place and stale or missing in another.

Confirmed examples:

1. A `consuming` method receiver in a branch (`s.green()`) moved the receiver
   in flow, but `mir_annotate::statement_moves` did not rediscover that move
   from the callee syntax. Lowering therefore did not clear the caller-side
   drop flag, and the VM double-freed the string buffer.
2. Impure `if` / `loop` conditions can be evaluated twice: the MIR builder
   lowers the condition into statements, but the terminator still stores the
   original expression and lowering lowers it again.
3. `Switch` / `match` scrutinee consumption is a terminator effect in flow,
   while lowering clears drop flags from statement move sets. Owned enum
   payload extraction in a conditional match can therefore double-free.
4. Wildcard payloads in owned enum matches can be consumed without a binder
   owning the payload drop. Payload ownership is currently split between
   pattern lowering and flow.

The proposed verifier in ADR 0017 would catch many of these bugs before the VM
runs, but the stronger fix is architectural: make disagreement impossible by
removing the duplicate representations and side-table compiler interface.

## Decision

Replace the public post-checking interface with two deep modules:

```text
typecheck(resolved AST) -> TypedProgram
mir::build_checked(&TypedProgram) -> (CheckedMir, FlowFacts)
lower(&TypedProgram, &CheckedMir) -> LoweredProgram
```

There is no HIR compiler phase. There is no public structural MIR. There is no
ownership side table consumed by compilation after `build_checked`.

### 1. The type checker returns `TypedProgram`

`TypeOutput` stops being the public compiler interface. It may survive as an
internal implementation detail while checking, but later compiler modules see a
`TypedProgram`.

`TypedProgram` owns a typed tree whose expression and pattern nodes expose
semantic facts directly:

- the checked type;
- member resolution;
- instantiation;
- existential pack/coercion information;
- semantic expression kind.

The semantic expression kind includes the rewrites HIR currently performs:

- `Member` resolved to a stored field becomes `Proj`;
- variant construction becomes `Con`;
- erased wrappers (`as`, single-element tuple parentheses) are represented by
  the inner value with the outer node's typed facts;
- record literal canonicalization is explicit;
- clone coercions are explicit.

Program-wide facts such as catalog entries, schemes, exports, and display names
remain available through `TypedProgram` methods. Callers do not index raw
`NodeID` maps to reconstruct expression meaning.

### 2. HIR is deleted from the compiler pipeline

The compiler driver no longer builds `hir::HirFile` after type checking.

The following HIR-era mechanisms are removed from compilation:

- `src/hir/build.rs` as a compiler phase;
- `Driver<Typed>::hir`;
- `Block::drops` and `Stmt::drops` as compiler inputs;
- `ExprOwnership` as a mutable compiler annotation;
- build-on-miss MIR fallback from HIR blocks.

Source-faithful ASTs may remain for LSP/editor features. They are not the
compiler artifact after checking.

### 3. `mir::build_checked` is the only MIR seam

The `mir` module owns its internal structural CFG representation privately.
`build_checked` performs all of these steps behind one interface:

1. build structural MIR from `TypedProgram`;
2. run CFG flow analysis;
3. rewrite structural MIR into `CheckedMir`;
4. return editor-facing `FlowFacts` derived from the checked result.

No compiler caller can access the half-checked structural MIR. `FlowFacts` is
for diagnostics/LSP only; no later compiler phase reads it.

### 4. `CheckedMir` is ownership-explicit

Lowering does not receive candidates plus annotations. It receives executable
ownership operations.

The lowering input does not contain:

- `DropCandidate` with optional elaboration;
- `statement.ownership.moves`;
- HIR `expr.ownership.consumes` flags;
- side maps keyed by `NodeID`;
- arbitrary HIR expressions in terminators.

Instead `CheckedMir` uses explicit operation shapes, for example:

```rust
Arg::Borrow(Operand)
Arg::Move { operand: Operand, place: Place }
Arg::Copy(Operand)
Arg::Retain { operand: Operand, ty: Ty }

Statement::Drop { operand: Operand, ty: Ty }
Statement::DropIfLive { flag: DropFlag, operand: Operand, ty: Ty }
Statement::SetDropFlag { flag: DropFlag, live: bool }
Statement::Call { callee: Callable, args: Vec<Arg>, result: Option<Temp> }

Terminator::Branch { condition: Operand, then_block: BlockId, else_block: BlockId }
Terminator::Switch { scrutinee: Operand, arms: Vec<SwitchArm> }
```

The exact Rust names can differ, but the invariant cannot: ownership transfer,
retain, drop, and drop-flag operations are explicit MIR instructions. Lowering
translates them mechanically.

### 5. Terminators contain operands, not impure expressions

Structural MIR building must flatten terminator inputs. `Branch.condition`,
`Loop.condition`, and `Switch.scrutinee` in `CheckedMir` are operands/temps
whose evaluation already appears in statements.

This removes the class where lowering evaluates a condition or scrutinee a
second time.

### 6. Match payload ownership is explicit in `CheckedMir`

Owned `switch` / `match` does not rely on pattern lowering to decide payload
ownership.

For each arm, `CheckedMir` explicitly represents ownership of every owned
payload:

- bound payload moved to a binder;
- borrowed payload reborrowed;
- wildcard payload dropped by a hidden checked MIR operation;
- payload retained when a clone coercion requires it.

The outer scrutinee drop is not used as an implicit fallback for payloads that
were already extracted.

### 7. Lowering accepts only `CheckedMir`

Lowering's public interface is:

```rust
pub fn lower(program: &TypedProgram, mir: &CheckedMir) -> LoweredProgram
```

Lowering is not allowed to:

- inspect AST/HIR ownership flags;
- derive moves from expression syntax;
- classify drops;
- maintain an ownership `drop_stack`;
- synthesize scope drops;
- lower structural MIR.

If lowering needs ownership information, it must be present as a `CheckedMir`
operation.

## Non-negotiable invariants

1. There is one compiler path from typed source to lowering.
2. There is one ownership representation after flow: `CheckedMir` operations.
3. Structural MIR is private to the `mir` module.
4. `FlowFacts` is not consumed by compilation.
5. Lowering cannot compile unless handed `CheckedMir`.
6. No compiler module after type checking reconstructs typed expression meaning
   from raw `NodeID` side maps.
7. No compiler module after `build_checked` reconstructs ownership effects from
   syntax.

## Cutover plan

These steps are one cutover branch. No step is mergeable if it preserves a
parallel compiler path.

1. Add the `TypedProgram` module and make `type_check` return it as the public
   checked artifact. Move HIR's semantic rewrites into typed expression and
   typed pattern construction.
2. Port MIR construction to read `TypedProgram` directly.
3. Make structural MIR private inside `mir`.
4. Move flow invocation inside `mir::build_checked`.
5. Change flow to rewrite structural MIR into `CheckedMir` with explicit
   ownership operations instead of annotations.
6. Port lowering to `CheckedMir` and remove lowering-side ownership analysis.
7. Delete the old compiler path in the same branch.

The branch is complete only when the old interfaces are gone and cannot be
called from compiler code.

## Required deletions in the cutover

- compiler use of `src/hir/build.rs`;
- `Driver<Typed>::hir`;
- `Driver<Typed>::mir_bodies` as a public structural/annotated body store;
- `flow::mir_annotate::statement_moves`;
- HIR `Block::drops` / `Stmt::drops` as compiler inputs;
- HIR `ExprOwnership` mutation as compiler input;
- `annotated_body` build-on-miss / HIR fallback annotation;
- lowering-owned `drop_stack` and ownership `drop_flags` analysis;
- lowering over `DropCandidate` elaborations;
- lowering over structural MIR;
- terminators carrying impure expressions.

## Regression tests required before merge

The cutover must include tests for these shapes:

1. a `consuming` method receiver used only on one branch does not double-free;
2. an impure `if` condition runs once;
3. an impure `loop` condition runs once per iteration;
4. owned enum payload extraction inside a conditional match does not double-free;
5. wildcard owned enum payloads in matches do not leak;
6. effect perform arguments that are source-consumed but runtime-retained by the
   performer preserve the ADR 0011 / flow-test behavior;
7. borrowed match scrutinees reborrow payloads and remain reusable;
8. generic ownership still follows the last-consume / earlier-retain rule.

## Consequences

- The type checker output becomes deeper: callers ask typed semantic questions
  instead of coordinating AST nodes with a bag of side tables.
- The MIR module becomes deeper: callers get checked executable ownership
  structure, not a structural CFG plus conventions.
- Lowering becomes smaller and more mechanical. Ownership bugs move to the MIR
  module, where structure and flow are local to one implementation.
- The cutover is larger than patching individual double frees, but it deletes
  the duplicate mechanisms that created the regressions.

## Relationship to earlier ADRs

- Extends ADR 0010 by completing the "one annotation home" intent as "no
  annotation home after checking; checked MIR operations are the home."
- Extends ADR 0015 by making checker-published facts a typed tree interface
  rather than a public side-map bag.
- Replaces ADR 0017's verifier-first mitigation with an architecture-first
  prevention strategy. A verifier can still be useful as defense in depth, but
  correctness does not rely on compiler phases comparing side tables.