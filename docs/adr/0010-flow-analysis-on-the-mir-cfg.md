# 0010 — Flow analysis runs on the MIR CFG

Status: superseded by ADR 0031 (2026-07-13)

## Context

The flow checker (`src/flow`) is a tree walk over the HIR. Control flow is
approximated by one scalar, `Diverges::{No, Yes}`: a branch that ends in
`return`, `break`, or `continue` is "diverging" and its state is discarded
at the `if`/`match` join. That is correct for `return` (the state exits the
function) and unsound for `break`/`continue`, whose states flow to the
enclosing loop's exit or head — join points a tree walk cannot represent.
Two confirmed bugs fall out directly:

1. A value moved on a conditional path ending in `continue` is forgotten;
   the loop's second walk re-enters believing it live → runtime double
   free (accepted program, memory unsafety).
2. Early-exit drop scheduling cannot be target-relative — the scope stack
   has no marker for "the loop starts here" — so `break`/`continue`
   schedule drops for *every* enclosing scope, exactly like `return`.
   Observable: a `'linear` value declared before `loop { break }` and
   consumed after it is rejected. Lowering compensates by ignoring
   break-path drop candidates entirely (re-deriving from its own drop
   stack), which currently *leaks* loop-locals instead — the same fact
   computed twice, disagreeing.

A related earlier finding (false `UseAfterMove` when a value moved before
a branch is reassigned in every branch) is the same join logic erring in
the conservative direction.

The compiler already builds the structure that makes all of this trivial —
the MIR CFG (`src/lower/mir.rs`), with blocks, `Branch`/`Switch`/`Loop`
terminators and scope statements — but builds it *after* flow runs,
because MIR consumes flow's HIR annotations. The analysis that needs a CFG
runs on the representation without one.

## Decision

Reorder the pipeline and move the flow checker onto the MIR CFG:

```
types → HIR → MIR (structural, per body, built once) → flow (CFG dataflow,
annotates MIR in place) → lowering (consumes annotated MIR)
```

- **MIR builds before flow, with no flow inputs.** Drop candidates are
  placed structurally: scope-exit candidates per scope local (as today),
  early-exit candidates covering exactly the scopes between the jump and
  its target (the builder has `scope_stack` and `loop_stack`; a frame
  gains a loop marker). Elaborations start empty.
- **Flow is a forward dataflow analysis over blocks.** A worklist iterates
  to a fixed point; `MoveState` joins at block entry from all predecessor
  exits. `break`/`continue`/`return` are edges, not a bit: their states
  reach the loop exit / loop head / function exit through the CFG. The
  per-statement transfer functions (the expression walkers, `seed_params`,
  the loan machinery) are reused; only the statement/control layer is
  replaced.
- **Annotations live on the MIR.** `LocatedStatement.ownership` (already
  present) carries drop elaborations and move sets; consume/auto-clone
  flags are written onto the statement-embedded expressions. The
  flow→HIR annotation pass and the NodeID-keyed side maps it feeds
  disappear (per the annotated-tree rule, with MIR as the annotated tree
  for everything at or below statement granularity).

## Stages (suite green after each)

1. **Control-flow-complete MIR.** Expression-position `if`/`match` today
   lower linearly into the current block (`lower_expr` walks both arms —
   no `Branch`); only statement-position control flow builds blocks. The
   builder is upgraded so *every* control-flow construct materializes
   blocks and a join, with the construct's value delivered through the
   join (statement-ification). Without this, a `break` inside an
   argument-position `if` is invisible to the CFG.
2. **MIR builds pre-flow.** Remove flow inputs from the builder;
   structural, target-relative drop-candidate placement (fixes bug 2's
   scheduling); the driver builds and stores one `Body` per checkable
   body (functions, inits, closures, file top level); lowering consumes
   the stored bodies (the existing `mir_bodies` cache becomes the store).
3. **Flow on the CFG.** Worklist fixpoint over blocks; joins at merge
   points (fixes bug 1 and the false-UseAfterMove); loans/liveness keyed
   by (block, statement) positions; drop candidates classified
   (Static/Dead/Conditional/Open) from maybe-initialized state at their
   program point; lowering's compensations (stack-derived break drops)
   deleted — the candidates become the single authority.
4. **One annotation home.** Delete the HIR statement walk, the
   flow→HIR `Annotator`, and HIR-side drop annotations; `FlowFacts` for
   the editor is produced from the MIR walk.

## Citations

- **Analyses on a CFG, not an AST.** Rust's MIR RFC motivates the move
  verbatim for our situation: "Reasoning about fine-grained control-flow
  in an AST is rather difficult. The right tool for this job is a
  control-flow graph (CFG)" — [RFC 1211: MIR](https://rust-lang.github.io/rfcs/1211-mir.html).
  Rust's AST borrow checker was subsequently replaced by the MIR borrow
  checker ([rust-lang/rust#52083](https://github.com/rust-lang/rust/pull/52083),
  [#95565](https://github.com/rust-lang/rust/pull/95565)).
- **Loans via fixed-point dataflow over the CFG.**
  [RFC 2094: non-lexical lifetimes](https://rust-lang.github.io/rfcs/2094-nll.html)
  computes in-scope loans at each CFG point by fixed-point dataflow; NLL
  is defined in terms of the MIR CFG, not source structure.
- **Drop elaboration as MIR dataflow.** rustc places drop terminators
  structurally during MIR building, then refines them with
  maybe-initialized dataflow and drop flags —
  [rustc dev guide: drop elaboration](https://rustc-dev-guide.rust-lang.org/mir/drop-elaboration.html),
  [rustc dev guide: MIR dataflow](https://github.com/rust-lang/rustc-dev-guide/blob/master/src/mir/dataflow.md).
  Our Static/Dead/Conditional/Open elaborations are the same scheme;
  stage 2's "place structurally, classify by dataflow" mirrors it.

## Departures from precedent (deliberate)

- **No three-address flattening.** rustc's MIR flattens expressions into
  rvalues over temporaries. We keep straight-line HIR expression trees
  embedded in statements as the lowering payload; only *control flow* is
  required to be block-level (stage 1). Full flattening is the core-IR
  elaboration plan's territory, not this change. Consequence: transfer
  functions still walk expression trees, but never across a control-flow
  boundary.
- **Structured fixpoint, not region inference.** NLL infers region
  variables; our loans keep the existing place/permission model — only
  their propagation moves to the CFG.
