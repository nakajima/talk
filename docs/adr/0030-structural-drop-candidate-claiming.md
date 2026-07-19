# 0030 — Structural drop-candidate claiming

Status: superseded by ADR 0031 (2026-07-13)

## Implementation notes

`mir::build_checked` keeps `Body` and `Statement::DropCandidate` private to
MIR construction and flow. After flow records elaborations, one claiming pass
builds a distinct `CheckedBody`:

- scope-exit drops attach to `StorageDead` or the exiting value/terminator;
- assignment-replacement drops attach to `Assign`;
- symbol-rooted unwind drops attach to `Call`/`Perform`;
- temporary-end drops become explicit checked drop statements;
- a whole-CFG planner uses those normal temp drops as obligation templates,
  attaching matching temp actions to every suspension and function-exit edge;
- flow-only reads, scope markers, and unelaborated scalar candidates do not
  cross the seam.

The candidate pass rejects an unclaimed or multiply claimed structural
candidate. The CFG planner then verifies static temp identities and exact
normal/unwind path balance, including temps live across match/value-block
scaffolds that are not visible in a local builder stack. Every named place and
temp receives one initialization-order key; unwind actions sort by that shared
key rather than grouping by storage class. Flow records temp ownership changes
at their exact checked statement/terminator, avoiding whole-body disposition
leaks across earlier suspension points. Generic object possibility remains an
explicit conditional cleanup action until specialization. Lowering consumes
only `CheckedBody`; the positional scans, look-behind helpers, and post-return
call-temp release heuristic are deleted.

## Context

Flow-elaborated `DropCandidate` statements are freestanding MIR
statements, and every consumer finds its candidates positionally:

- `lower_mir_storage_dead` / `storage_dead_drop_elaboration` look back
  exactly one statement for the paired `ScopeExit`/`EarlyExit` candidate;
  `assignment_drop_elaboration` looks back one for `AssignmentReplace`.
- `following_drop_candidates` / `unwind_drop_candidates` scan the run of
  statements after a `ReturnValue`/`Call`/`Perform`, ending at the first
  non-matching statement (`drop_candidates_following` is the shared walk).
- `unclaimed_scope_exit_drops` treats a candidate as claimed iff the very
  next statement is a `StorageDead` for the same symbol;
  `trailing_early_exit_drops` scans the trailing run before a terminator.

Nothing asserts these adjacency invariants at build time. A builder
change that interposes a statement between a candidate and its consumer
fails toward a leak: the storage-dead path emits a diagnostic
(`debug_assert` + "no elaborated drop candidate"), but the cursor scans
silently end the run and drop candidates from the returned list.

Two mitigations exist today:

- The free-balance verifier (ADR 0017, on by default in `cfg(test)` at
  `Driver::lower`) turns any silently-unclaimed candidate into a loud
  per-path Leak/DoubleFree failure on every test program that compiles
  the affected shape. Claiming drift is therefore fenced end-to-end, but
  only for shapes the test corpus exercises.
- The scans share one parameterized walk, so the matching rules can no
  longer drift apart between consumers.

## Decision

Attach candidate lists to their consumers structurally at MIR build,
and delete the positional scans:

- `StorageDead` carries its (at most one) paired candidate.
- `Call` / `Perform` carry their `Unwind` candidate list.
- `Terminator::Return` (and the break/continue jump statements) carry
  their exit-drop candidate lists; `Assign` carries its
  `AssignmentReplace` candidate.

The claiming question then never arises: consumers read their own
candidates directly, and an interposed statement cannot detach a
candidate from its consumer by construction.

## Prior art

rustc's MIR makes drops **terminators**, not statements: `Drop` (and
formerly `DropAndReplace`) terminate a block and carry their `place`,
success target, and `unwind` action as fields — cleanup is attached to
the consuming control-flow edge, and unwind paths are explicit edges
into cleanup blocks, so nothing is ever matched up by statement
adjacency. Drop elaboration (`rustc_mir_transform::elaborate_drops`)
rewrites those terminators in place using dataflow results, which is
the same publish-then-elaborate split our flow pass performs. The
proposal is the moral equivalent for this codebase's
statements-plus-annotations MIR.

## Why this is an ADR and not a cleanup

Flow keys per-point elaborations on statement identity: candidates are
transferred, recorded, and annotated as statements by the CFG engine
(`ownership.drop`), simulated by the balance verifier, and read back by
lowering. Moving candidates into consumer fields moves all of that:
every builder emission site, the flow engine's statement walk (each
embedded candidate needs its own elaboration slot), `mir_annotate`, the
balance verifier, and the lowering readers change together — several
hundred lines through the drop-authority spine, and per-candidate
annotation storage is a data-model decision (ADR 0015's
"typing publishes, lowering reads" shape extended to per-field slots).

## Alternatives considered

- **Status quo + balance fence** (current): sound, loud on exercised
  shapes; fragility remains for untested shapes and every new consumer
  must re-learn the adjacency rules.
- **Build-time adjacency verifier**: a `cfg(test)` MIR pass asserting
  every candidate is claimed under the positional rules. Cheap (~60-80
  lines) but redundant with the balance fence on exercised shapes, and
  it re-states the very protocol the structural fix deletes — kept out
  per the no-smearing rule.
- **Self-lowering candidates** (drop at the candidate's own position):
  works for the storage-dead pairing but not for returns/unwinds, where
  the drop chain must be spliced into a continuation or entry lambda
  after the value is evaluated.

## Resolved questions

1. Candidates become `CheckedDrop` values with their elaboration embedded;
   consumers own an optional drop or an ordered vector as appropriate.
2. `ScopeExit`, `StorageLive`, reads, and other flow bookkeeping remain in
   private structural MIR but are absent from `CheckedBody`.
3. The migration was a single cutover: flow continued annotating structural
   candidates internally, then all lowering readers moved to claimed checked
   operations before the positional scans were removed.
