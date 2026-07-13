# 0030 — Structural drop-candidate claiming

Status: proposed (2026-07-12); not yet reviewed

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

## Decision (proposed)

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

## Open questions

1. Per-candidate elaboration storage: a `Vec` of slots on the consumer
   mirroring the candidate list, or candidates as small structs with
   their own `ownership` payloads embedded in the consumer.
2. Whether `ScopeExit`/`StorageLive` bookkeeping statements retain any
   role once exits carry their own lists.
3. Migration order: builder emission first (dual-publish), flow second,
   lowering readers last — or a single cutover.
