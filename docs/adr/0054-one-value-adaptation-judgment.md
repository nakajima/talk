# ADR 0054: One value-adaptation judgment

Status: DRAFT (challenge me)

## The disease

"How does a value of type F cross into a slot of type E?" is decided today at
(at least) eight independent typing sites and realized at several independent
lowering sites, each with locally-different rules, evidence, and diagnostics:

| site | judgment it re-implements |
|---|---|
| `solve/mod.rs` borrow→owned path (~:560) | donate on Return/Body; Copy = free copy; CheapClone = retain (records `coerce_clones`); else error |
| `unify.rs push_apply_param_eq` | auto-borrow at immediate application |
| `unify.rs push_borrow_downgrade_eq` | covariant return downgrade (`&mut` → `&`) |
| `member.rs push_immediate_argument_eq` | receiver borrow-matching for requirement binding |
| `finalize.rs check_pack_payload_ownership` | pack payloads — self-described as "the deferred **twin** of solve_coerce_owned's tier-2 rule" |
| `finalize.rs copy_marker_coerces` | `copy` marker evidence — a third copy of the coerce-kind tiers |
| `ty.rs match_pattern` (peel_pattern_borrows) | borrow erasure in witness matching (ADR 0014) |
| `catalog.rs canonical_conformance_arg` | Copy-inline borrow collapse for conformance args |

And in MIR: `consume_call_argument_into` + `coerce_clones` reads + donation
realization, invoked separately from each call-lowering path (direct,
committed-witness, deferred-witness, derived-glue, indirect).

This scatter breeds exactly the bug class ADR 0053 just eliminated for
catalog state, with worse consequences because adaptation is
memory-safety-bearing:

- The 2026-08-09 **Identity-glue double free**: the derived-dispatch path
  skipped the consume transfer every other call path performs. A missed
  adaptation is a double free or a leak, not a type error.
- The **Copy borrow-erasure layout bug** (fixed 2026-08-02): adaptation
  semantics (`&T`/`T` Copy equivalence) leaking into layout identity because
  the collapse rule lives in a catalog helper some classifiers consulted and
  others didn't.
- The **`T` vs `&T` diagnostic** on consuming rigid params: correct
  rejection, incomprehensible rendering, because the failing site is a bare
  `Eq` that never knew it was an adaptation question ("this call must own
  the value; `&T` can't donate because T isn't known Copy/CheapClone — add
  `consume` or clone" is the answer the user needed).
- Two of the eight sites are *documented copies* of a third — divergence
  maintained by comment.

## The cure

**One judgment, one evidence table, one realizer.**

1. **The judgment.** One solver function decides every crossing:

   `adapt(found, expected, site) → Adaptation | Deferred | Error`

   where `Adaptation` is a small closed enum: `Identity`, `Borrow` (auto-
   borrow), `Downgrade` (`&mut`→`&`), `Donate` (borrow fills owned slot:
   `Copy` tier = free copy, `CheapClone` tier = retain), `Consume`
   (ownership transfer into the callee/slot). `site` carries only what
   changes the rule today: application vs nested position (ApplyBorrow's
   distinction), return vs argument, marker (`copy`) vs implicit, pack
   payload. The existing `CoerceOwned`/`ApplyBorrow` constraints collapse
   into `Eq`-with-site; the per-site helpers become calls into the one
   judgment.

2. **The evidence.** Typing publishes the chosen `Adaptation` per node in one
   artifact table — the generalization of today's `coerce_clones` (which
   records only the CheapClone tier). "Typing publishes, lowering reads"
   (ADR 0015/0038) applied to adaptation: MIR stops re-deriving *any*
   crossing decision.

3. **The realizer.** One MIR helper — `realize_adaptation(operand, node)` —
   consulted by every call-lowering path and every slot store. The
   Identity-double-free class becomes unrepresentable: a path that lowers a
   crossing without consulting the table doesn't compile against the new
   seam, rather than silently skipping a transfer.

4. **One diagnostic.** A failed adaptation renders as an adaptation error
   ("this position needs an owned `T`; the borrowed argument can't donate
   because `T` has no Copy/CheapClone evidence — declare the parameter
   `consume`, or clone at the call") instead of eight flavors of type
   mismatch.

## What this deletes

- `check_pack_payload_ownership` and `copy_marker_coerces` (finalize) — both
  become reads of the published table; the twin-maintenance comment dies.
- The inline coerce-tier logic in `solve/mod.rs`'s borrow→owned path, and
  the `CoerceOwned`/`ApplyBorrow` constraint variants plus their solver
  arms (folded into `Eq` + site).
- The borrow-peel special cases in `push_apply_param_eq` /
  `push_borrow_downgrade_eq` / `push_immediate_argument_eq` (each becomes a
  one-line judgment call).
- Per-call-path `consume_call_argument_into` invocations in MIR (five call
  paths → one realizer), including the Derived-branch special case added for
  the double-free fix — the fix generalizes instead of surviving as a spot
  patch.
- Longer-term (explicitly out of v1 scope): `canonical_conformance_arg` and
  the match_pattern borrow-peel could read the same equivalence the judgment
  defines, closing the layout-identity seam — deferred until the judgment is
  proven in the value path.

## What stays

- The ownership *checker* (MIR flow analysis, drop/move results per point,
  the balance verifier) — this ADR unifies the *decision and realization* of
  crossings, not the soundness analysis that audits them.
- `CoerceKind` and its catalog queries — they become the judgment's Donate
  tier lookup, called from one place.
- ADR 0018 borrow-by-default parameter semantics — unchanged rules, one
  implementation.

## Stages (each lands green; no stop-and-decide points)

1. **Introduce the judgment + table** behind the existing behavior: implement
   `adapt` and the artifact table; port the borrow→owned solver path and
   `coerce_clones` onto it (pure refactor, differential-tested).
2. **Port the Eq-adjacent helpers** (`push_apply_param_eq`,
   `push_borrow_downgrade_eq`, `push_immediate_argument_eq`) — delete
   `ApplyBorrow`/`CoerceOwned` constraints when their last emitters die.
3. **Port finalize** — pack payloads and copy markers read the table;
   delete both twins.
4. **One realizer in MIR** — all call paths + slot stores consult it; the
   Derived-branch patch and its test generalize (the double-free test
   becomes the realizer's contract test, extended to every derived recipe
   and heap-built values).
5. **One diagnostic** — adaptation failures render uniformly; re-pin the
   handful of expected-message tests (the `T` vs `&T` messages get better,
   deliberately).

## Risks, resolved in advance

- **Hot path**: `adapt` sits inside unification. It replaces logic already
  inline there, adds none; stage 1 is differential-tested against the pinned
  bench outputs (both backends) like ADR 0045 was.
- **Memory safety**: every stage runs the corpus with the balance verifier
  and the differential debug+release suites; the stage-4 contract test
  routes heap-built strings through every adaptation kind (the lesson from
  the Identity bug: literals and Copy scalars prove nothing).
- **Diagnostic churn**: message re-pins are contained to stage 5 and are
  strict improvements; no semantics change.

## Relation to ADR 0053

Same principle, next axis: 0053 removed hand-reconciled *copies of facts*;
0054 removes hand-reconciled *copies of a judgment*. Both replace "N sites
that must agree" with "one site that cannot disagree with itself".
