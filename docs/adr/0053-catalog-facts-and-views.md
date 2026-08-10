# ADR 0053: One catalog per compilation

Status: IMPLEMENTED (all stages, 2026-08-09). History: v1 proposed layered
views — rejected: adds a layer over the duplication. v2 proposed the
one-table cure. v3 = v2 amended by a four-way code audit; corrections
marked **[audit]**. Implementation notes: stage 2's commitment landed at the
MIR assembly point (where the module set closes) rather than a separate
driver hook; per-module synthesis/commits remain for typing's own reads, the
backend pass is the once-over-everything authority. Export slices carry
amendment stubs for foreign protocols (own-added requirements appended after
the exporter's — the slot-prefix rule made structural); `param_bounds` and
`member_owners` travel whole (additions indistinguishable from imported
copies; insertion dedups). Pinned by: `sibling_conformance_rows_collide_at_collection`,
`multi_module_compiles_are_deterministic_in_process`,
`declared_reflexive_conformance_overrides_the_synthesized_twin`,
`module_slice_carries_private_facts_and_retroactive_rows`.

## The disease

The same logical information — a protocol's requirement table, a conformance
row, a param's bounds, a committed dictionary — exists in many catalogs per
compilation: each module's private copy (built by merging imports), each
module's export-carved interface, and MIR's independently re-merged union.
Every seam is a place for state to diverge; the 2026-08-09 bug sweep was
entirely seam bugs.

**[audit]** The audit found the duplication is worse than v2 claimed: the main
program's catalog already holds carved copies of every import, so MIR's union
computes N full slices plus O(N²) carved partial copies of the same facts,
value-deduped — and each stdlib cache entry re-serializes its imports' merged
facts inside its own `TypedProgram`. Exactly four whole-catalog `.clone()`s
exist in the tree (`generate/mod.rs:101`, `mir/build/mod.rs:1283`, `:1322`,
`finalize.rs:511`); all four die or become borrows under this ADR.

The copies are vestigial. Three facts make them unnecessary:

1. **Compilation is whole-program in practice.** One driver invocation
   compiles core, stdlib, and every package module, in dependency order, in
   one process. There is no on-disk module-image format on this branch — the
   only serialized artifacts are the `~/.cache/talk/*.bin` compile caches
   (bincoded `(Module, TypedProgram)`) and the bootstrap `frontend.tbc`,
   which contains **no catalog at all** (MIR/bytecode only; `frontend.abi` is
   rendered text derived from resolved names). **[audit]**
2. **Symbols are globally unique** (ADR 0038 absolute module identity), and
   provenance is already in the data: `Symbol::module_id()` covers every
   declaration kind and `ConformanceId` carries `module_id` — slice
   extraction needs zero new tracking. **[audit]**
3. **Privacy is enforced by accessibility checks at use sites** (ADR 0042).
   Carving is a second, redundant enforcement mechanism — the one that ate
   `Block: Into<String>`.

## The cure

**One `TypeCatalog` per compilation, owned by the driver, threaded through
every module's typecheck in dependency order.** A module's session writes its
facts into the one table; at its turn the table holds exactly core + its deps
+ itself — the correct worldview, because dependency order *is* the view.

Threading design **[audit]**: carry the shared table on `DriverConfig`
(mirroring the existing `modules: Rc<ModuleEnvironment>` idiom) — zero churn
at `Driver::type_check`'s ~34 call sites; 8 signatures change total
(7 changed + 1 new `TypeCatalog::insert_slice`, a plain per-table extend with
no dedup and no recommit, ~25 LOC replacing `merge`'s 114).

Consequences, each a deletion:

- **No import-merge.** `TypeCatalog::merge` and both dedup regimes die, with
  the by-head index repair, the `previous_head` bookkeeping, and the trailing
  per-merge recommit trio.
- **No export surgery.** `interface.rs` keeps ~115 of its 319 lines: slice
  filtering (`own(symbol)` — one line of today's file, the `member_visibility`
  retain, already has exactly this shape) plus serialization glue. The
  196-line reachability sweep, `local_private`, `kept_params`, and the
  "conclusion nameable" row gating die.
- **No synthesis dance.** `strip_synthesized_conformances`, its driver call
  site, and both conformance-id ceiling blocks die. Synthesis itself is
  idempotent per `(head, protocol)` against the one table.
- **No MIR union.** The merge loop, the post-merge recommit, the
  `struct_index`/`enum_index` maps (the one table's `structs`/`enums` *are*
  the index; the maps exist only to split lifetimes across owned copies), and
  three deep catalog clones per compile die. `Layouts` borrows the table.
- **One commitment** for the three lowering-facing indexes — `deinit_rows`,
  `dictionaries`, `callable_owners` — which the audit confirmed have **no
  typing-phase readers**. Eleven call sites become one.

**Slot stability by construction:** requirement tables grow append-only in
dependency order, so an exporter's slots are a prefix of the final table and
every module's compiled bodies index the slots the final commitment
publishes.

## Corrections from the audit (v2 → v3)

1. **Synthesis stays per-module, post-collect.** Module M's own body checks
   resolve `.show()`/`==`/`.into()` through rows for M's types, so derived +
   reflexive synthesis must run after M collects, before M's bodies check.
   "Once" survives as idempotence — whichever module first collects a head
   mints its rows; later modules skip. Only *commitment* moves.
2. **`commit_member_visibility` is not a commitment.** It is an insert-only
   per-module publish from that module's `ResolvedNames`, read throughout
   body checking (`solve/member.rs`). It stays at the per-module seam.
3. **"After the last module" = the backend boundary.** Stdlib modules
   activate on demand and `with_backend_inputs` is where the module set
   closes — commitment runs there, not at an arbitrary driver point. Until
   stage 4 lands, cache serialization also needs committed dictionaries
   (export reachability reads `row.dictionary`), so stage ordering is 4
   before-or-with 2, or commit-before-serialize is kept in the interim.
4. **`finalize.rs:510` is a stage-1 blocker.** The export zonk `mem::take`s
   the whole catalog and rewrites *imported* entries — harmless on a private
   copy, wrong on a shared table. It becomes an own-slice, in-place walk
   before threading lands (stage 0).
5. **The `use package::html` revert is wrong as written.** Local imports do
   two jobs: catalog merging (which this ADR obsoletes) and **file
   discovery** (which it does not — a package library compiles from one entry
   source; only import-reachable files are parsed). Either stage 4 adds
   package-wide source enumeration, or the revert is dropped and local
   imports remain as discovery directives. Decision for Pat.
6. **Conformance visibility falls out automatically** — the audit confirmed
   the solver has no per-module row filter anywhere; visibility today is
   purely "which catalogs got merged". Deleting the merge makes rows
   package-global with zero solver or resolver changes.
7. **Module-id stability graduates from nuisance to hazard.** Package ids are
   assigned by lock-file *position* (`package.rs:2328`); the cache key does
   not include module numbering. Under one table a stale slice mis-keys the
   whole compilation. Either key package ids off `StableModuleId`, or
   invalidate caches on any lock reorder. Cache `FORMAT_VERSION` bumps 1→2
   with the stage-4 payload change (standalone; no interaction with
   `bytecode::FORMAT_VERSION = 7` — answers v2 open question #3).
8. **LSP open question answered**: the analysis workspace already reads one
   merged table and enforces no per-module isolation; per-request sessions
   need only the slice-loading path (~10–20 LOC in `workspace.rs`).

## Semantic change: package-global conformances

With one table, a conformance is visible to every module in the compilation —
Rust's model: impls are in scope whenever the defining crate is in the build
([Implementations, The Rust Reference](https://doc.rust-lang.org/reference/items/implementations.html);
impls collected per crate, consulted globally under coherence:
[trait_impls_in_crate](https://doc.rust-lang.org/stable/nightly-rustc/rustc_middle/query/cached/fn.trait_impls_in_crate.html)).

Scope, DECIDED (no open questions remain in this ADR):

- **Conformance rows go global; inherent extend rows keep use-site
  ambiguity.** The existing test
  `overlapping_imported_inherent_rows_are_ambiguous_at_use` stays green
  unchanged — inherent dispatch already arbitrates. Rust's analog: inherent
  impls are orphan-restricted so the case can't arise; Talk's use-site rule
  is the moral equivalent.
- **Sibling packages included.** One table across `compile_graph` makes
  dependency libraries' conformances mutually visible. Any collision this
  surfaces in code we own (core, stdlib, test corpus) is fixed in the same
  stage by deleting the duplicate row — the resolution is predetermined, not
  a mid-flight decision. A cross-package orphan rule
  ([RFC 2451](https://rust-lang.github.io/rfcs/2451-re-rebalancing-coherence.html))
  is future work gated on packages actually shipping to third parties; it is
  not needed for anything this compilation model can build today.
- **Module-id stability: fold the numbering inputs into the cache key.** The
  lock file already carries a fingerprint; hashing it (plus the stdlib module
  list) into `cache.rs` keys makes any reorder invalidate caches by
  construction — two lines, hazard eliminated. Re-keying package ids off
  `StableModuleId` is orthogonal future work.
- **File discovery: local imports stay as discovery directives.** The
  `use package::html` revert is dropped from stage 4; imports keep their
  file-discovery job and simply stop having catalog-visibility consequences.
  Package-wide source enumeration is a separate feature if ever wanted.

## What stays

- Per-module **name resolution** and import lists (lexical scoping is
  untouched; local imports may also stay as file-discovery directives, per
  correction 5).
- The cache image shape `(Module, TypedProgram)` — with the catalog inside it
  reduced to the module's own slice (stage 4), keyed by the bumped
  `FORMAT_VERSION`.
- Accessibility records and checks — now the sole privacy mechanism (see
  risk R7).
- The fail-closed `dictionary.len() != expected` check in MIR — upgraded to
  `debug_assert!` + fail-closed, since under one table it can only fire on a
  genuine bug.
- The `SYMBOL_NAMES` display thread-local — though it installs once per
  compilation instead of once per module view, and `imported_symbol_names`'s
  N-way fold dies.

## Stages (each lands green)

0. **Prep**: `finalize.rs` export zonk → own-slice in-place walk; assert
   deterministic module order in the driver (it is today — pin it).
1. **Thread the one catalog** (`DriverConfig`-carried). Sessions take the
   shared table; delete the import-merge seed and `merge`'s import caller.
   Synthesis stays per-module post-collect. Package graph compiles deps in
   dependency order into the table (~80 LOC churn in `package.rs`); LSP
   workspace takes the table (~20); proc-macro re-entrancy guard keeps its
   test (~10).
2. **Commit once, at the backend boundary.** Deinit/dictionaries/owners move
   to where the module set closes; `commit_member_visibility` stays
   per-module; interim commit-before-serialize for cache writes.
3. **MIR takes the catalog.** Delete union + recommit + `struct_index`/
   `enum_index` + three catalog clones; `Layouts` borrows. Fix the three
   places that leaned on carving: the borrowed-storage gate filters to
   input-module-owned symbols; `display_names` builds a union name map; the
   ABI root-symbol scan disambiguates by owner. `talk bootstrap` regeneration
   + fixed-point re-pin.
4. **Cache payload = slice.** Delete the interface carving (~204 LOC);
   `TypedProgram` stops re-serializing imported facts; `FORMAT_VERSION` 1→2;
   resolve the file-discovery decision (correction 5).
5. **Coherence sweep.** Collection-time `OverlappingConformance` for
   conformance rows (sibling-module *and* sibling-package tests); pin the
   eviction-visibility case (a declared row evicting an earlier module's
   reflexive twin); inherent rows keep use-site ambiguity per the decision
   above.

## Audit ledger (deduplicated)

| surface | deleted | added | churned |
|---|---|---|---|
| `interface.rs` carving | ~204 | +6 (slice predicate net) | ~58 |
| `TypeCatalog::merge` + its unit test | 143 | — | — |
| `strip_synthesized_conformances` + call site | 22 | — | — |
| conformance-id ceiling blocks (×2) | 20 | — | — |
| MIR union + recommit + indexes + scans (`variant_names`/`field_names` → map hits) | ~69 | — | ~40 (rewritten smaller) |
| import seed (`generate/mod.rs`) + stale docs | ~10 | — | ~10 |
| driver/env threading, `insert_slice`, commit-once, cache slice loads | — | ~77 | ~60 |
| coherence diagnostic (stage 5) | — | ~15 | — |
| cache payload slice-ification + version bump | — | ~10 | ~50 |
| **totals** | **~468** | **~108** | **~218** |

**Net ≈ −360 LOC** in the compiler, before test-side effects: 3 tests deleted
(~80 LOC — two pin the carving the ADR removes, one pins `merge` itself),
~13 updated (mostly the `compile_library` helper rewrite paying for 11 of
them), 3 re-verified after stage 2 (they read committed state from
`type_check()` output), 2+ new (coherence collision; cross-module
determinism). Roughly 300 LOC of the deletions are the 2026-08-09 band-aids
plus their host function — the fixes that motivated this ADR consume
themselves.

## Former risk register — now in-stage tasks

Every item below has a predetermined resolution inside a stage; none is a
stop-and-decide point.

- Stage 0: `finalize.rs` own-slice walk; deterministic-module-order
  assertion.
- Stage 1: any `OverlappingConformance` surfacing in our tree when suites
  first run under one table is fixed then and there by deleting the
  duplicate row (predetermined resolution; our code, our call).
- Stage 3: borrowed-storage gate filters to input-module-owned symbols
  (`mir/build/mod.rs:962–999`); `display_names` builds the union name map
  (expected-output pins that relied on per-program insert order get re-pinned
  in the same commit); ABI root lookup disambiguates by owning module
  (`abi.rs:292–297`); `talk bootstrap` regeneration + fixed-point re-pin
  (routine — the gate is loud by design).
- Stage 4: cache keys gain the lock fingerprint + stdlib list hash;
  `FORMAT_VERSION` 1→2; privacy-coverage sweep: grep every use-site-facing
  read of `catalog.structs`/`extend_members`/`callable_contracts`, confirm
  each routes through `member_accessible` (three known call-site families),
  add the check where absent — bounded, mechanical, done inside the stage.
- Stage 5: pinning tests — sibling-module and sibling-package conformance
  collision at collection; eviction-visibility (declared row evicting an
  earlier module's reflexive twin); cross-module determinism (the other half
  of ADR 0043's gate).
