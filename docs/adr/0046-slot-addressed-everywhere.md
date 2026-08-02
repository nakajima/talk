# ADR 0046: Slot-addressed aggregates everywhere

Status: implemented — all four stages landed 2026-08-02. Stage B held
wire byte-identity; stage D's fold regenerated the artifact (fixed point
held); stage C re-pinned the C backend's generated-text tests with the
differential suite as the behavior gate.

## Context

ADR 0045 gave the VM one flat aggregate representation: `Value::Agg(layout, slots)`,
tag in slot 0, spliced children inline, every access a static offset under the
published layout table. But the compiler still speaks three addressing schemes:

1. **VM / wire**: slot offsets (flat) — the ADR 0045 form.
2. **C native structs**: field-indexed members (`x.m{field}`), spliced children
   as nested struct members — for products; native *sums* are already slot-flat.
3. **C tagged fallback**: `talk_agg(symbol, tag, len)` with **payload-indexed**
   `fields[]` — the pre-0045 model, alive in one backend.

MIR must therefore carry logical indexes (`index`, `of_variant`) so each backend
can re-derive its own addressing, `lower` re-resolves offsets the classifier
already knows, and statically-flat member chains (`array.storage.base` is slot 0)
cannot fold: a folded access is "slot o of x", which index vocabulary cannot say.

## Decision

One addressing scheme: **slot offsets under published layouts**, in all three
representations.

- **D1 — MIR is offset-addressed.** `Inst::Field`/`Inst::SetField` carry
  `{offset, member layout}`; `index`/`of_variant` are deleted. The classifier
  owns the arithmetic (ADR 0045 rule 4): a single `layout::field_site` answers
  offset+member for the builder, and `shape_desc` publishes from the same
  computation, so compiler-side and wire offsets cannot drift. This is the
  standard AOT model — fields resolve to layout offsets at compile time (C
  struct member access; Rust/Swift aggregate layout), not re-derived per
  backend.
- **D2 — Native product structs flatten to slot-named members** (`m{offset}`,
  one member per slot), exactly the form native sums already have. A spliced
  child's members are the parent's members at its offset range; whole-child
  copies remain plain struct-slice assignments (identical member prefixes ⇒
  compatible layout).
- **D3 — The tagged C form becomes the VM value verbatim**:
  `TalkAgg { layout, display, width, slots[] }` — tag in slot 0 for sums, slots
  hold tagged values, spliced children inline. Structural operations (render,
  logical field access at the existential boundary, copy-on-write splice
  writes) dispatch through generated per-layout helpers, generalizing the
  mechanism `TalkNative` already uses (`talk_native_field/set_field/retag/scan`).
  Rendering stays cold-path: flat converts to the renderer's nested form via
  the generated retag, as native boxes do today.
- **D4 — Layout-less containers keep their own shape.** Closures, cells,
  existentials, and continuation thunks use `talk_agg` as an untyped slot
  vector (all members single slots, so payload index ≡ slot offset) under a
  sentinel layout; the closure's function index stays header metadata. They are
  runtime representation, not layout-governed aggregates.
- **D5 — Chain folding happens at emission.** With offsets in MIR, a member
  chain through spliced parents accumulates into one access at the emission
  site. Gated on an ownership audit: an intermediate spliced-read temp may
  carry teardown obligations; only obligation-free hops fold. The
  checked-indexed-load pattern updates in the same change (its window shrinks
  again), and the artifact regenerates.
- **D6 — The wire format does not change.** The wire has been offset-addressed
  since format 6; stages A–C are byte-identical on the wire (verified by
  `bootstrap --check` returning *up to date*), and only D5 changes emitted
  bytes.

## Stages (each lands green: full suites, differential, zero warnings)

- **A.** `layout.rs` gains the offset API; `shape_desc` publishes through it
  (one arithmetic source).
- **B.** *(landed)* MIR `Field`/`SetField` carry `{container, offset,
  member}`; MIR gained `FieldIndex`/`SetFieldIndex`, mirroring the wire's
  logical ops, and the existential-boundary routing moved from `lower` into
  the builder (`push_field`/`push_set_field`); `lower`'s `field_site`/
  `unshaped` are deleted; c.rs recovers field identity from offsets
  (`product_field`/`payload_index` — stage C retires both). `Field` keeps
  `of_variant` transitionally: the payload-indexed tagged C sum needs the
  variant to map an offset back to a payload position; stage C deletes it.
  Gate held: `bootstrap --check` byte-identical after the move.
- **C.** *(landed)* Flattened native structs (one member per slot, sums
  and products one typedef); `TalkAgg { layout, symbol, meta, len }` with
  flat slots, tag in slot 0 (`meta` carries the closure function index);
  the layout table embedded as C data (`talk_layouts`) drives rendering
  and the logical boundary generically — the generated per-layout
  field/set_field dispatchers are deleted, `talk_native_field`/`_set_field`
  are prelude-generic, and box/unbox/retag collapse to one per-slot
  conversion loop for every shape. Runtime form invariant: values of
  box-native layouts are `TALK_NATIVE` wherever the emitter reasons
  statically; children sliced out of flat parents re-box through the
  generated `talk_rebox`, and `talk_unbox_l{id}` accepts both forms.
- **D.** *(landed)* The fold lives in `push_field` as an adjacency
  rewrite: when the source is the immediately-preceding instruction's
  spliced read, the new access re-addresses through the parent at the
  summed offset — only the new access rewrites, the intermediate stays
  for any other consumer, and `dead_code` (which now collects member
  reads) removes it otherwise. Adjacency alone makes it sound. The
  checked-indexed-load pattern shrank 7→6 instructions in the same
  change, with a stats test pinning that fusion still fires.

## Consequences

- MIR loses a vocabulary (`index`/`of_variant`, the classifier's dual
  clients); `lower`'s field resolution thins to a copy.
- The interim fold inside `checked_indexed_load` (ADR 0045 follow-up S3)
  retires when D5 lands; general `x.storage.base` chains stop allocating.
- Pinned C outputs change at stage C (member renaming, flat tagged form) —
  re-pinned deliberately, behavior verified by the differential suite.
- The renderer and scanner consume generated per-layout code instead of
  trusting `len` — the last place a C value could disagree with its published
  layout disappears.
