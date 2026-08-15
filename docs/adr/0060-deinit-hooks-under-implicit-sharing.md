# 0060 - Deinit hooks under implicit sharing

Status: accepted (implemented 2026-08-08 — `DropToken` in core/Array.tlk
over `_storage_is_unique` (Ownership.tlk cannot hold it: Array imports the
grade protocols, so the buffer type is only available downstream); stdlib channel endpoints refactored onto it; the
per-copy hook rule pinned by tests/reference/flow corpus programs)

## Context

Implicit sharing (docs/ownership.md) duplicates a value by retain at value
boundaries: a non-last-use consume donates, a field read out of a live place
donates, a tuple element read donates. Each duplicate is a real owned value
whose scope exit runs drop glue — and ADR 0038's `Deinit` conformance is a
hook inside that glue. The two decisions compose into an observable fact:
**a `Deinit` hook runs once per copy, not once per logical value.**

Core containers were always safe under this rule without saying so: `Array`
and `String` deinits gate their teardown on `_is_unique` over the buffer
they own, so every copy runs the hook and exactly one copy tears down.
ADR 0059's channel endpoints were the first hook-carrying types with *no*
buffer, and they broke both ways before this was understood: the drop
scheduler skipped hooks stored inside aggregates (a compiler bug, fixed —
`contains_deinit` in needs_drop), and donation ran close/unregister once per
duplicate (not a bug — the model).

## Decision

1. **The per-copy rule is the semantics, not a defect.** A `Deinit` hook is
   part of drop glue; drop glue runs per owned value; implicit sharing mints
   owned values by retain. Rejecting duplication for hook-carrying types was
   considered and refused: `String` and `Array` conform to `Deinit`, and
   move-only strings would gut the sharing model. Hidden drop flags were
   refused too: they tax every move to serve a rare pattern.

2. **Exactly-once hooks opt in with a witness the runtime already
   refcounts.** A type whose hook must fire once per logical value carries a
   `DropToken` — a one-field struct owning an empty buffer — and gates the
   hook body on `token.is_last()`. Retains bump the buffer's owner count, so
   the copy whose count is 1 is provably the last, wherever and whenever it
   drops. This is the same gate core containers use, given a name.

3. **`DropToken` lives in core (Array.tlk)** next to
   `_storage_is_unique`, the primitive it names. A fresh token is
   a fresh logical identity: `clone`-style operations that mint a new
   logical value construct a new token; copies made by the compiler share
   the token.

## Consequences

- stdlib `Sender`/`Receiver`/`Recv` (and every future endpoint type) spell
  their lifecycle guard as one field and one `is_last()` call instead of a
  hand-rolled token buffer each.
- A hook-only struct without a token remains legal: its hook runs per copy.
  That is the right meaning for idempotent hooks (close-if-open over an
  already-guarded resource) and the documented sharp edge for everything
  else.
- The cost of exactly-once is one empty buffer allocation per logical value
  and one owner-count read per drop — paid only by types that ask.

## Validation

1. tests/reference/flow/deinit_hook_runs_through_stored_fields.tlk — hooks
   fire through struct fields, enum payloads, array elements (the fixed
   compiler half).
2. A `DropToken`-guarded hook fires exactly once under donation, field
   extraction, and cross-worker transfer — the channel corpus programs pin
   this on every backend, C's exit-time leak accounting included.

## Relationship to existing decisions

- **ADR 0038:** `Deinit` stays a plain glue hook; this names its
  interaction with sharing instead of changing it.
- **docs/ownership.md:** duplication-by-retain is untouched; linear and
  unique values remain the only refusals.
- **ADR 0059:** channel endpoints are the first `DropToken` users.
