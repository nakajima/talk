# Commit 098: `21e56b9b` - Wave 4: port the strings/collections/drops reference clusters

| Field | Value |
|---|---|
| Commit | `21e56b9bb8902318b3a3d731d24b51472ee313ec` |
| Parent reviewed | `d471beb900bd638f527214ec81ba2aa9b5ced1ae` |
| Author date | 2026-07-17T04:01:32-07:00 |
| Author | Pat Nakajima |
| Patch size | 126 files, +733 / -19 |
| Review result | **No new finding; inherited red state** |

## Intent and sequence context

61 reference behavior tests join G6 as three corpus clusters
(tests/reference/{strings,collections,drops}) alongside the effects
cluster - 79 pins total. The port immediately caught three real
defects, now fixed: initializers registered writeback slots for
exclusive-borrow parameters that constructions never unpack (every
mut-mode for loop failed the convention validator - F6 confirmed and
closed); consume_into retained through Borrowed-classified views,
counting references view drops never release (iterator adapters leaked
one allocation); and or-patterns/variant patterns computed
leaves-owned-unbound conservatively, rejecting or-arms that bind every
payload. The writeback validator now names the offending callee.

This is part of the lean backend sequence that remains represented at the branch tip unless a later review explicitly notes supersession.

## Patch analysis

- File operations: A: 124, M: 2.
- Production Rust: 1 files (+46/-19): `src/backend/mir.rs`.
- Tests and test oracles: 125 files (+687/-0): `tests/reference/collections/array_count.tlk`, `tests/reference/collections/array_get.tlk`, `tests/reference/collections/array_iterator_next.tlk`, `tests/reference/collections/array_of_structs.tlk`, `tests/reference/collections/array_show.tlk`, `tests/reference/collections/array_show_generic.tlk`, `tests/reference/collections/array_swap.tlk`, `tests/reference/collections/consume_for_feeds_consuming_callback.tlk`, and 117 more.

### Highest-churn files

| File | Added | Deleted |
|---|---:|---:|
| `src/backend/mir.rs` | 46 | 19 |
| `tests/reference/strings/utf8_decode.tlk` | 42 | 0 |
| `tests/talk_tests.rs` | 23 | 0 |
| `tests/reference/collections/array_iterator_next.tlk` | 20 | 0 |
| `tests/reference/strings/grapheme_category_lookup.tlk` | 17 | 0 |
| `tests/reference/strings/string_operations.tlk` | 16 | 0 |
| `tests/reference/collections/consuming_protocol_default_on_projection.tlk` | 16 | 0 |
| `tests/reference/collections/sums_borrowed_scalars.tlk` | 14 | 0 |
| `tests/reference/collections/mut_for_mut_borrow_after.tlk` | 14 | 0 |
| `tests/reference/drops/conditional_field_scrutinee_match.tlk` | 13 | 0 |
| `tests/reference/collections/mut_for_non_cheap_clone.tlk` | 13 | 0 |
| `tests/reference/collections/match_borrowed_loop_element.tlk` | 13 | 0 |
| `tests/reference/collections/index_borrowed_struct_witness.tlk` | 13 | 0 |
| `tests/reference/collections/for_break_drops_binders.tlk` | 13 | 0 |
| `tests/reference/drops/break_after_move.tlk` | 12 | 0 |

### Representative declarations touched

- `impl<'a> ProgramBuilder<'a> {`
- `impl<'p, 'a> FunctionBuilder<'p, 'a> {`
- `struct Point`
- `struct Item`
- `struct Pt`
- `enum Entry`
- `struct Holder`
- `enum Wrapped`
- `enum E`
- `fn reference_effects_cluster_matches_frozen_stdout() {`
- `fn reference_strings_cluster_matches_frozen_stdout`
- `fn reference_collections_cluster_matches_frozen_stdout`
- `fn reference_drops_cluster_matches_frozen_stdout`

## Test and validation review

- Historical checkout: `cargo check --all-targets --locked --quiet` passed at this exact commit (2s).
- Historical checkout: `cargo test --locked --quiet` **failed** at this exact commit (15s): `run_enforces_capture_list_modes`.
- This test failure is inherited from `cabfc772`; this patch did not introduce it. The originating review contains the root finding.
- `git diff --check` passed for this commit against its first parent.
- Added or materially introduced Rust test functions detected in the patch: `reference_strings_cluster_matches_frozen_stdout`, `reference_collections_cluster_matches_frozen_stdout`, `reference_drops_cluster_matches_frozen_stdout`.
- Added Talk/expected-output fixtures: `tests/reference/collections/array_count.tlk`, `tests/reference/collections/array_get.tlk`, `tests/reference/collections/array_iterator_next.tlk`, `tests/reference/collections/array_of_structs.tlk`, `tests/reference/collections/array_show.tlk`, `tests/reference/collections/array_show_generic.tlk`, `tests/reference/collections/array_swap.tlk`, `tests/reference/collections/consume_for_feeds_consuming_callback.tlk`, `tests/reference/collections/consume_for_moves_out.tlk`, `tests/reference/collections/consume_for_non_cheap_clone.tlk`, `tests/reference/collections/consuming_protocol_default_on_projection.tlk`, `tests/reference/collections/element_feeds_borrow_callback.tlk`, `tests/reference/collections/expected/array_count.stdout`, `tests/reference/collections/expected/array_get.stdout`, `tests/reference/collections/expected/array_iterator_next.stdout`, `tests/reference/collections/expected/array_of_structs.stdout` and 108 more.

## Findings

No correctness, safety, or integration blocker was identified in this commit under the stated review scope. This is not a claim that every behavior was re-executed at the historical checkout; it means the patch, exact-checkout compile result (when applicable), tests/oracles changed, and later interactions did not expose a commit-local defect.

## Disposition

No new defect was attributed to this patch, but it is not independently green because it inherits the unresolved test failure from `cabfc772`. Correct or squash the originating commit before retaining this point in history.
