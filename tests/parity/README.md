# Backend parity fixtures

This directory freezes behavior and test dispositions from
`pre-backend-reset-2026-07-13` (`96249e71`). The semantic authority remains ADR
0032; baseline artifacts are evidence, not permission to restore unsafe or
superseded behavior.

## Complete-program oracles

`programs/<name>.stdout` is the byte-exact baseline stdout for
`tests/programs/<name>.tlk`. See `programs/README.md` for capture and resource
observations.

## Archived test dispositions

`baseline-test-disposition.tsv` accounts for every test reported by the
baseline library test binary under these modules:

- `flow::flow_tests`: 151 tests
- `lower::lower_tests::tests`: 53 tests
- `vm::vm_tests::tests`: 293 tests

Total: 497 tests. The inventory was checked against `cargo test --lib -- --list`
on the immutable baseline worktree. Every test appears exactly once, and every
referenced row exists in `docs/backend-parity-ledger.md`.

Columns:

| Column | Meaning |
| --- | --- |
| `suite` | `F` flow, `L` lowering, `V` VM |
| `test` | Exact baseline test name |
| `class` | `R` required behavior, `I` deleted implementation-only test |
| `ledger_rows` | Capability rows that preserve or replace the behavior |
| `disposition` | How to interpret the old assertion |

Disposition codes:

| Code | Meaning |
| --- | --- |
| `B` | Preserve the source, diagnostic, runtime-safety, or observable behavior through the new pipeline |
| `FS` | Do not port the old flow/drop-fact shape; replace it with structural MIR, verifier, and black-box laws |
| `LS` | Do not port the old lowering/lambda-G shape; preserve the named behavior through canonical artifacts and G5 |
| `EF` | Do not restore the evaluator fence; enforce the resource invariant in the reference runtime |

A Required disposition does not mean the old harness returns. For example,
`vm_matches_evaluator_*` records required source behavior, while the evaluator
half of the old differential harness remains deleted. Once Wasm connects,
bytecode-versus-Wasm execution provides the independent differential check.

The row mapping is intentionally many-to-many. A borrowed enum match with an
owned payload belongs to aggregate, pattern, borrow, ownership, and managed
storage rows. A row cannot claim parity until all required tests mapped to it
have replacement coverage or an accepted changed/reject disposition.
