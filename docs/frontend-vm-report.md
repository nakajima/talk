# Self-hosted frontend VM report

Status: current forwarding-call experiment on commit `d2bd469e` (2026-07-29).

The complete current report is
[`profiles/frontend-vm/d2bd469efa5d-dirty-a6b49355f2ef.txt`](../profiles/frontend-vm/d2bd469efa5d-dirty-a6b49355f2ef.txt).
The clean pre-forwarding baseline remains
[`profiles/frontend-vm/d2bd469efa5d.txt`](../profiles/frontend-vm/d2bd469efa5d.txt).
This document summarizes their exact counts and the isolated native-counter
A/B from the same source transition.

## Workloads and method

Exact bytecode counts come from:

```text
scripts/frontend-vm-stats.sh
```

The script builds the frontend twice, verifies the candidate is a fixed point,
records both stages' optimization counts, and runs `parse_file_source` over the
four sorted `stdlib/syntax/*.tlk` files. Counts are VM-owned and deterministic.
The elapsed time includes statistics collection and is not a native performance
claim.

Native counters use the root library test executable directly with 12 fixed
threads. Each executable receives one warmup immediately before its measured
batch:

```text
perf stat -r 3 -e task-clock,cycles,instructions,branches,branch-misses -- \
  "$TEST_EXECUTABLE" --quiet --test-threads=12
```

Cargo and build time are excluded. The experiment changes only the forwarding
pass, its tests and accounting, and the regenerated frontend artifact.

## Current snapshot

| Measure | Current |
| --- | ---: |
| Frontend artifact | `899cd2e85dfc...675f45d59a4e` |
| Artifact bytes | 836,288 |
| Bytecode chunks | 1,075 |
| Emitted VM instructions | 96,851 |
| Executed VM instructions | 175,259,482 |
| Frontend export runs | 4 |
| Instrumented VM time | 20.593 s |
| Instrumented throughput | 8.511 M dispatches/s |

Both bootstrap stages report the same 16,137 rewrites:

| Optimization | Rewrites |
| --- | ---: |
| `unreachable_blocks` | 7,142 |
| `dead_code` | 2,463 |
| `inline_small` | 2,130 |
| `match_switch` | 1,602 |
| `simplify_block_params` | 1,563 |
| `branch_fold` | 1,087 |
| `constant_fold` | 73 |
| `forward_calls` | 40 |
| `checked_indexed_load` | 37 |

## Forwarding-call result

The whole-program MIR pass recognizes an identity forwarder only when it has
one block, no block parameters, one unwind-free direct call over its parameters
in order, and returns that call's destination. It retargets direct callers while
preserving each caller's own destination and unwind edge. Closure construction,
exports, entry points, and `inline_small`'s call-free contract are untouched.

The frontend contains 13 such `subscript_read` functions. They have 40 direct
call sites and execute 3,382,302 times in the corpus.

| Measure | Before | Current | Change |
| --- | ---: | ---: | ---: |
| Artifact bytes | 836,288 | 836,288 | 0 |
| Emitted instructions | 96,851 | 96,851 | 0 |
| Executed instructions | 182,024,086 | 175,259,482 | -6,764,604 (-3.72%) |
| `Call` executions | 14,587,056 | 11,204,754 | -3,382,302 (-23.19%) |
| `Ret` executions | 14,587,064 | 11,204,762 | -3,382,302 (-23.19%) |

The exact reduction is the predicted `Call; Ret` pair per invocation. All other
opcode counts are unchanged.

## Checked indexed-load result

The earlier 37 checked-load fusion sites reduced exact dispatches from
213,321,433 to 182,024,086 (-14.67%) while increasing the artifact by 2,146
bytes (+0.26%). Each successful fusion replaces eleven dispatched instructions
with `CheckedIndexedLoad; Jump`, removing nine dispatches. Across 3,477,483
executions that accounts exactly for 31,297,347 removed dispatches. The
appended original sequence remains the failure path, preserving the
source-owned, catchable Talk `'panic`.

Together, checked loads and call forwarding reduce the pre-fusion stream from
213,321,433 to 175,259,482 dispatches (-17.84%).

## Current opcode composition

| Opcode | Emitted | Executed | Execution share |
| --- | ---: | ---: | ---: |
| `GetField` | 33,274 | 41,678,989 | 23.78% |
| `Branch` | 2,136 | 23,760,887 | 13.56% |
| `Cmp` | 1,282 | 18,752,400 | 10.70% |
| `Add` | 1,056 | 12,280,221 | 7.01% |
| `Ret` | 1,714 | 11,204,762 | 6.39% |
| `Call` | 5,783 | 11,204,754 | 6.39% |
| `Jump` | 8,979 | 10,208,983 | 5.83% |
| `Const` | 3,834 | 10,102,982 | 5.76% |
| `Load` | 491 | 5,250,828 | 3.00% |
| `Extract` | 3,528 | 4,900,901 | 2.80% |
| `GetTag` | 2,240 | 3,765,985 | 2.15% |
| `CheckedIndexedLoad` | 37 | 3,477,483 | 1.98% |

Calls and returns now account for 12.79% of dispatches, down from 16.03%.

## Hottest chunks

| Chunk | Name | Emitted | Executed | Share |
| ---: | --- | ---: | ---: | ---: |
| 33 | `scan` | 2,692 | 20,878,284 | 11.91% |
| 91 | `get` | 16 | 17,964,876 | 10.25% |
| 477 | `claim_slot_full` | 162 | 12,891,246 | 7.36% |
| 482 | `token_index_starting` | 23 | 10,214,841 | 5.83% |
| 531 | `token_at` | 19 | 7,454,368 | 4.25% |
| 508 | `token_index_ending` | 23 | 6,870,412 | 3.92% |
| 75 | `at` | 7 | 5,422,788 | 3.09% |
| 40 | `token_positions` | 62 | 4,579,749 | 2.61% |
| 710 | `infix_precedence` | 516 | 3,746,867 | 2.14% |
| 106 | `is_alpha` | 28 | 3,607,063 | 2.06% |

These ten chunks account for 53.42% of execution. The former two-instruction
`subscript_read` wrappers now execute zero instructions. The dominant
successful `get` site remains:

```text
GetField
GetField
GetField
CheckedIndexedLoad
Jump
Ret
```

## Isolated native-counter A/B

The immediately warmed, adjacent three-run confirmation produced deterministic
instruction and branch counts:

| Counter | Before | Current | Change |
| --- | ---: | ---: | ---: |
| CPU task time | 94.508 s | 92.045 s | -2.61% |
| Cycles | 400.594 B | 389.504 B | -2.77% |
| Instructions | 790.585 B | 769.837 B | -2.62% |
| Branches | 119.615 B | 116.221 B | -2.84% |
| Branch misses | 303.670 M | 312.907 M | +3.04% |

A separate initial five-run batch measured -3.16% instructions, -3.48% cycles,
-3.88% CPU task time, and -3.42% branches. Full-suite subprocess and cache state
can shift the absolute instruction baseline between batches, so the adjacent
warm confirmation is the conservative retained result. Both batches establish
the same material reduction in instructions, cycles, task time, and branches.
Branch-miss direction was inconsistent between batches and is not claimed as
an improvement.

## Previous sampled attribution

The most recent frame-pointer sample predates call forwarding:

| Category | Weighted cycles |
| --- | ---: |
| Frontend VM | 83.61% |
| Type checking | 9.50% |
| Frontend bridge | 2.52% |
| Other | 2.26% |
| Backend | 1.40% |
| Name resolution | 0.56% |

Its overlapping VM costs included `rk` at 10.70%, `call_regs` at 10.27%,
`arg_values` at 6.82%, and `deliver_return` at 4.12%. Call forwarding removes
work from the latter three, so this attribution must be refreshed before
choosing a host-side call optimization.

## Ranked next work

1. **Refresh the frame-pointer profile.** Confirm how much `call_regs`,
   `arg_values`, and `deliver_return` fell and identify the new dominant native
   cost.
2. **Emit checked indexed loads semantically from MIR.** Direct emission can
   remove the structural matcher, make success fall through instead of
   executing 3,477,483 `Jump`s, and cover unit-width accesses while preserving
   the explicit source-owned failure target.
3. **Re-evaluate call-frame construction and RK operands.** Only optimize these
   after the refreshed profile; forwarding has removed a large portion of the
   traffic represented by the previous samples.
