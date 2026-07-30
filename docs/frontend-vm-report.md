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

## Forwarding native-counter A/B

The immediately warmed, adjacent three-run confirmation produced deterministic
instruction and branch counts:

| Counter | Before | After forwarding | Change |
| --- | ---: | ---: | ---: |
| CPU task time | 94.508 s | 92.045 s | -2.61% |
| Cycles | 400.594 B | 389.504 B | -2.77% |
| Instructions | 790.585 B | 769.837 B | -2.62% |
| Branches | 119.615 B | 116.221 B | -2.84% |
| Branch misses | 303.670 M | 312.907 M | +3.04% |

## Critical-path latency

Per-test timing with 12 suite threads identifies
`compiling::bridge::tests::structured_results_validate_over_corpus` as the
wall-time gate. It consistently finishes about 0.2 seconds before the whole
library suite. Running that test alone removes suite scheduling noise.

Forwarding-call threading improved the isolated critical path by 4.50% elapsed,
4.00% instructions, 3.96% cycles, and 4.36% branches. A frame-pointer profile
of that result attributed 97.59% of cycles to the frontend VM, led by `rk` at
13.19%, `call_regs` at 11.06%, and `arg_values` at 8.81% inclusive.

## Owned RK materialization

`rk_value` now reads an owned register or constant operand directly for
`call_regs` and aggregate argument construction. Borrowed `rk` remains in
arithmetic and comparisons. `arg_values` uses one pre-sized explicit loop
instead of collecting an iterator of `Result`s. Bounds checks, cloning,
constant semantics, and safe Rust ownership are unchanged.

The five-run isolated critical-path A/B is:

| Counter | Before | With `rk_value` | Change |
| --- | ---: | ---: | ---: |
| Elapsed time | 8.433 s | 7.925 s | -6.03% |
| CPU task time | 8.428 s | 7.922 s | -6.01% |
| Cycles | 39.967 B | 37.417 B | -6.38% |
| Instructions | 105.560 B | 102.239 B | -3.15% |
| Branches | 15.758 B | 15.166 B | -3.76% |
| Branch misses | 34.544 M | 25.540 M | -26.06% |

The full 12-thread library suite's adjacent three-run counters confirm the
host-wide reduction:

| Counter | Before | With `rk_value` | Change |
| --- | ---: | ---: | ---: |
| CPU task time | 92.803 s | 87.779 s | -5.41% |
| Cycles | 394.164 B | 370.319 B | -6.05% |
| Instructions | 769.838 B | 748.512 B | -2.77% |
| Branches | 116.221 B | 112.431 B | -3.26% |
| Branch misses | 312.980 M | 276.222 M | -11.74% |

Full-suite elapsed time moved from 11.641 to 11.486 seconds, but its run
variance remains too high for a latency claim. The isolated critical path is
the authoritative wall-time result.

## Post-`rk_value` critical-path profile

The refreshed frame-pointer capture attributes 97.28% of weighted cycles to the
frontend VM. Exact-symbol inclusive accounting gives:

| VM path | Inclusive cycles |
| --- | ---: |
| `call_regs` | 10.53% |
| borrowed `rk` | 10.27% |
| `rk_value` | 4.89% |
| `arg_values` | 4.74% |
| `deliver_return` | 3.97% |
| `Allocations::check_access` | 1.75% |
| `chunk` | 0.88% |

`arg_values` fell from 8.81% to 4.74%. Of `call_regs`' 10.53%, 3.32 percentage
points are nested `rk_value`, leaving about 7.21% outside operand ownership.
Borrowed `rk` is therefore the largest independent helper at 10.27%.

## Native cost by bytecode type

The critical-path corpus executes 78,663,225 VM instructions across 257 export
runs. Differential microbenchmarks compare loops containing four and twelve
copies of one opcode, using exact retired native instructions and repeated wall
and cycle counters. `Call+Ret` is measured as one call frame round trip. The
wall estimates are context-sensitive and not additive, but their ranking and
retired-instruction weights identify where execution time is actually spent.

| Instruction | Critical executions | Native instructions/execution | Weighted native instructions | Share of all native instructions | Estimated wall time |
| --- | ---: | ---: | ---: | ---: | ---: |
| `GetField` | 18.09 M | 1,053 | 19.05 B | 18.6% | 1.25 s |
| `Call+Ret` | 5.09 M | 3,359 | 17.10 B | 16.7% | 1.25 s |
| `Cmp` | 8.19 M | 1,388 | 11.37 B | 11.1% | 0.80 s |
| `Add` | 5.92 M | 1,390 | 8.24 B | 8.1% | 0.62 s |
| `Branch` | 10.56 M | 610 | 6.44 B | 6.3% | 0.46 s |
| `Const` | 4.92 M | 947 | 4.66 B | 4.6% | 0.36 s |
| `Load` | 2.84 M | 1,458 | 4.14 B | 4.0% | 0.29 s |
| `TupleNew` | 1.20 M | 2,274 | 2.74 B | 2.7% | 0.19 s |
| `Extract` | 2.46 M | 1,053 | 2.59 B | 2.5% | 0.18 s |
| `VariantNew` | 0.90 M | 2,287 | 2.05 B | 2.0% | 0.14 s |
| `CheckedIndexedLoad` | 1.12 M | 1,796 | 2.02 B | 2.0% | 0.13 s |
| `Jump` | 4.11 M | 458 | 1.88 B | 1.8% | 0.12 s |
| `RecordNew` | 0.79 M | 2,282 | 1.81 B | 1.8% | 0.12 s |
| `GetTag` | 1.74 M | 760 | 1.32 B | 1.3% | 0.08 s |

These calibrated types explain 83.5% of retired native instructions and about
75.7% of isolated wall time. Field projection, call frames, and comparison
control flow are the dominant costs; borrowed RK combinators are a component
of those handlers rather than the largest strategic opportunity by themselves.

Exact dynamic shape counts expose the largest removable streams:

| Shape | Executions | Share of all VM dispatches |
| --- | ---: | ---: |
| `Cmp; Branch` over the comparison result | 7,541,379 | 9.59% |
| Consecutive `GetField` pair edge | 6,669,300 | 8.48% |
| `CheckedIndexedLoad; Jump` | 1,122,524 | 1.43% |
| Remaining direct `Call; Ret` tail shape | 400,228 | 0.51% |

There are 1,174 immediate compare-branch sites among 1,282 emitted `Cmp` sites,
so comparison branching is a general compiler shape rather than one anomalous
source function.

## Ranked next work

1. **Semantic compare-branch instructions.** Fuse a dead comparison result and
   its branch in MIR or direct bytecode emission. This can remove up to 7.54
   million dispatches, boolean register materialization, and the second
   dispatch fetch while preserving typed comparison errors. It is the largest
   bounded, generic opportunity.
2. **Field-path projection.** Consecutive field reads expose 6.67 million
   removable pair edges. A verified `GetFieldPath`-style operation could borrow
   through intermediate records, clone only the final value, and avoid both
   intermediate dispatches and `Rc` traffic. This may rival compare-branch but
   requires more validation and encoding work.
3. **Broader call reduction.** Call frames account for 16.7% of native
   instructions, but only 0.51% of dispatches remain in the simple direct
   tail-call shape. Significant gains require more inlining, specialization, or
   a cheaper calling convention rather than another narrow forwarding pass.
4. **Baseline native compilation.** The VM consumes 97.28% of critical-path
   cycles. Removing interpretation entirely has the largest long-term ceiling,
   but is a substantially larger project than semantic superinstructions.
5. **Micro-optimizations.** Flattening borrowed `rk` and removing the checked
   load success jump remain valid smaller experiments, but they should follow
   the two measured superinstruction opportunities.
