# Self-hosted frontend VM report

## Workload

This capture ran:

```text
cargo test --lib compiling::bootstrap::tests::checked_in_frontend_artifacts_are_a_fixed_point -- --exact
```

The test rebuilds the checked-in self-hosted frontend twice and checks that the
result is a fixed point. A temporary `VmStats` probe aggregated every
`parse_file_source` export call. The same 35 calls were run against:

- before: `7fd550fe5166b10a44788f05f5af0bb4cdc4fbd199d33d6fe1d80b67dbe0cf30`;
- after: `e3f6f0b138f72dbc162cf40055abf048cad02babd7b9d949685228b6d978a477`.

The old artifact was supplied through a temporary test-only loader override;
the probe and override were removed after capture.

Counts are exact. Time is the instrumented VM run-loop time and includes the
cost of incrementing one `(chunk, pc)` counter per dispatch. Native instruction
costs below are estimates from the differential measurements recorded in
`docs/profiling-findings.md`; `VmStats` does not time individual dispatches.

## Optimization result

| Measure | Before | After | Change |
| --- | ---: | ---: | ---: |
| Frontend export runs | 35 | 35 | 0 |
| Bytecode chunks | 1,075 | 1,075 | 0 |
| Artifact bytes | 951,106 | 934,063 | -17,043 (-1.79%) |
| Emitted VM instructions | 113,944 | 111,442 | -2,502 (-2.20%) |
| Executed VM instructions | 562,537,865 | 544,420,518 | -18,117,347 (-3.22%) |
| Instrumented VM time | 97.281 s | 94.638 s | -2.643 s (-2.72%) |
| Whole test time | 128.69 s | 126.26 s | -2.43 s (-1.89%) |

**The optimizations helped.** They removed 2.2% of the image and 3.2% of the
dynamic instruction stream. Those exact count reductions are the reliable
result. A repeat run of the optimized artifact took 96.785 s in the VM and
129.16 s overall, so the observed wall-clock improvement is within run-to-run
noise and should not be treated as established yet.

The optimized workload still executes more than half a billion VM
instructions. Its ten hottest chunks account for 54.9% of all dispatches.

## Emitted code

### Opcode composition

| Opcode | Emitted | Share |
| --- | ---: | ---: |
| GetField | 33,163 | 29.8% |
| Retain | 11,924 | 10.7% |
| GetPayload | 11,735 | 10.5% |
| Branch | 10,020 | 9.0% |
| Cmp | 9,521 | 8.5% |
| Jump | 8,916 | 8.0% |
| Call | 5,783 | 5.2% |
| Const | 3,834 | 3.4% |
| Extract | 3,528 | 3.2% |
| GetTag | 2,240 | 2.0% |
| RecordNew | 1,915 | 1.7% |
| Ret | 1,714 | 1.5% |
| VariantNew | 1,250 | 1.1% |
| Add | 1,019 | 0.9% |

The first seven opcodes occupy 81.7% of the image. Field projection alone is
nearly 30% of all emitted code.

Most of the static reduction came from constants and control-flow cleanup:

| Opcode | Before | After | Removed |
| --- | ---: | ---: | ---: |
| Const | 5,448 | 3,834 | 1,614 |
| Trap | 895 | 553 | 342 |
| Jump | 9,084 | 8,916 | 168 |
| Call | 5,871 | 5,783 | 88 |
| Sub | 157 | 84 | 73 |
| UnwindRet | 479 | 420 | 59 |
| Ret | 1,758 | 1,714 | 44 |
| GetField | 33,206 | 33,163 | 43 |
| TupleNew | 906 | 864 | 42 |
| Branch | 10,042 | 10,020 | 22 |

### Largest chunks

| Chunk | Name | Emitted | Executed |
| ---: | --- | ---: | ---: |
| 447 | `_index_iterable_get` | 8,350 | 602,998 |
| 537 | `_retain` | 8,349 | 0 |
| 701 | `_retain` | 3,836 | 0 |
| 776 | `pub_decl` | 3,783 | 95,146 |
| 442 | `_index_iterable_get` | 3,690 | 108,079 |
| 875 | `_retain` | 3,689 | 0 |
| 33 | `scan` | 2,844 | 52,281,964 |
| 715 | `member_infix` | 2,662 | 369,920 |
| 740 | `call` | 2,607 | 972,742 |
| 790 | `let_decl` | 2,402 | 200,618 |
| 837 | `desugar_let_else` | 2,228 | 0 |
| 745 | `call_with_leading_string_arg` | 1,928 | 0 |
| 714 | `check_as` | 1,861 | 829,485 |

The largest two chunks alone occupy 15.0% of the image; the largest ten occupy
37.9%. The near-identical 8,350-instruction `_index_iterable_get` and
8,349-instruction `_retain` pair is the strongest code-size anomaly.

For this workload, 495 chunks containing 39,899 instructions never execute.
That is 35.8% of the image. This is workload reachability, not proof that those
chunks are globally dead, but the very large unexecuted `_retain` chunks merit
specific investigation.

## Dynamic execution

Only four opcode classes changed dynamically. Constant elimination accounts
for 96.5% of all removed dispatches:

| Opcode | Before | After | Change |
| --- | ---: | ---: | ---: |
| Const | 56,485,442 | 39,002,300 | -17,483,142 (-30.95%) |
| Jump | 15,946,678 | 15,628,565 | -318,113 (-1.99%) |
| Sub | 3,670,575 | 3,427,042 | -243,533 (-6.63%) |
| Branch | 89,171,642 | 89,099,083 | -72,559 (-0.08%) |

Calls, returns, comparisons, field accesses, and all allocation-related opcode
counts were unchanged.

### Opcode frequency after optimization

| Opcode | Executed | Share |
| --- | ---: | ---: |
| Cmp | 95,970,299 | 17.63% |
| GetField | 95,960,634 | 17.63% |
| Branch | 89,099,083 | 16.37% |
| Ret | 41,181,593 | 7.56% |
| Call | 41,181,523 | 7.56% |
| Const | 39,002,300 | 7.16% |
| Add | 36,672,386 | 6.74% |
| Load | 20,318,206 | 3.73% |
| Jump | 15,628,565 | 2.87% |
| Mul | 12,588,537 | 2.31% |
| Extract | 11,520,234 | 2.12% |
| GetTag | 8,586,505 | 1.58% |
| TupleNew | 5,629,822 | 1.03% |
| VariantNew | 4,472,901 | 0.82% |
| Div | 3,954,934 | 0.73% |
| RecordNew | 3,779,228 | 0.69% |
| Sub | 3,427,042 | 0.63% |
| SetField | 3,321,348 | 0.61% |
| Store | 3,216,080 | 0.59% |
| IsUnique | 1,953,607 | 0.36% |
| BToI | 1,549,143 | 0.28% |
| Free | 1,440,098 | 0.26% |
| GetPayload | 1,420,523 | 0.26% |
| Move | 881,518 | 0.16% |
| Alloc | 877,327 | 0.16% |
| Retain | 771,445 | 0.14% |

Comparison, field access, and branching account for 51.6% of all dispatches.
Calls and returns add another 15.1%.

### Hottest chunks

| Chunk | Name | Emitted | Executed | Share |
| ---: | --- | ---: | ---: | ---: |
| 92 | `_check_index` | 26 | 66,408,310 | 12.20% |
| 91 | `get` | 8 | 53,126,648 | 9.76% |
| 33 | `scan` | 2,844 | 52,281,964 | 9.60% |
| 477 | `claim_slot_full` | 181 | 31,291,203 | 5.75% |
| 482 | `token_index_starting` | 23 | 22,354,106 | 4.11% |
| 531 | `token_at` | 23 | 18,506,098 | 3.40% |
| 508 | `token_index_ending` | 23 | 15,063,341 | 2.77% |
| 75 | `at` | 7 | 13,597,108 | 2.50% |
| 40 | `token_positions` | 69 | 13,285,602 | 2.44% |
| 37 | `subscript_read` | 2 | 12,982,316 | 2.38% |
| 106 | `is_alpha` | 44 | 11,207,103 | 2.06% |
| 710 | `infix_precedence` | 624 | 10,297,340 | 1.89% |
| 287 | `push` | 34 | 10,125,988 | 1.86% |
| 288 | `allocate_with_capacity` | 28 | 8,485,156 | 1.56% |
| 77 | `push` | 34 | 8,372,340 | 1.54% |

The largest reductions in dynamic chunk execution were:

| Chunk | Name | Before | After | Removed |
| ---: | --- | ---: | ---: | ---: |
| 482 | `token_index_starting` | 25,514,974 | 22,354,106 | 3,160,868 |
| 477 | `claim_slot_full` | 33,815,568 | 31,291,203 | 2,524,365 |
| 508 | `token_index_ending` | 17,006,619 | 15,063,341 | 1,943,278 |
| 33 | `scan` | 53,767,128 | 52,281,964 | 1,485,164 |
| 526 | `current` | 7,794,998 | 6,495,910 | 1,299,088 |
| 288 | `allocate_with_capacity` | 9,352,350 | 8,485,156 | 867,194 |
| 40 | `token_positions` | 14,112,557 | 13,285,602 | 826,955 |
| 78 | `allocate_with_capacity` | 8,109,418 | 7,578,776 | 530,642 |
| 710 | `infix_precedence` | 10,803,129 | 10,297,340 | 505,789 |

Bounds-checked collection access is the dominant remaining shape. `_check_index`, `get`,
and `subscript_read` alone account for 132.5 million dispatches, or 24.3% of
the run. The eight instructions in chunk 91 each execute 6,640,831 times; ten
instructions on the hot path through chunk 92 execute the same number of
times.

## Calibrated implementation cost

Applying the existing differential native-instruction costs to opcodes whose
shape has a usable calibration gives:

| Instruction shape | Executions | Calibration | Estimated native instructions |
| --- | ---: | ---: | ---: |
| Call + Ret pair | 41,181,523 | 543/pair | 22.36 G |
| GetField | 95,960,634 | 163 | 15.64 G |
| Cmp | 95,970,299 | approximately 145 | 13.92 G |
| Branch | 89,099,083 | approximately 145 | 12.92 G |
| Add | 36,672,386 | approximately 228 | 8.36 G |
| Const | 39,002,300 | 159 | 6.20 G |
| Mul | 12,588,537 | approximately 228 | 2.87 G |
| Jump | 15,628,565 | approximately 145 | 2.27 G |
| Div | 3,954,934 | 204 | 0.81 G |

These calibrated shapes cover 86.6% of dispatches and imply approximately
85.3 billion native instructions. The removed `Const`, `Jump`, `Sub`, and
`Branch` executions represent approximately 2.89 billion native instructions
under the same calibration, of which `Const` elimination contributes 2.78
billion. This is not a whole-run estimate: `Load`, aggregate construction,
allocation, and the remaining handlers are omitted. It does establish that
call/return, field access, and compare/branch machinery are the largest known
remaining costs.

## Findings

1. **The optimization pass is effective.** It removed 2,502 static and 18.1
   million dynamic instructions, overwhelmingly by eliminating materialized
   constants. The estimated native saving is about 2.89 billion instructions.
2. **Dynamic instruction volume remains the immediate problem.** Half a
   billion dispatches dominate before small handler-level improvements matter.
3. **Bounds-checked collection access is the first concrete remaining
   target.** A small collection-access cluster consumes almost a quarter of
   all dispatches and was unchanged by this optimization.
4. **The lexer scanner is both very large and very hot.** `scan` shrank from
   2,916 to 2,844 emitted instructions and executes 1.49 million fewer
   instructions, but still executes 52.3 million.
5. **Static code size is highly concentrated.** Ten chunks hold 37.9% of the
   image. Large `_retain` chunks closely mirror large functional chunks and
   are mostly or entirely cold in this workload.
6. **Static and dynamic importance differ sharply.** `Retain` and `GetPayload`
   consume 21.2% of the image but only 0.40% of dispatches here, while `Add`
   occupies 0.9% of the image but 6.7% of execution.
7. **Call overhead matters at this granularity.** There are 41.2 million
   call/return pairs, unchanged by the optimization and contributing an
   estimated 22.4 billion native instructions under the existing calibration.

The next investigation should explain the giant `_retain`/
`_index_iterable_get` pairs in emitted code and then inspect why parser and
lexer collection access repeatedly traverses `_check_index` and `get` instead
of keeping validated indexing within a tighter bytecode sequence.
