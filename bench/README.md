# Benchmark corpus

Eight self-contained programs, one per workload archetype the
profiling passes surfaced (see the plan's waves 9–11 and the
published profile report). Each prints one deterministic value;
`bench_corpus_runs` in `tests/talk_tests.rs` pins the outputs.

| Program | Archetype | Dominant opcodes |
| --- | --- | --- |
| `arith.tlk` | tight scalar loop | Add/Mul/Div/Cmp with RK constants, Branch/Jump |
| `fields.tlk` | struct construction + field reads | RecordNew (direct), GetField |
| `dispatch.tlk` | enum construction + match | VariantNew, GetTag/GetPayload, branch chains |
| `calls.tlk` | call machinery (fib) | Call/Ret, frame pool, argument copies |
| `strings.tlk` | UTF-8 grapheme iteration | Load, the `_utf8_decode` leaf family |
| `arrays.tlk` | Array growth + bounds-checked reads | Alloc/Load/Store, inlined `get` |
| `drops.tlk` | per-iteration owned buffers | shared drop functions, Free, retain balance |
| `effects.tlk` | resumable effects in a loop | PushHandler/FindHandler, CallIndirect |

## Analyzing a program

```sh
talk run   bench/arith.tlk          # execute
talk mir   bench/arith.tlk          # the backend IR after mir_build
talk bytecode bench/arith.tlk       # lowered VM instructions (RK operands as k[n])
talk build bench/arith.tlk -o /tmp/a.img && perf stat talk run-image /tmp/a.img
```

`talk mir` renders the IR before inlining/regalloc; `talk bytecode`
is the final form the VM executes. For opcode-mix and pass-timing
probes, see the "Method" section of the profile report — they are
temporary, env-gated, and not kept in tree.
