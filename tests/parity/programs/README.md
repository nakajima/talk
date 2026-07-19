# Baseline program output oracles

These files freeze the byte-for-byte stdout produced by the last green backend
at tag `pre-backend-reset-2026-07-13` (`96249e71`). Each `<name>.stdout` matches
`tests/programs/<name>.tlk`.

Capture procedure:

```text
git worktree add --detach <baseline> pre-backend-reset-2026-07-13
cargo build --bin talk
talk run tests/programs/<name>.tlk > <name>.stdout 2> <name>.stderr
cargo test --test programs
```

Observed on 2026-07-14:

- all 16 commands exited with status 0;
- all 16 commands wrote empty stderr;
- the archived `tests/programs.rs` suite passed 17 tests;
- that test build ran both the evaluator and VM and applied the baseline
  allocation/object balance policy;
- every output file includes the exact trailing newline emitted by the baseline.

The files are behavior oracles, not authority over accepted semantic changes.
If ADR 0032 deliberately changes a program's behavior, preserve this baseline
file and record the reviewed replacement oracle separately rather than silently
overwriting history.

`handlers.stdout` preserves the baseline CLI's debug rendering `I64(0)` for the
program's final non-Void result. TOOL-06 is now dispositioned: new `talk run`
uses Talk syntax and prints `0`, never the runtime enum name. Unit produces no
final-result line. The reviewed replacement oracle is retained separately at
`tests/parity/reviewed-programs/handlers.stdout`; the historical baseline file
is intentionally unchanged.
