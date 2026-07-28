# Frontend VM statistics

Run from the repository root:

```text
scripts/frontend-vm-stats.sh
```

The script builds the frontend candidate twice to verify its fixed point,
records optimization counts for both stages, parses every `frontend/*.tlk`
source through the candidate's `parse_file_source` export, and writes a report
here. It does not overwrite the checked-in artifact. Clean runs use
`<short-commit>.txt`; dirty runs add a fingerprint of the working tree so
distinct uncommitted changes do not overwrite one another.

Reports contain:

- the full commit and frontend artifact hashes;
- optimization rewrite counts for both bootstrap stages;
- exact emitted and executed instruction counts;
- opcode, chunk, and hot instruction-site counts;
- instrumented elapsed time and host/toolchain metadata.

Instruction counts are deterministic for a given artifact and corpus. Elapsed
time includes statistics collection and is expected to vary, so performance
claims should rely on repeated timing runs while code-generation diffs should
use the exact counts.

To compare two captures:

```text
diff -u profiles/frontend-vm/OLD.txt profiles/frontend-vm/NEW.txt
```

Use `--output-dir DIR` to write reports elsewhere.
