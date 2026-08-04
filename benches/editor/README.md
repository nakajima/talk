# Editor latency benchmarks

These benchmarks pin the two costs that determine editor responsiveness:
canonical frontend work inside one process and complete LSP requests across
stdio.

## Fixed cases

| Case | Focus | Purpose |
| --- | --- | --- |
| `small` | `benches/editor/fixtures/small.tlk` | Startup and fixed request overhead |
| `core` | `core/Array.tlk` | Multi-file Core workspace |
| `syntax` | `stdlib/syntax/Parser.tlk` | Large self-hosted frontend workspace |

The benchmark output records byte counts and raw samples. Source changes are
therefore visible rather than silently being treated as performance changes.

## Frontend benchmark

```sh
cargo bench --bench editor_latency -- --warmups 1 --iterations 5
```

Run one case while iterating:

```sh
cargo bench --bench editor_latency -- --case syntax --warmups 1 --iterations 3
```

It measures:

- `parse_lenient_focus`: the canonical lenient parse used by editor analysis;
- `semantic_tokens_focus`: lexing, parsing, classification, and LSP token encoding;
- `workspace_rebuild`: a fresh parse, name-resolution, type, diagnostic, and
  ownership analysis for the case's editor workspace.

The benchmark runs in one optimized process. Warmups initialize the embedded
frontend session and process-wide Core/stdlib artifacts before samples are
recorded.

## LSP benchmark

Build the exact binary first, outside the measurement:

```sh
cargo build --release --bin talk
scripts/lsp-latency-bench.py --warmups 1 --iterations 5
```

Run one case:

```sh
scripts/lsp-latency-bench.py --case syntax --warmups 1 --iterations 3
```

It opens a real stdio LSP session and measures:

- `completion_after_edit`;
- `definition_after_edit`;
- `semantic_refresh_after_edit`.

Each sample alternates one trailing ASCII space through a full-document
`didChange`. The edit is semantically neutral but creates a new document
revision, exercising the same invalidation and analysis path as an ordinary
edit. Completion and definition are requested immediately. Each sample waits
for the corresponding semantic-token refresh before the next sample, so work
from adjacent samples cannot overlap.

## Recording and comparing results

Both benchmarks write newline-delimited JSON to stdout and progress to stderr:

```sh
mkdir -p profiles/editor
cargo bench --bench editor_latency -- --iterations 5 \
  > profiles/editor/frontend-before.ndjson
scripts/lsp-latency-bench.py --iterations 5 \
  > profiles/editor/lsp-before.ndjson
```

Each result includes median, nearest-rank p95, and every raw sample. Compare raw
samples rather than only medians. Use the same binary, source revision, power
profile, warmup count, iteration count, and idle machine for an A/B. Run the A
and B close together; sustained frontend workloads can be affected by thermal
throttling.
