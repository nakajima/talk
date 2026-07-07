# Benchmarks

Run the Criterion VM benchmark suite with:

```sh
cargo bench --bench vm_e2e
```

The suite has two timings for each fixture:

- `<fixture>/end_to_end`: parse, resolve names, type check, lower, schedule, then run on the VM with `CaptureIO`.
- `<fixture>/scheduled_vm`: compile and decode bytecode once, then time VM execution only.

Use a filter when iterating on one case:

```sh
cargo bench --bench vm_e2e -- bench_tight_loop/end_to_end
cargo bench --bench vm_e2e -- bench_tight_loop/scheduled_vm
```

Criterion output and history are written under `target/criterion/`.
