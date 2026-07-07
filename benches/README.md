# Benchmarks

Run the VM benchmark suite with:

```sh
cargo bench --bench vm_e2e
```

The suite has two timings for each fixture:

- `e2e_*`: parse, resolve names, type check, lower, schedule, then run on the VM with `CaptureIO`.
- `scheduled_vm_*`: compile and decode bytecode once, then time VM execution only.

Use a filter when iterating on one case:

```sh
cargo bench --bench vm_e2e e2e_tight_loop
cargo bench --bench vm_e2e scheduled_vm_tight_loop
```
