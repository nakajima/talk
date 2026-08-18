# 12. Testing

Put tests in files ending with `.test.tlk`, then run `talk test`. TalkTalk finds the tests in your package, runs them, and reports which assertions passed or failed.

## A first test

A generated package contains:

```tlk norun
test("example") {
    @assert(1 + 1 == 2)
}
```

Run it with:

```sh
talk test
```

The runner discovers `.test.tlk` files under the package's `tests/` and source trees. You can also name files or directories explicitly:

```sh
talk test tests/math.test.tlk
talk test tests/
```

## Assertions

`@assert` is the normal assertion form. Because it is a macro, a failure can include the original condition text.

The test prelude also exposes functions for dynamically built checks:

```tlk norun
test("positive") {
    assert(4 > 0)
    assertMessage(2 + 2 == 4, "addition should work")
}
```

A failed assertion records a test failure rather than panicking the entire test runner.

## Selecting and automating tests

Run one exact test name:

```sh
talk test --filter positive
```

Emit machine-readable output for editor or CI integration:

```sh
talk test --json
```

Compilation diagnostics fail the test command before test execution. A finished run exits nonzero when any assertion failed.

## Testing effects and failures

Tests can define and handle effects like any other source. Prefer exposing side effects behind a small effect and installing a deterministic handler in a test; this keeps the function under test in direct style while avoiding a real host dependency.

Cleanup remains deterministic in tests. `Deinit` hooks run on normal scope exit, abortive effect paths, and cancellation, so resource-lifecycle behavior can be tested directly.

## Core and standard-library tests

The repository keeps core tests beside their modules as `core/*.test.tlk` and standard-library tests as `stdlib/*.test.tlk`. Reference programs and expected diagnostics under `tests/reference/` pin language behavior in more detail than application tests normally need.
