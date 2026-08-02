# talk-ffi

Language-neutral C ABI for embedding the Talk compiler, bytecode adapter,
and VM in Swift, C, and other C-compatible hosts. TalkSwift is one binding
over this interface, not its owner.

The public C header is `include/talk_ffi.h`. Its preamble is the interface
contract: the ABI version, status and error conventions, the exact free
function matching every returned buffer and opaque handle, how long
borrowed `TalkStringRef` and view data remain valid, synchronous-callback
rules, thread affinity, UTF-8 requirements, and panic containment. Read it
before writing a new binding.

`tests/smoke.c` is a minimal C client that exercises representative
one-shot and handle APIs and frees every result; `cargo test -p talk-ffi`
compiles, links, and runs it against the host static library. Use it as
the template for future bindings.

Build for the host:

```sh
cargo build -p talk-ffi --release
```

Build for iOS after installing the targets:

```sh
rustup target add aarch64-apple-ios aarch64-apple-ios-sim
cargo build -p talk-ffi --release --target aarch64-apple-ios
cargo build -p talk-ffi --release --target aarch64-apple-ios-sim
```

Most language-service APIs return typed opaque result handles, not JSON:

- diagnostics: `TalkDiagnostics *`
- hover: `TalkHover *`
- completions: `TalkCompletions *`
- inlay hints: `TalkInlayHints *`
- highlighting: `TalkHighlightTokens *`
- goto definition: `TalkLocationResult *`
- rename: `TalkWorkspaceEditResult *`
- program/package/REPL evaluation: `TalkEvalResult *`
- package tests: `TalkTestResult *`

Each handle has status/error accessors plus typed count/get/value accessors. String fields are returned as `TalkStringRef` slices borrowed from the handle and remain valid only until the handle is freed. Swift wrappers should copy them into Swift `String` values immediately.

String/raw-byte APIs still use `TalkResult`:

- `talk_package_create_utf8`
- `talk_package_install_utf8`
- `talk_package_install_with_provider_utf8`
- `talk_format_utf8`
- `talk_highlight_html_utf8`
- `talk_render_lowered_utf8`
- `talk_render_bytecode_utf8`
- `talk_compile_bytecode_utf8`

`talk_package_create_utf8` creates a new package directory with an executable `main` target, an empty lockfile, and a passing starter test. `talk_package_install_utf8`, `talk_package_run_utf8`, and `talk_package_test_utf8` use the built-in host provider. It uses `git` for Git sources and `curl` for tarball downloads; tar extraction and checksum validation run inside Talk.

`talk_package_provider_new` creates a tar-only source provider. Its callback writes the downloaded archive to the supplied `TalkPackageArchiveSink` and finishes or fails the sink synchronously. Use the `_with_provider_utf8` install/run/test functions with it. Git dependencies fail clearly because this provider has only the `TALK_PACKAGE_SOURCE_TAR` capability.

Always free returned values with the matching free function, e.g. `talk_diagnostics_free`, `talk_test_result_free`, `talk_hover_free`, or `talk_result_free`.
