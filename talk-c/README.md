# talk-c

C ABI facade for embedding Talk in Swift/iOS and other C-compatible hosts.

Build for the host:

```sh
cargo build -p talk-c --release
```

Build for iOS after installing the targets:

```sh
rustup target add aarch64-apple-ios aarch64-apple-ios-sim
cargo build -p talk-c --release --target aarch64-apple-ios
cargo build -p talk-c --release --target aarch64-apple-ios-sim
```

The public C header is `include/talk_c.h`.

Most language-service APIs return typed opaque result handles, not JSON:

- diagnostics: `TalkDiagnostics *`
- hover: `TalkHover *`
- completions: `TalkCompletions *`
- inlay hints: `TalkInlayHints *`
- highlighting: `TalkHighlightTokens *`
- goto definition: `TalkLocationResult *`
- rename: `TalkWorkspaceEditResult *`
- program/REPL evaluation: `TalkEvalResult *`

Each handle has status/error accessors plus typed count/get/value accessors. String fields are returned as `TalkStringRef` slices borrowed from the handle and remain valid only until the handle is freed. Swift wrappers should copy them into Swift `String` values immediately.

String/raw-byte APIs still use `TalkResult`:

- `talk_format_utf8`
- `talk_highlight_html_utf8`
- `talk_render_lowered_utf8`
- `talk_render_bytecode_utf8`
- `talk_compile_bytecode_utf8`

Always free returned values with the matching free function, e.g. `talk_diagnostics_free`, `talk_hover_free`, or `talk_result_free`.
