# ADR 0055: Unforgeable diagnostic blame

Status: DRAFT (challenge me)

## The disease

The 2026-08-10 span audit found ~40 sites emitting diagnostics at wrong
locations, but they are all instances of one decision: **a diagnostic's
location is unvalidated data any emitter can fabricate.** Every pipeline has
its own way to fabricate it:

| pipeline | fabrication mechanism | user-visible result |
|---|---|---|
| types (generate/solve) | `CtOrigin::new(NodeID::SYNTHESIZED, ..)` accepted | diagnostic **silently dropped** — build fails with no message (`workspace.rs:841` returns `None`) |
| types | `CtOrigin` pinned to an enclosing node (callee, func, decl head) | error underlines the wrong thing; `nested()` can never narrow |
| MIR/ownership | `BackendError::new(msg, Span::SYNTHESIZED)` accepted while `FuncBuilder::current_span` is tracked and correct | line 1:1 of an **arbitrary file** (`workspace.rs:311` first-document anchor) |
| self-hosted parser | `fail(code:message:)` sends `start: -1, end: -1` across the ABI (56 sites; all lexer failures) | line 1:1; `finish` can *replace* a positioned error with a positionless one |
| frontend bridge | `ParserError::Frontend { span: None }`, `id: NodeID(file, 0)` (an id no node can have) | 0..0 |
| macro expansion | expansion-output nodes deleted from `items`; aux spans (`name_span` etc.) never rewritten | 0..0; go-to-def jumps to garbage |
| renderers | `AnyDiagnostic: Display` drops the `NodeID`; `talk run` prints `{err:?}`; `range_for_node` falls back to `TextRange::new(0,0)` | no location at all, or a fake caret at 1:1 |

Fixing the 40 sites individually is smearing. The cure must delete the
fabrication mechanisms so the bug class cannot recur.

## The cure

**Locations become witnesses, not data.** A diagnostic can only be
constructed from a proof that its location resolves, and the proof cannot be
forged. Five mechanisms, each deleting one fabrication channel:

### 1. `Blame`: the sealed location witness

A new type in `src/common/diagnostic.rs`:

```rust
pub struct Blame(NodeID);   // field private; module exposes NO raw constructor
```

- The only public constructors are on AST nodes (`node.blame()`,
  `expr.blame()`, …) and on the sink's synthetic-id path
  (`TypeArtifacts::synthetic_id(owner)` — already remapped to `owner` at
  `into_diagnostics`). Both refuse `FileID::SYNTHESIZED` by construction:
  a node with a synthesized file id has no `blame()`; you must name its
  origin instead.
- `Diagnostic<E>` and `CtOrigin::new` take `Blame`, not `NodeID`.
  `NodeID::SYNTHESIZED` stops compiling at every emission site — the type
  checker finds the audit's remaining instances for us, and each fix is
  forced to thread the real offending node.
- `Diagnostic<E>` gains `span: Option<Span>`, a *narrowing override* for
  sub-node precision (import symbol, effect name, pattern field) where the
  exact span already sits in the AST. It can only tighten, never replace,
  the `Blame` anchor: the renderer uses it when present and valid, the
  anchor otherwise. This is rustc's diagnostic-struct shape — the location
  is a required, typed field of the error, not a side channel.

### 2. MIR: location comes from tracked state, not caller choice

`BackendError::new(msg, span)` becomes private. Emission inside the builder
goes through `FuncBuilder::error(msg)` / `fail(msg)`, which stamp
`self.current_span` (already maintained at every decl/stmt/expr/pattern:
`mir/build/mod.rs:5980/6358/6733/8327`). The seven `Span::SYNTHESIZED`
sites don't get fixed — they get *deleted as a possibility*, because call
sites no longer supply spans at all. Frame-level errors (`frame_span`) keep
a separate explicit constructor so whole-function blame is a stated choice,
not a default.

### 3. Parser ABI: a failure without a position does not decode

- `Parser.tlk`: delete the positionless `fail(code:message:)`; the only
  failure constructors take start/end (the current-token span is always in
  hand: `fail_at(..., start: self.current().span.lower, ...)`). Lexer
  failures carry their (already-computed) position structurally instead of
  formatted into the message. `finish` stops masking a positioned parse
  failure with a positionless lex failure.
- Bridge: `ResultAdapter` rejects a `Fail` with negative offsets — fail
  closed, consistent with the bootstrap loader's philosophy. After the
  sweep, `ParserError::Frontend.span` becomes non-optional and
  `parser_error_range`'s 0..0 arm is deleted.

### 4. Fresh nodes inherit blame or don't exist

Post-parse node minting (desugar, macro expansion, memberwise init) must
either copy meta from the origin node or mint via `synthetic_id(owner)`.
The two macro paths that *delete* a failed nested invocation
(`macro_expansion.rs:901/:965`) instead keep it as a unit node (the
existing `replace_with_unit` shape), so `ast.find` cannot miss.
`CallSiteSpanRewriter` rewrites every span field on expanded nodes
(`name_span`, `label_span`, `mode_span`, `path_span`), not just
`node.span` — rustc solves this by carrying expansion context on the span
itself (`source_callsite()`); with our one-shot rewriter, completeness is
the equivalent guarantee.

### 5. One renderer; resolution failure is loud, never silent

- Delete the bare `AnyDiagnostic: Display`-as-UI path. `talk check`,
  `talk run`, the REPL, `talk test`, and the LSP all render through one
  function that resolves Blame → document + range (`cli/diagnostics.rs`
  becomes the only formatter). `talk run`'s `eprintln!("{err:?}")` and
  location-free type errors die here; the REPL's prefix-offset subtraction
  lives in this one place.
- `diagnostic_for_any` stops returning `Option` — every diagnostic renders
  somewhere. If resolution still misses (should now be impossible):
  **cfg(test)/debug = panic** (the balance-verifier pattern: default-on in
  tests so regressions cannot land), **release = render the message at
  file scope with no caret** — degraded but never dropped, and never a
  fake 1:1 caret pretending precision. rustc behaves the same way: a
  `DUMMY_SP` primary span suppresses the caret, not the message.
- `Span` gets a lawful `PartialEq` (compare `file_id`) so the renderer's
  file checks mean what they say; the three `bridge.rs` sites calling the
  free `span_from` (stamping `FileID(0)`) switch to `Adapter::span`; the
  driver validates a backend span's file id against the owning program
  before formatting (kills the core/stdlib → user-file misattribution).

### What this deletes

- `NodeID::SYNTHESIZED` as a value that can enter diagnostics (all uses).
- `Span::SYNTHESIZED` as a `BackendError` argument (constructor gone).
- `Fail { start: -1 }` as a representable ABI value.
- `TextRange::new(0, 0)` fallbacks in `parser_error_range` and
  `range_for_node` (the guarded-degrade path replaces them).
- The `Option` return of `diagnostic_for_any` (silent drop).
- Per-pipeline ad-hoc rendering (`{err:?}`, bare `Display`).

### Out of scope (recorded, not solved here)

- Narrowing *within* the type solver (per-argument `CtOrigin` slots so
  unification decomposition can blame `1` instead of `xs.append`) — that is
  a precision improvement on top of this integrity floor, and belongs with
  the ADR 0054 adaptation-judgment work where call-site constraints are
  being restructured anyway.
- VM runtime spans / stack traces (bytecode has no span table by design;
  separate ADR if wanted).
- Test-assert file/line (needs stdlib `testing.tlk` + harness work).

## Staging

1. **Blame + sealed constructors** (`common/diagnostic.rs`, `CtOrigin`),
   compile-error-driven sweep of every emission site. The SYNTHESIZED-drop
   emitters (recursion eq, ambient effect rows, implication residuals,
   solver overflow) get real owner nodes here.
2. **MIR `FuncBuilder::error`** + delete public `BackendError::new`.
3. **Parser.tlk sweep** (56 `fail` sites + lexer position + `finish` masking),
   `talk bootstrap`, bridge fail-closed, non-optional `Frontend.span`.
4. **One renderer** + `Option`-ectomy + debug-panic backstop + REPL offset.
5. **Span Eq/Hash + bridge `span_from` + driver file-id validation.**
6. **Macro node preservation + full sub-span rewrite.**

Each stage lands green independently; stage 1 is the enforcement floor —
after it, a new emission site *cannot* compile with a fabricated location.

Every stage adds pinned tests asserting the diagnostic's resolved
`file:range` (not just its message), plus one corpus-wide invariant test:
compile the reference corpus, assert every emitted diagnostic resolves to a
nonzero range in the document that produced it.

## Citations (per decision)

- **Location as a required typed field of the error** — rustc's
  `#[derive(Diagnostic)]` structs with `#[primary_span]`: errors are
  structs whose primary span is a declared field, separated from emission
  logic ([rustc-dev-guide: Diagnostics](https://rustc-dev-guide.rust-lang.org/diagnostics.html),
  [rustc_macros::derive.Diagnostic](https://doc.rust-lang.org/stable/nightly-rustc/rustc_macros/derive.Diagnostic.html)).
- **Location as a provably-resolvable tree pointer** — rust-analyzer
  diagnostics carry `InFile<SyntaxNodePtr>` / `InFile<AstPtr<_>>`: a
  file-qualified pointer that resolves against the tree by construction
  ([hir/src/diagnostics.rs](https://github.com/rust-lang/rust-analyzer/blob/master/crates/hir/src/diagnostics.rs),
  [SyntaxNodePtr](https://rust-lang.github.io/rust-analyzer/syntax/type.SyntaxNodePtr.html)).
- **Sentinel spans are a recognized bug source; degrade loudly, don't
  fabricate** — rustc suppresses the caret (not the message) for
  `DUMMY_SP`; rustdoc migrated a dummy-span-returning API to `Option` to
  stop sentinel leakage ([rust#100299](https://github.com/rust-lang/rust/pull/100299));
  EOF diagnostics were fixed by anchoring to the previous token's end
  rather than a dummy span ([rust#145350](https://github.com/rust-lang/rust/pull/145350)).
- **Macro-expanded code must blame the call site via span machinery, not
  per-field luck** — rustc spans carry `SyntaxContext` with
  `source_callsite()` resolving to the expansion's call site
  ([rustc_span::Span](https://doc.rust-lang.org/stable/nightly-rustc/rustc_span/struct.Span.html),
  [rustc-dev-guide: Macro expansion](https://rustc-dev-guide.rust-lang.org/macro-expansion.html)).
- **Default-on verifier in cfg(test)** — precedent in this repo: the
  wave-2 MIR balance verifier (memory: wave2-stream4-balance-verifier),
  which turned silent lowering leaks into test failures.
