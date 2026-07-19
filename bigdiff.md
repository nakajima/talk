# Big diff follow-ups

Status: deferred from the ownership/effect PR

These changes were removed to keep the current PR focused. Reintroduce them as
independent follow-ups so each has a small interface, focused tests, and no
ownership/effect coupling.

## 1. Nested `@_ir` type resolution

### Scope

Restore recursive name resolution and lowering for type arguments embedded in
inline IR instructions, such as `retain Wrapper<String> %0`.

### Work

- In `src/name_resolution/name_resolver.rs`, drive the complete inline-IR type
  annotation tree instead of resolving only the outer nominal name.
- In `src/lower/splices.rs`, preserve nominal generic arguments when converting
  a `TypeAnnotation` to the checked type used by retain/drop walks.
- Apply the current specialization theta when an annotation names a generic
  parameter.
- Reject unsupported annotation shapes with the existing explicit lowering
  diagnostic rather than silently erasing generic arguments.

### Acceptance tests

- Name resolution resolves both names in `Outer<Inner>` inside `@_ir`.
- Lowering `retain Wrapper<String> %0` walks the instantiated `String` field.
- A generic type parameter in an inline-IR annotation resolves through theta.
- Unsupported nested annotation forms fail with a lowering diagnostic.

### Files

- `src/name_resolution/name_resolver.rs`
- `src/name_resolution/name_resolver_tests.rs`
- `src/lower/splices.rs`
- `src/lower/lower_tests.rs`

## 2. Parser diagnostic range improvement

### Scope

Give `ParserError::ParamModeBorrowConflict` the range of the conflicting borrow
annotation instead of the file-wide fallback range.

### Work

- Add the error-specific mapping in `src/analysis/workspace.rs`.
- Use the parser-provided annotation span directly; do not re-scan source text.
- Verify the result through the workspace diagnostic interface used by the LSP.

### Acceptance tests

- `func f(fn: (consume &Foo) -> Foo) {}` highlights exactly `&Foo`.
- The diagnostic kind and message remain unchanged.
- The range remains correct when the annotation is not on the first line.

### Files

- `src/analysis/workspace.rs`

## 3. Tour documentation refresh

### Scope

Reintroduce the documentation-only cleanup in `www/content/tour.md` without
mixing it with compiler behavior changes.

### Work

- Present primitive types in a compact table.
- Restore the `Person` struct and generated memberwise-initializer example.
- Use the canonical `talk` code-fence language consistently.
- Preserve the existing informal tone.
- Ensure the file ends with a newline and renders correctly in the site build.

### Acceptance checks

- The website build succeeds.
- Markdown tables and code fences render correctly.
- Every shown syntax example passes `talk check` where it is intended to be a
  complete program.

### Files

- `www/content/tour.md`

## Landing order

The follow-ups are independent. Preferred order:

1. Parser diagnostic range improvement.
2. Nested `@_ir` type resolution.
3. Tour documentation refresh.

Each should land as its own PR. None should modify ownership flow, checked MIR,
effect unwinding, or runtime accounting.
