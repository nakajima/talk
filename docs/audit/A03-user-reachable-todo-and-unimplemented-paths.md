# A03: User-reachable `todo!()` and `unimplemented!()` paths

**Severity:** High  
**Area:** language feature completeness / compiler robustness  
**Primary files:** `src/name_resolution/decl_declarer.rs`, `src/types/passes/inference_pass.rs`, `src/ir/lowerer.rs`, `src/types/constraints/*`, `src/ir/interpreter.rs`

## Summary

There are still multiple `todo!()` and `unimplemented!()` calls in non-test production code, including paths that are plausibly reachable from user programs. That means unsupported language features do not consistently fail as diagnostics; some instead crash the compiler or interpreter.

During audit, there were **19** `todo!()` / `unimplemented!()` occurrences in non-test `src/`.

## Evidence

Representative sites:

- `src/name_resolution/decl_declarer.rs:429`
  - `PatternKind::Struct { .. } => todo!()`
- `src/types/passes/inference_pass.rs:1638`
  - `ExprKind::RowVariable(..) => todo!()`
- `src/types/passes/inference_pass.rs:3249`
  - `PatternKind::Struct { .. } => todo!()`
- `src/ir/lowerer.rs:879`
  - `TypedPatternKind::Or(..) => unimplemented!()`
- `src/ir/lowerer.rs:903-918`
  - literal/tuple/variant/record/struct pattern lowering left as `todo!()`
- `src/types/constraints/type_member.rs:68`
  - `Ty::Constructor { .. } => todo!()`
- `src/types/constraints/projection.rs:188`
  - `unimplemented!("ambiguous: {matching:?}")`
- `src/ir/interpreter.rs:654`
  - `Instruction::Free { .. } => unimplemented!()`
- `src/ir/interpreter.rs:498`
  - unsupported reference taking is `unimplemented!()`

There are also ignored tests whose messages corroborate incomplete feature areas.

## Why this matters

For an evolving language implementation, unsupported features are fine. Crashing at runtime or in the compilation pipeline is not.

A user should get one of two outcomes:

1. the feature works, or
2. the compiler produces a clear diagnostic saying the feature is unsupported or ambiguous

The current state mixes those outcomes unpredictably.

## Specific risk areas

## 1. Pattern handling is split across stages

Struct, tuple, variant, record, and literal patterns are not uniformly implemented across:

- parsing shape representation
- declaration/name-resolution handling
- type inference
- lowering
- matcher planning

That creates a dangerous partial-support zone where syntax may parse and type information may exist, but lowering later crashes.

## 2. Ambiguous type/projection cases hard-crash

`projection.rs` uses `unimplemented!("ambiguous: ...")` for ambiguity. Ambiguity is a semantic condition, not an internal impossibility. It should become a type error or deferred resolution result.

## 3. Runtime instructions are not all implemented

If IR generation or inline IR reaches `Free` or certain reference forms, the interpreter will abort.

## Recommended policy

For every remaining placeholder, choose one of these paths explicitly:

### Path A: implement fully

Use this for features intended to be part of the supported language/runtime surface soon.

### Path B: reject early with diagnostics

Use this when the syntax or AST form exists but the compiler is not ready to support it.

That means replacing `todo!()` in user-reachable paths with something like:

- parser diagnostic
- type error
- lowering error
- runtime error

## Suggested prioritization

### First wave

- struct patterns
- tuple/variant/record/literal pattern lowering
- projection ambiguity reporting
- constructor type-member handling if user-visible

### Second wave

- row variables
- interpreter `Free`
- unsupported reference-taking modes
- unqualified lookup TODOs in lowering

## Acceptance criteria

- No user-authored program can trigger `todo!()` / `unimplemented!()` in normal parse/resolve/typecheck/lower/interpreter flows.
- Unsupported features fail with actionable diagnostics.
- Ambiguous semantic states surface as typed errors, not panics.
- Ignored tests related to placeholder behavior are either implemented, converted to diagnostic tests, or removed with rationale.

## Related issues

- [A06](./A06-interpreter-runtime-contract-is-panic-heavy.md): panic-heavy runtime behavior amplifies the impact of interpreter placeholders
- [A09](./A09-large-hotspot-files.md): the current file sizes make it harder to identify and eliminate incomplete branches systematically
