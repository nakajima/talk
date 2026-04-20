# A09: Architectural entanglement in hotspot passes

**Severity:** Medium-high  
**Area:** maintainability / architecture / change safety  
**Primary files:** `src/ir/lowerer.rs`, `src/types/passes/inference_pass.rs`

## Summary

The main pain in this codebase is **not simply that some files are large**. Large files are a symptom. The deeper problem is that a few central abstractions own too many responsibilities at once.

In practice, this means:

- the hardest files are not just long; they are **semantically entangled**
- changes in one concern often require touching unrelated concerns
- refactors feel risky because important invariants are spread across one ambient mutable context

The clearest examples are:

- `src/ir/lowerer.rs`
- `src/types/passes/inference_pass.rs`

By contrast, other large files such as the parser may be large without creating the same level of pain if their responsibilities are still conceptually coherent.

## Reframed problem statement

A09 should not be treated as:

> "split large files into smaller files"

It should be treated as:

> "reduce the number of responsibilities each hotspot abstraction owns"

File splitting may still happen, but it should come **after** new architectural boundaries exist.

## Evidence

## 1. File size is real, but not the root cause

Largest files observed during audit included:

- `src/types/passes/inference_pass.rs` — 4619 lines
- `src/ir/lowerer.rs` — 4063 lines
- `src/parsing/parser_tests.rs` — 3857 lines
- `src/ir/interpreter.rs` — 3496 lines
- `src/parsing/parser.rs` — 3297 lines
- `src/types/types_tests.rs` — 2845 lines
- `src/parsing/formatter.rs` — 2604 lines

The important distinction is that the biggest pain points are not merely the biggest files. They are the files where many conceptual systems are interleaved.

## 2. `src/ir/lowerer.rs` is carrying too many roles at once

The current lowerer acts as all of the following simultaneously:

### Program/module lowerer
Owns and finalizes:

- `functions`
- `static_memory`
- `record_labels`
- module-level symbol/type/layout lookup

### Function CFG builder
Owns and mutates:

- current blocks
- terminators
- phis
- register allocation
- current block stack

### Environment/storage manager
Owns or coordinates:

- `Binding`
- `LValue`
- mutable locals
- captured values
- pointer-backed locals
- binding read/write behavior

### Call elaborator
Determines whether a call is:

- a direct function call
- a constructor call
- a method call
- a property/function-field call
- an enum constructor call
- an effect call
- an indirect call

### Closure/capture lowerer
Handles:

- capture env creation
- env field materialization
- captured binding rebinding

### Continuation/handler lowerer
Handles:

- handler lowering
- pending continuations
- handler-specific function termination
- continuation finalization

### Layout/query service
Provides:

- field index lookup
- variant tag lookup
- nominal lookup
- static member lookup
- instance member lookup

This is the core reason the file feels bad to change.

## 3. `lower_call` is a mixed responsibility hotspot

`lower_call` is not just emitting a call instruction. It also handles:

- constructor dispatch
- method-call dispatch
- property-call lowering
- mutating-self tracking
- indirect call fallback
- receiver writeback policy

That is too much semantic policy for one function to own.

## 4. `lower_func` is another mixed responsibility hotspot

`lower_func` is not just lowering a function body. It also handles:

- capture-environment construction
- handler-specific parameter shaping
- continuation finalization
- self-out mutation plumbing
- function registration into the program-level table

Again, multiple distinct systems meet inside one routine.

## 5. `src/types/passes/inference_pass.rs` has the same problem

The current inference pass effectively combines several passes:

### Discovery/header population
- conformances
- effects
- protocols
- associated-type requirement setup

### Body inference
- decl traversal
- stmt traversal
- expr traversal
- pattern checking/inference

### Constraint generation and solving coordination
- constraint creation
- solve orchestration
- default-type handling
- post-solve diagnostics

### Typed AST construction
- building typed nodes during traversal

### Session and side-table mutation
- symbol insertion
- call tree recording
- instantiation tracking
- `types_by_node`
- handled-effect tracking

### Synthesis work
- auto-derived body generation
- helper expression synthesis

As with the lowerer, the issue is not that helper functions are nearby. The issue is that one pass boundary is standing in for several distinct phases.

## 6. `visit_call` and `visit_func` show the entanglement clearly

### `visit_call`
It is not just typing a call. It also:

- records call-tree data
- synthesizes trailing-block functions
- handles instantiation bookkeeping
- wires call constraints
- applies protocol-member receiver logic

### `visit_func`
It is not just typing a function. It also:

- registers generics
- tracks current function for side tables
- sets up effect tracking
- infers/checks the body
- inserts the function into the environment
- collects foralls

Those are too many responsibilities for single units if the goal is long-term maintainability.

## Why this matters

This architectural entanglement has concrete costs:

- changes cross multiple conceptual systems at once
- hidden invariants are hard to see and preserve
- bugs emerge from cross-phase ambiguity rather than local mistakes
- test coverage is harder to target by subsystem
- incomplete branches are harder to inventory and eliminate
- refactors feel risky because there is no clear ownership boundary

This concern also aligns with existing design notes in the repository, especially:

- `documents/instantiation-redesign.md`
- `documents/effect-plans/02-handler-identity-and-scoping-plan.md`

Those documents already point toward the same underlying issue: cross-phase and cross-responsibility ambiguity.

## Recommended approach

## Core principle

**Introduce new architectural units first. Split files later.**

A09 should begin by creating clearer responsibilities inside the existing hotspot files, even if those new abstractions initially remain in the same file.

Only after the conceptual boundaries are real should the code be moved into separate files.

## Recommended direction for `lowerer`

### 1. Introduce a `ProgramLowerer`

Responsibilities:

- own module/program-level lowering state
- own `typed` and `config`
- own `functions`, `static_memory`, and `record_labels`
- lower roots and finalize `Program`
- create nested function-lowering contexts

This separates module-level ownership from per-function lowering state.

### 2. Introduce a `FunctionLowerer` / `FunctionCx`

Responsibilities:

- own current function blocks
- own register allocation
- own local bindings
- own flow/loop context relevant to the function
- lower expr/stmt/block into CFG
- emit instructions and terminators

A nested function should ideally be lowered by constructing a new function context, not by mutating an ambient stack on the outer module-level lowerer.

### 3. Introduce a `Place` abstraction for storage/mutation

Today, mutation/capture/self-writeback logic is spread across:

- `Binding`
- `LValue`
- param binding
- variable lookup
- lvalue lowering
- load/store helpers
- method self-tracking helpers

A dedicated storage abstraction should own operations like:

- bind symbol
- read place
- write place
- take address of place

This gives mutation, capture, and receiver writeback one conceptual home.

### 4. Separate call planning from call emission

Introduce a `CallPlan` / `ResolvedCallee`-style step.

Examples of planned forms:

- direct function call
- constructor call
- method call
- property/function-field call
- enum constructor call
- effect call
- indirect call

Then split the work into:

- call classification/elaboration
- IR emission for a resolved plan

That reduces the semantic overload currently concentrated in `lower_call`.

### 5. Isolate effect/continuation lowering

Handler and continuation lowering should not remain a cross-cutting tax on general expression lowering.

Possible directions:

- dedicated handler/continuation lowering component
- a pre-lowering transform that makes handler/continuation semantics more explicit before CFG emission

This is one of the most important architectural seams to clarify.

## Recommended direction for `inference_pass`

### 1. Split discovery/header work from body inference

A dedicated discovery/header phase should own:

- protocol discovery
- effect discovery
- conformance discovery
- associated-type requirement setup

No expression traversal.

### 2. Keep body inference focused on obligation generation

A body-inference phase should primarily own:

- decl/stmt/expr traversal
- pattern checking/inference
- typed AST construction
- constraint generation

Not every side table or post-processing concern needs to live here.

### 3. Separate solve/finalize from traversal

Constraint solving, substitution application, and unresolved-diagnostic emission should be more clearly separated from AST visitation.

### 4. Move post-inference synthesis/collection out of the core visitor where possible

Candidates include:

- auto-derived body synthesis
- call-instantiation collection
- side-table population that does not need to be interleaved with expression visitation

This reduces the number of policy systems living inside `visit_expr`, `visit_call`, and `visit_func`.

## What A09 should *not* optimize for

The following are **not** good primary success metrics:

- number of files created
- whether every 4k-line file was split
- whether helpers are shorter or more geographically separated

A file can stay large and still be healthy if its responsibility is coherent.

A file can be split into six files and still be unhealthy if the same god-object abstraction remains intact.

## Suggested implementation strategy

## Phase 1: architectural seams inside current files

For `lowerer`:

- introduce `ProgramLowerer` and `FunctionLowerer`-style abstractions
- move responsibility between impls/types without changing behavior
- add a storage/place abstraction
- add a call-planning boundary

For `inference_pass`:

- make discovery/header logic a distinct phase/unit
- isolate body inference from solve/finalize concerns
- move synthesis/collection work out of the hottest visitor paths where practical

## Phase 2: file/module layout follows architecture

Once the boundaries exist and prove useful, then split files so the filesystem reflects the conceptual model.

## Acceptance criteria

A09 should be considered successful when most of the following are true:

- major changes in call lowering do not require editing unrelated storage, continuation, and program-finalization logic at the same time
- nested function lowering no longer depends on mutating one ambient module-level lowering stack as the only model
- mutation/capture/self-writeback have a clearer single home
- call elaboration is distinct from call emission
- effect/handler lowering is isolated enough that general expression lowering no longer pays all of its complexity cost
- discovery, body inference, solve/finalize, and synthesis are clearer units on the type side
- file splitting, when it happens, reflects architectural boundaries rather than hiding the lack of them

## Non-goals

- Mechanical helper shuffling as the main A09 deliverable
- Renaming everything during the first structural pass
- Mixing this work with unrelated correctness fixes unless necessary
- Treating parser size alone as a problem if the parser is not actually a pain point

## Related issues

- [A03](./A03-user-reachable-todo-and-unimplemented-paths.md): incomplete branches are harder to eliminate when responsibilities are blurred
- [A04](./A04-lsp-full-workspace-rebuild-behavior.md): cleaner architectural boundaries make future analysis/LSP work easier to reason about
- [A02](./A02-interpreter-string-path-io-mismatch.md): current correctness work in lowering/runtime will be safer once lowering responsibilities are clearer
- [A10](./A10-repo-hygiene-and-archaeology-debt.md): documentation and repo cleanup should follow the architecture, not substitute for it
