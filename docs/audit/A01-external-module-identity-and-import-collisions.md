# A01: External module identity and import collisions

**Severity:** High  
**Area:** module system / cross-module correctness  
**Primary files:** `src/compiling/module.rs`, `src/compiling/driver.rs`

## Summary

The current external-module identity scheme is too weak. A module's so-called stable ID is derived from **export names only**, and imported modules are stored in a map keyed by that ID. Two different modules with the same export surface can therefore collide, overwrite one another, and corrupt later lookups.

This is an architectural correctness problem, not just a naming nit.

## Evidence

### Stable module ID generation

`src/compiling/module.rs:35`

`StableModuleId::generate(exports)` hashes only the joined export keys.

That means all of these differences are ignored:

- implementation body
- type signatures
- static memory
- symbol names beyond exported keys
- semantics of exported declarations
- module path or package origin

### Import storage

`src/compiling/module.rs:383`

`ModuleEnvironment::import()` inserts the imported module into:

- `modules_by_local`
- `modules_by_name`
- `modules`

The `modules` map is keyed by `module.id`, which is the weak stable ID above.

### Local module ID allocation

`src/compiling/module.rs:384`

`let id = ModuleId::External(self.modules.len() as u16);`

This couples external module ID allocation to the current size of the stable-ID map. If two imports collide on stable ID, the map length does not grow as expected, so future local module IDs can be reused or assigned unexpectedly.

## Why this matters

This creates a class of bugs where the compiler appears to import module A, but later lookups resolve against module B.

Potential failure modes:

1. **Overwritten imported module**
   - module X and module Y export the same names
   - both hash to the same stable ID
   - importing Y overwrites the stored entry for X

2. **Wrong symbol/type/program lookup**
   - earlier `modules_by_local` entries still point at the overwritten stable ID
   - type lookup, symbol-name lookup, or program lookup now sees the wrong module

3. **ModuleId allocation skew**
   - because `self.modules.len()` undercounts collided imports, `ModuleId::External(n)` assignment can drift or be reused

4. **Cross-driver cache corruption**
   - this gets worse when modules are cached, precompiled, or reused across multiple compiler sessions

## Why it may appear fine today

A lot of current compilation seems to happen in a single-driver, single-workspace world with limited external-module import scenarios. That reduces exposure. But the weakness is still real and will become more dangerous as:

- package imports mature
- precompiled module reuse expands
- module caches become more central
- the system starts linking multiple independently compiled artifacts

## Recommended fix

## 1. Strengthen stable identity

A stable module ID should include at least one of:

- serialized module content hash
- canonical module path / package coordinate
- exported symbol names **and** their types
- program/static-memory hash

Best option: hash a canonical serialized representation of the imported module.

## 2. Decouple local `ModuleId` allocation from `self.modules.len()`

Maintain a dedicated monotonic counter for local external-module IDs.

That avoids accidental reuse when the backing map does not grow.

## 3. Add collision tests

Add tests proving that two distinct modules with the same export names do **not** alias.

Suggested cases:

- same exports, different bodies
- same exports, different type signatures
- same exports, different static memory
- same module name from different package origins

## 4. Clarify identity terminology

If an ID is based only on export keys, it is not stable in the semantic sense. Either rename it or make it truly content-derived.

## Acceptance criteria

- Importing two modules with the same export names but different contents does not overwrite either module.
- `program_for`, `lookup`, `resolve_name`, and related APIs always resolve through the intended imported module.
- Local `ModuleId` assignment is monotonic and independent of stable-ID collisions.
- Regression tests cover module-collision scenarios.

## Related issues

- [A02](./A02-interpreter-string-path-io-mismatch.md): correctness bug currently visible in tests
- [A11](./A11-clippy-not-enforced-in-ci.md): stronger CI would help catch some regression classes earlier
