# Talk Compiler

Talk is a compiler and interpreter for a statically-typed programming language (.tlk files) featuring generics, structural typing with row polymorphism, an effects system, and pattern matching.

## Commands

```bash
cargo test                              # Run all tests (required before completing tasks)
cargo check                             # Quick compile check
cargo run -- run examples/HelloWorld.tlk  # Run a .tlk file
cargo run -- check src.tlk              # Type check a file
cargo run -- ir src.tlk                 # Show IR output
cargo run -- lsp                        # Start language server
```

## Project Structure

- `src/parsing/` - Lexer, parser, AST generation
- `src/name_resolution/` - Symbol resolution and imports
- `src/types/` - Type inference, constraint solving, effects
- `src/ir/` - Intermediate representation and interpreter
- `src/compiling/` - Compiler pipeline orchestration
- `src/lsp/` - Language server protocol
- `core/` - Standard library (.tlk files)
- `examples/` - Example programs

## Type System

The type system uses constraint-based inference with:
- **Row polymorphism** for structural typing of records
- **Effects tracking** via effect annotations on function types
- **Unification** via `ena` crate's union-find implementation

Key files: `src/types/type_session.rs`, `src/types/type_error.rs`, `src/types/effects_tests.rs`

## IR System

The `build.rs` script generates implementation code from `src/ir/instruction.rs`. Instruction variants are documented with special comments that drive code generation.

Key files: `src/ir/instruction.rs`, `src/ir/interpreter.rs`, `src/ir/lowerer.rs`

## Testing

Test files are collocated with modules as `*_tests.rs`:
- `src/parsing/parser_tests.rs`
- `src/types/types_tests.rs`, `src/types/effects_tests.rs`
- `src/ir/lowerer_tests.rs`
- `src/name_resolution/name_resolver_tests.rs`

Test helpers in `src/test_utils.rs`. Always add tests when modifying behavior.

## Coding Conventions

- **No panics in prod**: `unwrap()`, `expect()`, `panic!()`, `todo!()` forbidden outside tests
- **Nightly Rust**: Uses many unstable features (box_patterns, try_blocks, etc.)
- **Error types**: Domain-specific errors (ParserError, TypeError, IRError)
- **Collections**: Prefer `FxHashMap`/`FxHashSet` over std
- **Tracing**: Use `tracing::instrument` and `tracing::debug!` for observability
