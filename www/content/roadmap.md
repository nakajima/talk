# What's missing

things not yet implemented, or implemented poorly

### Real I/O [missing]
`print` writes to stdout. That's the only I/O primitive. No file system access, no network (except the experimental HTTP server), no stdin.

### Standard library [missing]
No hashmaps, no sort, no JSON, no regex. The set of built-in operations is small on purpose for now, but it will need to grow.

### Explicit mutation [missing]
Everything is currently mutable without a keyword. The plan is to require `var` for mutable bindings and leave `let` as the immutable default, matching most modern languages.

### Mutable arrays [missing]
Arrays exist but don't have `push`, `pop`, or in-place mutation. You can construct new arrays by concatenation for now.

### Concurrency [missing]
No threads, no async, no fibers. The effect system is the intended foundation for async — once non-termination handling settles, effects for cooperative scheduling become a natural fit.

### Visibility modifiers [partial]
`public` is a keyword and is accepted by the parser, but nothing is private yet — all top-level declarations are exported.

### Real docs [partial]
You're looking at the beginning of them. The reference docs (a full language spec, stdlib reference) are not written.

### LSP & tooling [missing]
Syntax highlighting in the browser is fine for a demo; real editor integration (hover types, go-to-definition, diagnostics) is not built.
