# The desugaring phase

Runs on freshly parsed ASTs, before name resolution, rewriting surface
sugar into kernel forms so name resolution and every later compiler stage
see a smaller language than the parser accepts. The driver calls
`desugar()` at the start of `Driver<Parsed>::resolve_names()`; the name
resolver itself only declares and binds names.

The transforms run in this order:

- `lower_for_loops` — `for pattern in xs { ... }` becomes a block that
  creates an iterator, loops, calls `.next()`, and matches
  `Optional.some(pattern)` / `Optional.none` (`break`). Rvalue iterables
  are first bound to a synthetic source binding so their storage lives for
  the loop.
- `lower_funcs_to_lets` — a top-level `func f(...) { ... }` becomes
  `let f = func f(...) { ... }`, so later stages have one kind of
  top-level value binding.
- `lower_operators` — unary and binary operators become protocol-static
  member calls (`a + b` becomes an `Add.add(a, b)`-shaped call); `&&` and
  `||` become `if` expressions so they short-circuit.
- `lower_if_to_match` — expression-position `if c { t } else { e }`
  becomes a boolean `match` with `true` and `false` arms. Statement `if`
  stays as statement control flow.
- `prepend_self_to_methods` — instance methods and protocol requirements
  get `self` as an explicit first parameter, so a method is represented as
  a function whose first argument is the receiver.

This is why the type checker has no operator rules, no expression-`if`
rule, and no implicit-method-receiver rule. Statement-level control flow
(`if`, `loop`, `break`, `continue`, `return`, handler scopes) remains for
HIR/MIR, flow analysis, and lowering to handle explicitly.
