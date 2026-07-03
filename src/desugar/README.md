# The desugaring phase

Runs on the freshly parsed AST, before name resolution, rewriting
surface sugar into kernel forms so that name resolution and every later
stage see a smaller language than the parser accepts. The driver calls
`desugar()` between parsing and name resolution; the name resolver no
longer rewrites the tree — it only binds names.

Each transform rewrites one kind of sugar:

- `lower_for_loops` — `for x in xs { … }` becomes a plain loop over
  `xs.iter()`, calling `.next()` and matching `some`/`none`.
- `lower_operators` — unary and binary operators become protocol
  method calls (`a + b` → `Add.add(a, b)`-shaped protocol-static
  dispatch); `&&`/`||` become `if` expressions so they short-circuit.
- `lower_funcs_to_lets` — a top-level `func f(…) { … }` becomes
  `let f = func f(…) { … }`, so the rest of the pipeline has exactly
  one kind of top-level value binding.
- `prepend_self_to_methods` — instance methods and protocol
  requirements get `self` as an explicit first parameter, so a method
  is just a function whose first argument is the receiver.

This is why the type checker has no operator rules and the lowerer
has no method-receiver special case: by the time they run, those
constructs no longer exist.
