# Types

- Auto borrowing/cloning (i guess like, swift style instead of rust style). Basically it's a pain to have to worry about cloning ffor types where it'd fine to do so. It'd be better to suppress cloneability and only have errors in those cases than have to worry about ownership everywhere. Also if we could auto-borrow for things to avoid copies, that'd be cool too.
- For this one, we should probably just disregard or borrow s rather than rejeect it?
    .a -> {
      let moved = s
      s.length
    }
- Const generics
- Dependent types????????????

# Stdlib

- Array
- String
- Dictionary
- `cove stdlib --all`?

# Optimizations

- Benchmark suite first

# Syntax

- Subscriptable protocol for allowing thing[idx]

# Random

- Clean up diagnostics stuff. Maybe a DiagnosticSet object that tracks sevs separately so we don't need to do filtering all the time?

# else
