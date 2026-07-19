# Types

- Metatypes
- Const generics
- Dependent types????????????

# Macros?????
- Maybe something like #_assert(true) where we force an underscore because this api sucks
- then the implementation can be like:
    #macro _assert { args in
      // args == [true] 
      if args.count == 1 {
        assert(args[0], "default message")
      } else {
        assert(args[0], args[1])
      }
    }

# Grammar

- Bitwise operators
- Force type annotations in conformance extends
- Subscriptable protocol for allowing thing[idx]
- Character literals
- #[attributes]

# Stdlib

- Array
- String
- Dictionary
- File/Directory apis
- Process
- `cove stdlib --all`?

# Optimizations

- Benchmark suite first

# Bugz
- Jump to def for enum variants doesn't go to the correct place
- LSP suggests import sources for modules that only imported symbols. it should only show where they are defined

# ggez

- semantic tokens should indicate ownership better
- formatter shouldn't automatically put every case on a new line
- unqualified enum implicit return values shouldn't get turned into calls by the parser/formatter
- unreachable

# Random

- Clean up diagnostics stuff. Maybe a DiagnosticSet object that tracks sevs separately so we don't need to do filtering all the time?

# else

- We should rewrite Talk of the Town in talktalk itself
