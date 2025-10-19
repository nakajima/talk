# Type System

## Passes

### Type headers

First we go through the ASTs, find type annotations and generics and other
type-level decls and collect them all. At this point we've just got a bunch
of syntax nodes.

### Type resolve

Convert all the AST nodes we collected earlier into the earliest bones of the
typed program.

### Dependencies

Figure out what stuff calls what other stuff so we can avoid recursive call issues.

### Inference

Infer the binder groups gathered by dependencies, then infer everything else.

## Constraints


