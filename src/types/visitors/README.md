# Ok so the visitors go like this:

## DefinitionVisitor

Just figures out high level type info like what is generic and what's not. This way we can figure out what specifically needs resolution later on.

It also gathers members of nominal types. We store these instead of relying on HasField constraints bebecause I clearly have not read enough papers to know how to combine generics with HasField.

We're also trying out letting DefinitionVisitor handle init resolution. So like calling Person() would get replaced by the init in the DefinitionVisitor to make things easier at inference time?

## Hoister
Hoists named things so they can be accessed out of order. In practice these things have all been visited by the DefinitionVisitor so we just use those.

## InferenceVisitor

Infers stuff. For things that are TypeSchemes with generics, it first creates canonical type variable substitutions, then visits the thing (func or struct
or whatever.) Then stores a new type scheme with constraints pointed at the canonical type vars. When we instantiate one of these schemes (at call time or
whenever), we create new "instantiated" type variables for each of the canonical type variables, then generate new constraints for these new instantiated
variables.

## Types of vars:

### TypeParameter

A generic. May or may not be named

### TypeVar

A thing where we don't know what it is. There are some kinds:

- **Canonical(TypeParameter)**: When we're in a generic context, we create these type variables which later get substituted by Instantiated variables
- **Instantiated**: The replacements for those above.

