# Module paths

```tlk
// Import all public symbols from a local source module.
use package::peer

// Import selected local symbols.
use package::peer::{ hello }

// Import a sibling module.
use super::sibling::{ hello }

// Import selected exports from an external package.
use some_module::{ hello }

// Qualify a local or package symbol.
package::peer::hello
some_module::hello
```
