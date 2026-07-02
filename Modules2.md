# new module system

```tlk
// Import symbol from a relative path
use { hello } from ./peer

// Import top-level exported symbol from a module
use { hello } from some-module

// Import non-top level exported symbol from a module
use { world } from some-module/world

// Qualify a relative symbol
./peer/hello

// Qualify a module symbol
some-module/world
```
