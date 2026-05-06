# The language tour

a walk through the features, with runnable examples

## Primitives
```tlk
// A tour of the built-in types. Records are structural — { x: 1 }
// and { y: 2 } have distinct types; no name is required.
123              // Ints
1.23             // Floats
true             // Booleans
"Hello 🦉"       // Strings — UTF-8
[1, 2, 3]        // Arrays — homogeneous
(true, 123)      // Tuples — fixed-arity, mixed-type
{ fizz: "buzz" } // Records
```

## Variables & expressions
```tlk
// `let` binds. Semicolons are optional.
// A block's value is its last expression.
let a = 1
let b = 2
let c = a + b
c // => 3
```

## Functions
```tlk
// `func name(params) { body }`. The last expression is the return
// value. A trailing block on a call site is passed as a closure arg.
func add(x) {
  x + 1
}

add(1) // => 2
```

## Type annotations
```tlk
// Annotations are optional. Present = checked, absent = inferred.
// Both forms produce the same errors.
let a: Int = 1
let b: Float = 2.0
let c = a + b   // type error — no implicit Int → Float
```

## Generics & inference
```tlk
// Functions are implicitly polymorphic. The compiler infers the
// most general type: `<T>(x: T) -> T` for `identity`.
func identity(x) { x }

identity(1.23)  // => 1.23  (Float)
identity(true)  // => true  (Bool)
```

```tlk norun
// Or write the generics explicitly, e.g. to document the signature:
func identity<T>(x: T) -> T { x }
```

## Closures
```tlk
// A function literal that captures variables from its enclosing
// scope. Closures are first-class — they can be returned, stored,
// and passed as arguments.
func makeCounter() {
  let i = 0
  return func() {
    i = i + 1
    i
  }
}

let counter = makeCounter()
counter(); counter(); counter() // => 3
```

## Structs
```tlk
// Nominal product type: named fields plus methods. Construction
// uses labelled arguments; methods access fields through `self`.
struct Person {
  let firstName: String
  let lastName: String

  func greet() {
    print("hi i'm " + self.firstName + " " + self.lastName)
  }
}

Person(firstName: "Pat", lastName: "N").greet()
```

## Enums & pattern matching
```tlk
// Nominal sum type: a finite set of tagged variants, each of which
// may carry data. `match` is exhaustive — forgetting a case is a
// type error.
enum Response {
  case ok(String), redirect(String), other(Int)
}

match Response.ok("success!") {
  .ok(string)    -> string,
  .redirect(msg) -> msg,
  .other(code)   -> "uh oh"
}
```

## Protocols & associated types
```tlk
// An interface a type can declare conformance to via `extend`.
// Roughly analogous to Rust traits or Swift protocols.

protocol Named {
  func name() -> String
}

struct CatFood {}
extend CatFood: Named {
  func name() { "tasty cat food" }
}

protocol Pet {
  associated Food: Named     // abstract type the conformer fills in
  func favoriteFood() -> Food

  func handleDSTChange() {   // default method
    print("where is my " + self.favoriteFood().name())
  }
}

struct Cat {}
extend Cat: Pet {
  func favoriteFood() { CatFood() }
}

Cat().handleDSTChange()
```

## Algebraic effects
```tlk
// `effect 'x` declares an operation with no built-in behavior.
// `@handle 'x { ... }` supplies behavior for handlers in scope.
// `continue v` resumes the caller with `v`.
// Effect rows (`'[fizz]`) track which effects a function invokes.

effect 'fizz(x: Int) -> Int

@handle 'fizz { x in
  continue x
}

func fizzes(x) '[fizz] {
  'fizz(x)
}

print(fizzes(123))
```

<!-- bonus -->
## Effects as exceptions
```tlk
// If a handler skips `continue` and returns from its own scope,
// the caller's continuation is discarded — that's how effects
// subsume exception handling.

effect 'throw(msg: String) -> Never

func boom(x) {
  @handle 'throw { msg in
    print("caught: " + msg)
    return true
  }

  if x == 0 { 'throw("boom") }
  false // unreachable
}

boom(0)
```

<!-- bonus -->
## Modules
```tlk norun
// Files are modules. `public` exports a top-level declaration;
// `import` pulls exports from another file. CLI only — not runnable
// in the browser.

// Exports.tlk
public let a = "we can export this string"

// Main.tlk
import { a } from ./Exports.tlk
print(a)
```

<!-- bonus -->
## A rough little HTTP server
```tlk norun
// Experimental — built on the effect system.
// Not stable. Shown because it exists.

let http = HTTP.Server()

http.get("/",       func() { "hello from talk" })
http.get("/health", func() { "ok" })

print("Listening on http://localhost:3000")
http.run(3000)
```
