# The language tour

what you can actually write in it

## Primitives
Some types you've probably seen before. Tuples and records are maybe a little less common but we've got 'em.

```tlk
123              // Ints
1.23             // Floats
true             // Booleans
"Hello 🦉"       // Strings
[1, 2, 3]        // Arrays
(true, 123)      // Tuples?
{ fizz: "buzz" } // Records??
```

## Variables & expressions
The last expression in a block is its value. No semicolons required; no semicolons denied either.

```tlk
let a = 1
let b = 2
let c = a + b
c // => 3
```

## Functions
Plain, boring, good. Trailing blocks work for callback-y things too.

```tlk
func add(x) {
  x + 1
}

add(1) // => 2. Imagine that.
```

## Type annotations
Annotate when you like. Everything gets checked either way.

```tlk
let a: Int = 1
let b: Float = 2.0
let c = a + b   // uh oh, type error
```

## Generics & inference
Polymorphic by default. Spell things out if you want.

```tlk
func identity(x) { x }

identity(1.23)  // => 1.23  (Float)
identity(true)  // => true  (Bool)
```

```tlk norun
// Or be explicit:
func identity<T>(x: T) -> T { x }
```

## Closures
Closures capture their environment. They're values, so you can pass them around.

```tlk
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
Structs are fields plus methods. init blocks let you customize construction.

```tlk
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
Sum types with associated values. Match on them with if-let, let-else, or full match expressions.

```tlk
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
Protocols can have required methods, default methods, and associated types with their own bounds.

```tlk
protocol Named {
  func name() -> String
}

struct CatFood {}
extend CatFood: Named {
  func name() { "tasty cat food" }
}

protocol Pet {
  associated Food: Named
  func favoriteFood() -> Food

  func handleDSTChange() {
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
Effects are declared with a leading `'` and handled by `@handle` blocks. Useful for exceptions, async, DI — pick your poison.

```tlk
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
Are effects just weird functions? Kind of. But you can also use them as exceptions.

```tlk
effect 'throw(msg: String) -> Never

func boom(x) {
  @handle 'throw { msg in
    print("caught: " + msg)
    return true
  }

  if x == 0 { 'throw("boom") }
  false // does not run
}

boom(0)
```

<!-- bonus -->
## Modules
Modules span files. This one isn't runnable in the browser, but the CLI handles it fine.

```tlk norun
// Exports.tlk
public let a = "we can export this string"

// Main.tlk
import { a } from ./Exports.tlk
print(a)
```

<!-- bonus -->
## A rough little HTTP server
There's already some rough HTTP stuff. Don't look at it too hard.

```tlk norun
let http = HTTP.Server()

http.get("/",       func() { "hello from talk" })
http.get("/health", func() { "ok" })

print("Listening on http://localhost:3000")
http.run(3000)
```
