## syntax

Here, have some math.

```tlk
2 * 3 / 4 + 10 // I can’t do this in my head
```

ok ok, that was exciting, let’s write a function now

```tlk accumulate norun
func add(x, y) {
  x + y
}
```

Let's call the function with `Int`s:

```tlk accumulate
add(1, 2) // => 3
```

Now let's call it with `String`s:

```tlk accumulate
add("hello ", "world") // => "hello world"
```

Wow functions are polymorphic. What a world!

We can also define functions with labeled params.

```tlk
func add_one(x:) {
	x + 1
}

add_one(x: 1) // => 2 Wow. Imagine that
```

"Ok Alonzo Church" you say, "but do you have like, normal *variables*?"

We do! I'm getting to it...

```tlk
let a = 1
let b = 2
let c = a + b
c // => 3
```

## types

Ok Philip Wadler, maybe you like types? You can specify them if you want.

```tlk accumulate norun
let a: Int = 1
let b: Float = 2.0
```

They’ll be checked. 

```tlk accumulate
let c = a + b // Uh oh, type error!
```

But you can also not specify them and types will still be checked:

```tlk
let a = 1
let b = 2.0
let c = a + b
```

Functions can have type annotations as well.

```tlk norun
// it's good to be explicit sometimes
func identity<T>(x: T) -> T { x }
```

Functions are values too, and they can capture state.

```tlk
func make_counter() {
	let i = 0

	return func() {
		i = i + 1
		i
	}
}

let counter = make_counter()
counter()
counter()
counter()
```

You can also use trailing blocks for callback-y stuff.

```tlk
func twice(callback) {
	callback()
	callback()
}

twice {
	print("oh hi")
}
```

## objects

Ok Alan Kay, maybe you like objects. You know, big bags of state and behavior that are the only correct way to program.

```tlk

struct Person {
	let first_name: String
	let last_name: String

	func greet() {
		// Strings can be concat'd
		print("hi i'm " + self.first_name+ " " + self.last_name)
	}
}

let person = Person(first_name: "Pat", last_name: "N")
person.greet()
person
```

By default, structs get constructors generated automatically. But if your struct is special then you can define a custom constructor with `init`.

```tlk
struct Dog {
	let age: Int
	let count: Int

	init(age: Int) {
		self.age = age
		self.count = 0
		self
	}
}

let dog = Dog(age: 3)
dog.age
```

Ok Chewbacca, maybe you're not one for all this ceremony. You can also just define records.

```tlk 
let rec = {
    fizz: "buzz",
    count: 1000,
    greeting: func(name) { "hi " + name }
}

print(rec.fizz)
print(rec.count)
print(rec.greeting("pat"))
```

## enums / pattern matching

What about enumerations? You ever enumerate stuff? It's the best!

```tlk accumulate
enum Response {
    case ok(String), redirect(String), other(Int)
}
```

You can pattern match on `enum`s. Your `match` expression will be checked for exhaustivity.


```tlk accumulate
match Response.ok("success!") {
    .ok(string) -> string,
    .redirect(message) -> message,
    .other(code) -> "uh oh"
}
```

We can pattern match in conditionals too.

```tlk 
enum Maybe<T> {
	case some(T)
	case none
}

let value = Maybe.some(31)

if let .some(x) = value, x == 31 {
   "it's 31, bestie"
} else {
   "who even knows"
}
```

And `let else` is handy when you want to bail out early.

```tlk accumulate
func unwrap_or_zero(_ value: Optional<Int>) -> Int {
	let .some(x) = value else { return 0 }
	x
}

unwrap_or_zero(.some(42))
```

Records can be pattern matched too.

```tlk
let point = { x: 10, y: 20 }

match point {
	{ x, y: 20 } -> x,
	{ x, y } -> y
}
```

## protocols

Ok what about ~~traits~~ ~~type classes~~ ~~interfaces~~ protocols? For making ad-hoc polymorphism less ad-hoc? Yea we've got those.

```tlk accumulate norun
protocol Addable {
    func add(to other: Self) -> Self
}
```

Ok so what if we want some types to conform to it? Ez, use an `extend` block.

```tlk accumulate
// Make Int addable
extend Int: Addable {
    func add(to other: Int) -> Int {
        self + other
    }
}

// Make String addable
extend String: Addable {
    func add(to other: String) -> String {
        other + self
    }
}

print(1.add(to: 2))
print("world".add(to: "hello "))
```

Conformances are verified.

```tlk accumulate
extend Float: Addable {}
```

## effects

Check it out, we've got effects:

```tlk
// Define an effect. Effect names have the prefix `'`
effect 'fizz(x: Int) -> Int

// Handles 'fizz for as long as handler is in scope
#handle 'fizz { x in
	// This effect doesn't do much, it just returns what it was passed
	'continue x
}

// Define a function with effects. The effect list is in `'[]`. Effects
// can also be defined as `'_` and they'll be inferred.
func fizzes(x) '[fizz] {
	'fizz(x: x)
}

print(fizzes(123))
```

Ok so are effects just weird functions? I mean kind of? But you can also use them as exceptions:

```tlk
effect 'throw(msg: String) -> Never

func boom(x) {
	#handle 'throw { msg in
		print("caught: " + msg)
		return true
	}

	if x == 0 {
		'throw("boom")
	}

	false // should not run
}

boom(0)
```


There are modules too. This one isn't runnable in the browser because it spans multiple files, but it works from the CLI.

```tlk norun
// Exports.tlk
pub let a = "we can export this string"

// Main.tlk
use package::Exports::{ a }

print(a)
```

And yes, there is already some rough little HTTP stuff.

```tlk norun
let http = HTTP.Server()

http.get("/", func() {
	"hello from talk"
})

http.get("/health", func() {
	"ok"
})

print("Listening on http://localhost:3000")
http.run(3000)
```
