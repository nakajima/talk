## syntax

Here, have some math.

```tlk
2 * 3 / 4 + 10 // I can’t do this in my head
```

ok ok, that was exciting, let’s write a function now

```tlk accumulate(func) norun
func add(x, y) {
  x + y
}
```

Let's call the function with `Int`s:

```tlk accumulate(func)
add(1, 2) // => 3
```

Now let's call it with `String`s:

```tlk accumulate(func)
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

```tlk accumulate(types) norun
let a: Int = 1
let b: Float = 2.0
```

They’ll be checked. 

```tlk accumulate(types)
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

What about enumerations? With attached values even?

```tlk accumulate(enums)
enum Response {
    case ok(String), redirect(String), other(Int)
}

let response = Response.ok("all good here, how are you?")
```

You can pattern match on `enum`s. Your `match` expression will be checked for exhaustivity.

```tlk accumulate(enums)
match response {
    .ok(string) -> string,
    .redirect(message) -> message,
    .other(_) -> "uh oh"
}
```

We can pattern match in conditionals too.

```tlk accumulate(enums)
if let .ok(message) = response {
   "ok: " + message
} else {
   "who even knows"
}
```

Records can be pattern matched too.

```tlk
let point = { x: 10, y: 20 }

match point {
	{ x, y: 20 } -> x,
	{ y, .. } -> y
}
```

One enum everyone loves is `Optional`. We love it so much there's a shorthand for it: `?`.

Let's see an example of it with `let else`, which lets you bail unless the pattern matches.

```tlk
func unwrap_or_zero(_ value: Int?) -> Int {
	let .some(x) = value else { return 0 }
	x
}

unwrap_or_zero(.some(42))
```

Speaking of bailing early, any two-variant enum can short circuit a function. Think rust's `?` operator but dumber but simpler. Elegant? One might say. But one might say a lot of things so who knows.

```tlk
// For example
enum Option<T> {
	case some(T), none
}

func maybe_increment(x: Option<Int>) -> Option<Int> {
	// if x is the second variant (none), we just return it here
	let unwrapped_x = x?
	
	// if it's the first variant (some), it's unwrapped 
	return .some(unwrapped_x + 1)
}
```
## protocols

Ok what about ~~traits~~ ~~type classes~~ ~~interfaces~~ protocols? For making ad-hoc polymorphism less ad-hoc? Yea we've got those.

Let's write a super basic protocol that let's a type be added to itself.

```tlk accumulate(protocols) norun
protocol Addable {
    func add(to other: Self) -> Self
}
```

How do we make types conform to it? With a lil `extend` declaration. Think rust's `impl Y for X` or swift's `extension X: Y`.

```tlk accumulate(protocols)
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

```tlk
extend Float: Addable {}
```

## effects

Check it out, we've got effects:

```tlk
// Define an effect. Effect names have the prefix `'`
effect 'throw<T: Showable>(_ val: T) -> ()

// Handles 'fizz for as long as handler is in scope
func rescue<T>(fn: () 'throw -> T) -> T? {
	#handle 'throw { val in
		print("oops got an error")
		print(val)
		return .none
	}

	.some(fn())
}

rescue {
	print("hello")
	'throw("oh no")
	print("this should not show up")
}
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
