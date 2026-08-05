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

```tlk accumulate
let rec = {
    fizz: "buzz",
    count: 1000,
    greeting: func(name) { "hi " + name }
}

print(rec.fizz)
print(rec.count)
print(rec.greeting("pat"))
```

What about enumerations? You ever enumerate stuff? It's the best!

```tlk accumulate
enum Response {
    case ok(String), redirect(String), other(Int)
}
```

You can pattern match on `enum`s. Your `match` expression will be checked for exhaustivity.


```tlk
match Response.ok("success!") {
    .ok(string) -> string,
    .redirect(message) -> message,
    .other(code) -> "uh oh"
}
```

We can pattern match in conditionals too.

```tlk accumulate
enum Maybe<T> {
	case some(T)
	case none
}

let value = Maybe.some(31)

if let .some(x) = value, x == 31 {
    print("it's 31, bestie")
} else {
    print("who even knows")
}
```

And `let else` is handy when you want to bail out early.

```tlk accumulate
func unwrap_or_zero(_ value: Maybe<Int>) -> Int {
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

Ok what about ~~traits~~ ~~type classes~~ ~~interfaces~~ protocols?

```tlk
// Ok so we've got some different pet foods here
struct CatFood {}
struct DogFood {}

// And we've got a protocol `Named` that just knows how
// to get names of things.
protocol Named {
    func name() -> String
}

// Let's make the pet foods conform to Named
extend CatFood: Named {
    func name() { "tasty cat food" }
}

extend DogFood: Named {
    func name() { "tasty dog food" }
}

// So far so good, right? Ok now let's add a Pet protocol.
protocol Pet {
    // Protocols can have associated types with their own constraints.
    associated Food: Named

	// This protocol has one required method. It just returns
	// the associated type Food for this pet.
    func favorite_food() -> Food

    // Protocols can specify default methods.
    func handle_DST_change() {
        print("what the heck where is my " + self.favorite_food().name())
    }
}

// Ok so now we've got a Cat, which conforms to Pet
struct Cat {}

// We use `extend` blocks to mark conformances.
extend Cat: Pet {
    func favorite_food() {
        CatFood()
    }
}

// And a Dog which conforms to Pet
struct Dog {}
extend Dog: Pet {
    func favorite_food() {
        DogFood()
    }
}

// We can call the protocol's methods 
Cat().handle_DST_change()
Dog().handle_DST_change()
```

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
public let a = "we can export this string"

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
