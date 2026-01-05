# talktalk

<span style="color: white;">talktalk</span> is a programming language. It kind of looks like Swift or Rust or Go if you squint. You probably shouldn’t use it. But I'm having fun making it.

Here’s some goals:

- Learning stuff: I didn’t super understand all the ins and outs of compilers. I still don’t but at least I have a way to learn now
- Fully typed everything: Types are cool.
- As much type inference as possible: I don’t know if it's a good idea. I just think it’s neat.
- Familiar-ish syntax: Haskell/ML-y syntax is beautiful. I hate it.
- Figure out cool syntax highlighting color schemes: I feel like making full programming language is the only way to do this, right? Right? Don't answer that.

Here’s some non-goals:

- Blazingly fast performance.
 I mean I’m probably not gonna litter the codebase with `sleep`s but I’m allowed to if I want.
- Everything perfectly sound and decidable.
 Is this even possible? I feel like I saw a YouTube video that said it’s not.

It has some types you may have heard of before.
```tlk
123 // Ints
1.23 // Floats
true // Booleans
"Hello 🦉" // Strings
[1, 2, 3] // Arrays
(true, 123) // Tuples?
{ fizz: "buzz" } // Records??
```

Here, have some arithmetic.

```tlk
2 * 3 + 4 / 2 // I can't do this in my head
```

Maybe you like assigning things. Like a variable?

```tlk
let a = 1
let b = 2
let c = a + b
c // => 3
```

Here’s how functions look to define and call.

```tlk
func add(x) {
	x + 1
}

add(1) // => 2 Wow. Imagine that
```

Maybe you like types? You can specify them if you want.

```tlk
let a: Int = 1
let b: Float = 2.0
let c = a + b // Uh oh, type error!
```

They’ll be checked. But you can also not specify them and types will still be checked:

```tlk
let a = 1
let b = 2.0
let c = a + b
```

We've got polymorphic functions.

```tlk
func identity(x) { x }
identity(1.23) // => 1.23 (Float)
identity(true) // => true (Bool)
```

You could write the function above explicitly too.

```tlk norun
// it's good to be explicit sometimes
func identity<T>(x: T) { x }
```

Maybe you like product types.

```tlk

struct Person {
	let firstName: String
	let lastName: String

	func greet() {
		// Strings can be concat'd
		print("hi i'm " + self.firstName + " " + self.lastName)
	}
}

Person(firstName: "Pat", lastName: "N").greet()
```

  

We've got sum types too:

  

```tlk
enum Response {
    case ok(String), redirect(String), other(Int)
}

enum Response {
    case ok(String), redirect(String), other(Int)
}

match Response.ok("success!") {
    .ok(string) -> string,
    .redirect(message) -> message,
    .other(code) -> "uh oh"
}
```

Ok what about protocols?

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
    func favoriteFood() -> Food

    // Protocols can specify default methods.
    func handleDSTChange() {
        print("what the heck where is my " + self.favoriteFood().name())
    }
}

// Ok so now we've got a Cat, which conforms to Pet
struct Cat {}

// We use `extend` blocks to mark conformances.
extend Cat: Pet {
    func favoriteFood() {
        CatFood()
    }
}

// And a Dog which conforms to Pet
struct Dog {}
extend Dog: Pet {
    func favoriteFood() {
        DogFood()
    }
}

// We can call the protocol's methods 
Cat().handleDSTChange()
Dog().handleDSTChange()
```

Check it out, we can parse effects (the rest is one big todo)

```tlk
// Define an effect. Effect names have the prefix `'`
effect 'fizz(x: Int) -> Int

// Handles 'fizz for as long as handler is in scope
@handle 'fizz { x in
	// This effect doesn't do much, it just returns what it was passed
	continue x
}

// Define a function with effects. The effect list is in `'[]`. Effects
// can also be defined as `'_` and they'll be inferred.
func fizzes(x) '[fizz] {
	'fizz(x)
}

print(fizzes(123))
```

Ok so are effects just weird functions? I mean kind of? But you can also use them as exceptions:

```tlk
effect 'throw(msg: String) -> Never

func boom(x) {
	@handle 'throw { msg in
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