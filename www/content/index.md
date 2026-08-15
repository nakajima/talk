<span style="color: white;">talktalk</span> is a programming language. It kind of looks like Swift or Rust, especially if you don’t know those languages.

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

```tlk error
let c = a + b // Uh oh, type error!
```
But you can also not specify them and types will still be checked:

```tlk error
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
    .other(_) -> "uh oh" // try deleting this line. i dare u.
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
Wow. Astounding.. Amazing. Simply... Extraordinary ok fine all modern languages can do that but talktalk can as well is all I'm saying.

You've also got a couple builtin enums, `Optional` and `Result`. They look like this:

```tlk norun
enum Optional<T> {
	case some(T), none
}

enum Result<T, E> {
	case ok(T), error(E)
}
```
Pretty standard stuff. I never promised you flowers. Or wait, i did? Ugh ok here have guard clauses instead, in the form of `let else`.

```tlk
func unwrap_or_zero(_ value: Int?) -> Int {
	let .some(x) = value else { return 0 }
	x
}

unwrap_or_zero(.some(42))
```
Speaking of bailing early, any two-variant enum can short circuit a function (say like, `Optional` or `Result`). Think rust's `?` operator but dumber but simpler. Elegant? One might say. But one might say a lot of things so who knows.

```tlk
func maybe_increment(x: Int?) -> Int? {
	// if x is the second variant (none), we just return it here
	let unwrapped_x = x?
	
	// if it's the first variant (some), it's unwrapped 
	return .some(unwrapped_x + 1)
}
```
What if you want to just go nuts and damn the torpedoes I know this thing is fine, stop yelling at me compiler, do you even know who my dad is?? For those cases you can use `!`, which simply unwraps the first variant and panics if it hits the second variant.

```tlk
let definitely: Int? = .some(42)
definitely!
```
# protocols
*visits Glasgow once* what about ~~traits~~ ~~type classes~~ ~~interfaces~~ protocols? For making ad-hoc polymorphism less ad-hoc? Yea we've got those.

Let's write a super basic protocol that lets a type be added to itself.

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
Protocols can also have associated types with their own constraints (basically the associated values must conform to other prototypes).

```tlk
protocol Named {
	func name() -> String
}

protocol Pet {
	associated Food: Named

	func favoriteFood() -> Food

	// a default method: every Pet gets this for free
	func describe() -> String {
		"a pet who likes " + self.favoriteFood().name()
	}
}

struct Kibble {}
extend Kibble: Named {
	func name() { "kibble" }
}

struct Cat {}
extend Cat: Pet {
	func favoriteFood() -> Kibble { Kibble() }
}

Cat().describe()
```

You can even extend a protocol itself, handing a new method to every conformer at once.

```tlk accumulate(protocols) norun
extend Addable {
	func quadruple() -> Self {
		self.add(to: self).add(to: self.add(to: self))
	}
}
```

```tlk accumulate(protocols)
1.quadruple()
```

## gadts
Not only can we pronounce "GADTs"[^1], we can use them.

```tlk accumulate(protocols)
enum Expr<Returns> {
	case int(Int) -> Expr<Int>
	case string(String) -> Expr<String>
	case add<T: Addable>(Expr<T>, Expr<T>) -> Expr<T>
}

func eval<T: Addable>(_ expr: Expr<T>) -> T {
	match expr {
		.int(i) -> i,
		.string(s) -> s,
		.add(a, b) -> eval(a).add(to: eval(b))
	}
}

print(eval(.add(.int(20), .add(.int(19), .int(3)))))
print(eval(.add(.string("hello "), .string("world"))))
```
Each arm of the `match` knows what `T` actually is, so `eval` can give you back `Int` or `String`, not `T`. Because everyone hates `T`[^2]

## effects
What are effects? Great question. I don't know. But i think they're like weird lil functions. Functions that can suspend execution, hand control off somewhere else, then return it. Think like, `async`/`await` in other languages, but more generalized.

```tlk
// Define an effect. Effect names have the prefix `'`
effect 'throw<T: Showable>(_ val: T) -> ()

// Handles 'fizz for as long as handler is in scope
func rescue<T>(fn: () -> T) -> T? {
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
Functions carry their effects as part of their signatures. In talktalk, panics are handled by the `'panic`, I/O operations are handled by the `'io` effect and memory allocations are handled by the `'alloc` effect.

Hover your mouse over the function names to see their effects.

```tlk
func could_panic(panics) {
	if panics { unreachable }
}

func does_io() {
	print("oh hi")
}

func allocates_memory() {
	let s = ""
	for i in 1..<5 {
		s = s + i.show()
	}
}
```
## collections
Arrays. They do what you think.

```tlk
let numbers = [1, 2, 3, 4, 5, 6]

for n in numbers {
	print(n * 10)
}

numbers.count
```
Subscripts work the way you would think. Unless you don't think they'd work. In which case they work but they don't work the way you don't think they don't work.

```tlk
let xs = [10, 20, 30]
print(xs[1])

xs[0] = 99
xs.show()
```
There's some generic iteration helpers. It's not all the way fleshed out yet. It will be.

```tlk
[1, 2, 3, 4, 5, 6]
	.map { $0 * 10 }
	.skip(count: 2)
	.to_array()
```
Ranges exist too.

```tlk
for i in 0..<3 {
	print(i)
}
```
There are tuples, with positional access.

```tlk
func line_col() -> (Int, Int) { (3, 7) }

let p = line_col()
p.0 + p.1
```
And the stdlib has a growable string-keyed `Dict`.

```tlk
use dict::{ Dict }

let scores = Dict<Int>()
scores.insert(key: "pat", value: 100)
scores.insert(key: "not pat", value: 85)

match scores.get(key: "pat") {
	.some(score) -> "pat scored " + score.show(),
	.none -> "who?"
}
```
## strings

Strings are unicode-correct[^3]. Iteration is by user-perceived character (extended grapheme clusters, UAX #29, etc. etc.), which means emoji can't tear.

```tlk
print("héllo 👋🏽".count())       // 7 characters
print("héllo 👋🏽".utf8().count()) // 15 bytes
print("👨‍👩‍👧‍👦".count())             // 1. a whole family!
```
Looping gives you one `Character` at a time.

```tlk
for ch in "héllo" {
	print(ch)
}
```
Ok Werner Buchholz, you want the bytes? You can call `utf8()` to get bytes.

```tlk
"héllo".utf8()
```
## ownership
talktalk has memory semantics. what are they? um, basically: everything has value semantics, sharing is implicit and cheap (refcounted, copy-on-write), and the compiler figures out the retains and releases. You mostly don't have to think about it.

```tlk
let original = [1, 2, 3]
let backup = original

original.push(4)

print(original) // [1, 2, 3, 4]
print(backup)   // [1, 2, 3], backup got a snapshot
```
Mutation happens through `mut func`s, which get exclusive access to `self`.

```tlk accumulate(ownership) norun
struct BankAccount {
	let balance: Int

	mut func deposit(amount: Int) {
		self.balance = self.balance + amount
	}
}
```

```tlk accumulate(ownership)
let account = BankAccount(balance: 100)
account.deposit(amount: 50)
account.balance
```
Function parameters borrow by default, so calling a function gives nothing up.

```tlk
func shout(message: String) {
	print(message + "!")
}

let greeting = "i said hello"
shout(message: greeting)
shout(message: greeting) // still ours
greeting
```

But sometimes a value really is one of a kind: a ticket, a token, a file handle. Mark the type `'linear` and it must be consumed exactly once. Not zero times, not two times.

```tlk
struct Ticket 'linear {
	let seat: Int

	consuming func tear() -> Int {
		self.seat
	}
}

func attend_show() -> Int {
	let ticket = Ticket(seat: 12)
	ticket.tear()
	ticket.tear() // Uh oh, one ticket can't admit two
}

attend_show()
```
Some day I'll tell you all about `consume` parameters, the `Copy`/`CheapClone` marker protocols, `Deinit` destructors, and exclusive `&mut` loans, but not today. I simply don't remember how they work atm.

## macros

Talk has hygienic macros. The declarative kind is a token template:

```tlk
macro double($x) { $x + $x }

@double(21)
```
They can introduce control flow, which functions can't.

```tlk
macro unless($cond, $body) { if $cond { () } else { $body } }

let x = 10
@unless(x > 5, print("x is beeg"))
print("still here")
```
Macro names don't capture variables, and expansions get type-checked like any other code.

The stdlib ships an HTML generation macro, written in talk itself, that parses and checks your markup at compile time:

```tlk 
use html::{ html }

let name = "<Ada & friends>"

let page = @html {
	main #content .page data-name=(name) {
		h1 { "Hello, " (name) }
		@for number in [1, 2, 3] {
			span { (number) }
		}
	}
}

print(page.into_string())
```
Interpolations get escaped, and `@for`/`@if` live right there in the markup. This one isn't runnable in the browser (the playground doesn't run procedural macros yet), but it works from the CLI.

[^1]: Generalized algebraic data types. GAAAAAA dits.

[^2]: jk `T`, we love u

[^3]: Probably!
