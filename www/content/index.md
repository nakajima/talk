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

## results

We met `Optional` and the `?` shortcut up in the enums section. Core also ships a `Result` for when failure deserves a payload:

```tlk
func divide(a: Int, b: Int) -> Result<Int, String> {
	if b == 0 {
		return .error("cannot divide by zero, sorry")
	}
	return .ok(a / b)
}

func double_quotient(a: Int, b: Int) -> Result<Int, String> {
	// if that's an .error, we bail and return it.
	// otherwise q is the unwrapped payload
	let q = divide(a: a, b: b)?
	return .ok(q * 2)
}

print(double_quotient(a: 10, b: 2))
print(double_quotient(a: 10, b: 0))
```

And if you're feeling dangerous, `!` unwraps the first variant or panics trying:

```tlk
let definitely: Int? = .some(42)
definitely!
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
Protocols can also have associated types with their own constraints, and default methods that conformers get for free.

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
	pub func quadruple() -> Self {
		self.add(to: self).add(to: self.add(to: self))
	}
}
```

```tlk accumulate(protocols)
1.quadruple()
```
## gadts

Not only can we pronounce "gadts", we can use them.

```tlk accumulate(protocols)
enum Expr<Returns> 'heap {
	case int(Int) -> Expr<Int>
	case string(String) -> Expr<String>
	case add<T: Addable>(Expr<T>, Expr<T>) -> Expr<T>
}

func eval<T: Addable>(_ expr: Expr<T>) -> T {
	match expr {
		.int(i) -> i,
		.string(s) -> s,
		.add(a, b) -> eval(a).add(to: b)
	}
}

print(evaluate(expr: .add(.int(20), .add(.int(19), .int(3)))))
print(evaluate(expr: .add(.string("hello "), .string("world"))))
```
Each arm of the `match` knows what `T` actually is, so `evaluate` hands you an honest `Int` or `String`, not some box you have to unwrap. The academics call this a GADT. You can call it "nice".

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
		'throw(msg: "boom")
	}

	false // should not run
}

boom(0)
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
Subscripts work, and yes, you can mutate (more on that in a second).

```tlk
let xs = [10, 20, 30]
print(xs[1])

xs[0] = 99
xs
```
They're iterable, so you can do the whole lazy dance.

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
scores.insert(key: "sam", value: 85)

match scores.get(key: "pat") {
	.some(score) -> "pat scored " + score.show(),
	.none -> "who?"
}
```
## strings

Strings are unicode-correct. Iteration is by user-perceived character (extended grapheme clusters, UAX #29, etc. etc.), which means emoji can't tear.

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
The bytes are there when you need them, but you have to ask for them explicitly with `utf8()`. No integer indexing, no surprises.
## ownership

Ok Rust, maybe you like ownership. Here's the talk take: everything has value semantics, sharing is implicit and cheap (refcounted, copy-on-write), and the compiler figures out the retains and releases. You mostly don't have to think about it.

```tlk
let original = [1, 2, 3]
let backup = original

original.push(4)

print(original) // [1, 2, 3, 4]
print(backup)   // [1, 2, 3], backup got a snapshot
```
Mutation happens through `mut func`s, which get exclusive access with write-back.

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
There's more where that came from (`consume` parameters, the `Copy`/`CheapClone` marker protocols, `Deinit` destructors, exclusive `&mut` loans), but the short version is: value semantics for you, references for the compiler, no lifetime annotations, ever.
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
Names a macro introduces can't capture your variables, and expansions get type-checked like any other code. The fun part is that macros can also be whole programs. The stdlib ships an HTML macro, written in Talk itself, that parses and checks your markup at compile time:

```tlk norun
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
// <main id="content" class="page" data-name="&lt;Ada &amp; friends&gt;">
//   <h1>Hello, &lt;Ada &amp; friends&gt;</h1><span>1</span><span>2</span><span>3</span>
// </main>
```
Interpolations get escaped, and `@for`/`@if` live right there in the markup. This one isn't runnable in the browser (the playground doesn't run procedural macros yet), but it works from the CLI.
## tooling

It's a real CLI, with the usual suspects.

<div class='code-block no-run'>
<pre class='code-highlight'>talk run main.tlk     <span class="comment"># compile and run</span>
talk test             <span class="comment"># discover and run .test.tlk files</span>
talk check            <span class="comment"># type-check the whole package</span>
talk format           <span class="comment"># the formatter</span>
talk lsp              <span class="comment"># language server, at your service</span></pre>
</div>

The language server does hover, goto-definition, completion, and rename, and its inlay hints mark every spot where the compiler quietly cloned something for you. `talk setup nvim` installs the Neovim runtime files, including a Neotest adapter so you can run Talk tests from the gutter. There are also packages with lockfiles (`talk new`, `talk install`, `talk update`) if you're building something with more than one file in it.
## unsafe

If you need to touch raw memory, you can, but you have to say so. Raw pointers and friends carry an `'unsafe` effect that must be discharged lexically with `#unsafe`.

```tlk
#unsafe {
	let buf = _alloc(count: 1024)
	print("allocated a kb, doing crimes")
	_free(ptr: buf)
}
print("all cleaned up")
```

(Leaks are detected, by the way. Free your mallocs.)

There's a `net` module with raw sockets on top of this machinery, and the compiler itself can be embedded in C and Swift hosts — the iOS-flavored XCFramework build is how the playground... just kidding, the playground is wasm. But the embedding thing is real.
## modules

There are modules too. This one isn't runnable in the browser because it spans multiple files, but it works from the CLI.

```tlk norun
// Exports.tlk
pub let a = "we can export this string"

// Main.tlk
use package::Exports::{ a }

print(a)
```
## http

And yes, there is already some rough little HTTP stuff.

```tlk norun
use http::{ HTTP }

let http = HTTP.Server()

http.get(path: "/", handler: func() {
	"hello from talk"
})

http.get(path: "/health", handler: func() {
	"ok"
})

print("Listening on http://localhost:3000")
http.run(port: 3000)
```
