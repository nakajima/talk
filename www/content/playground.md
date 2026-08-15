# Playground

## A typed interpreter

Evaluation returns the type carried by each expression—without casts.

```talk playground(gadt-evaluator)
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

## Nested behavior by scope

The same function changes behavior according to its nearest dynamic handler.

```talk playground(nested-handlers)
effect 'theme() -> String

func label() 'theme -> String { 'theme() }

func darkLabel() -> String {
	#handle 'theme { 'continue "dark" }
	label()
}

#handle 'theme { 'continue "light" }
print(label())
darkLabel()
```

## Exit across call frames

A typed effect can escape several callers without threading an error value through each one.

```talk playground(early-exit)
effect 'stop(message: String) -> Never

func deep() 'stop { 'stop(message: "caught") }
func middle() 'stop { deep() }

func attempt() {
	#handle 'stop { message in print(message) }
	middle()
	print("unreachable")
}

attempt()
```

## One effect, multiple types

A generic handler serves both `Int` and `Bool` requests while preserving their types.

```talk playground(generic-effect)
effect 'ask<T>(value: T) -> T

func request<T>(consume value: T) -> T {
	'ask(value: value)
}

#handle 'ask { value in 'continue value }
let number = request(value: 21)
let enabled = request(value: true)
if enabled { number * 2 } else { 0 }
```

## Values in types

One function specializes for different array lengths and can use that length at runtime.

```talk playground(static-values)
func length<static N: Int>(values: [Int; N]) -> Int {
	N
}

let pair: [Int; 2] = [10, 20]
let triple: [Int; 3] = [1, 2, 3]
length(values: pair) + length(values: triple)
```

## A cyclic graph

Heap values provide shared identity, mutation, and cycles when value semantics are not enough.

```talk playground(cyclic-graph)
struct Node 'heap {
	let value: Int
	let next: Node?
}

let first = Node(value: 1, next: Optional.none)
let second = Node(value: 2, next: .some(first))
first.next = .some(second)
first.value + second.value
```

## Copy-on-write snapshots

Sharing an array is cheap, but mutating one copy leaves the snapshot unchanged.

```talk playground(copy-on-write)
let current = [1, 2, 3]
let snapshot = current

current.push(4)
print(current)
print(snapshot)
snapshot.count
```

## Characters versus bytes

User-facing operations count graphemes; UTF-8 storage remains explicitly available.

```talk playground(unicode-graphemes)
let text = "héllo 👋🏽"

print(text.count())
print(text.utf8().count())
print("👨‍👩‍👧‍👦".count())
print("🇺🇳🇺🇳".count())
```

## Your type in a `for` loop

Conforming to `Iterator` makes a user-defined state machine work with built-in iteration syntax.

```talk playground(custom-iterator)
struct Countdown { let remaining: Int }

extend Countdown: Iterator {
	mut func next() -> Int? {
		if self.remaining == 0 { return .none }
		self.remaining = self.remaining - 1
		return .some(self.remaining + 1)
	}
}

for number in Countdown(remaining: 3) {
	print(number)
}
```

## A linear double spend

The checker rejects using a one-shot capability twice.

```talk playground(ownership-error)
struct Token 'linear { let id: Int }
struct Pair {
	let first: Token
	let second: Token
}

func spendTwice() -> Pair {
	let token = Token(id: 1)
	Pair(first: token, second: token)
}

spendTwice()
```
