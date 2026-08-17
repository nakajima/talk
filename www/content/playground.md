# Playground

## A typed interpreter

Evaluation returns the type carried by each expression—without casts.

```talk playground(gadt-evaluator)
enum Expr<Returns> {
	case int(Int) -> Expr<Int>
	case string(String) -> Expr<String>
	case add<T: Add<T>>(Expr<T>, Expr<T>) -> Expr<T>
}

func eval<T: Add<T>>(_ expr: Expr<T>) -> T {
	match expr {
		.int(i) -> i,
		.string(s) -> s,
		.add(a, b) -> eval(a).add(eval(b))
	}
}

print(eval(.add(.int(20), .add(.int(19), .int(3)))))
print(eval(.add(.string("hello "), .string("world"))))
```

## Generators are handlers

A handler that binds its resumption returns the rest of the generator as a linear value.

```talk playground(suspending-generator)
effect 'emit(value: Int) -> ()

enum Step {
	case yielded(Int, Resumption<(), Step>)
	case done
}

func generate() -> Step {
	#handle 'emit { value, k in Step.yielded(value, k) }
	'emit(value: 1)
	'emit(value: 2)
	'emit(value: 3)
	Step.done
}

func drain(consume step: Step) -> () {
	match step {
		.yielded(value, k) -> {
			print(value)
			drain(step: resume(k: k, value: ()))
		},
		.done -> {}
	}
}

drain(step: generate())
```

## Concurrency is a library

A handler schedules ordinary direct-style tasks whenever they pause.

```talk playground(cooperative-tasks)
'spawn(task: func() -> () {
	print("task started")
	'pause()
	print("task resumed")
})

print("main continues")

```

## Cancellation runs cleanup

Cancelling a suspended computation deterministically unwinds its captured frames.

```talk playground(cancel-cleanup)
let cleaned = 0

struct Guard { let id: Int }

extend Guard: Deinit {
	consuming func deinit() -> Void {
		cleaned = cleaned + 1
		()
	}
}

effect 'pause() -> ()

func work() -> () {
	let guard = Guard(id: 1)
	'pause()
	print("unreachable")
}

func reject() -> () {
	#handle 'pause { k in cancel(k: k) }
	work()
}

reject()
print(cleaned)
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
struct Node {
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

// spendTwice()
```
