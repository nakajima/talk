# 3. Bindings and Functions

Variables use `let`, functions use `func`, and both usually work without many type annotations. This chapter covers changing values, naming function arguments, passing functions around, and writing methods.

## Bindings and assignment

Declare a local with `let` and optionally ascribe its type:

```tlk
let score = 10
score = score + 5

let title: String = "TalkTalk"

score
```

Every `let` binding can be assigned again; TalkTalk has no separate `var` keyword. Assignment also works with writable fields, tuple positions, and supported subscripts. Function signatures still control whether a function may change a value passed in from its caller: that is what `mut` means in the parameter and method examples below.

Destructuring uses patterns. A refutable pattern needs `else`:

```tlk
let (x, y) = (3, 4)
let .some(value) = Optional.some(42) else { return }

(x, y, value)
```

## Defining functions

A function may infer parameter and return types locally:

```tlk
func add(x, y) { x + y }

add(1, 2)
```

Annotations are recommended on public boundaries:

```tlk
pub func clamp(_ value: Int, min lower: Int, max upper: Int) -> Int {
    if value < lower { return lower }
    if value > upper { return upper }
    value
}

clamp(12, min: 0, max: 10)
```

The final expression is returned implicitly. `return` without a value returns `Void`.

## Argument labels

The declaration determines each call-site label:

```tlk
func positional(x) { x }                  // positional(1)
func labeled(x:) { x }                    // labeled(x: 1)
func typed(x: Int) { x }                  // typed(x: 1)
func renamed(with value: Int) { value }   // renamed(with: 1)
func bare(_ value: Int) { value }         // bare(1)

(
    positional(1),
    labeled(x: 2),
    typed(x: 3),
    renamed(with: 4),
    bare(5)
)
```

A bare inferred parameter is positional. Adding a colon chooses a same-name label. A typed parameter is labeled unless `_` suppresses it.

## Parameter modes

Plain parameters are shared borrows by default. The complete set is:

- `borrow value: T` - explicit shared borrow
- `mut value: T` - exclusive, writable access
- `consume value: T` - ownership supplied to the callee
- `consume mut value: T` - owned and locally writable

A `mut` argument must name a writable place and is marked at the call:

```tlk
func bump(mut value: Int) {
    value = value + 1
}

let n = 1
bump(value: mut n)
n // 2
```

Ordinary and consuming arguments have no call-site marker. For shareable values, `consume` does not necessarily make the caller's name unusable: the compiler retains a snapshot when the caller has a later use.

## Closures

Closures can use an explicit `func` form or a block form:

```tlk
let increment = func(x: Int) -> Int { x + 1 }

increment(41)
```

Block closures are especially convenient as call arguments. The `$0`, `$1`, and so on shorthand is available when the surrounding call supplies the closure's parameter types:

```tlk
let doubled = [1, 2, 3].map { $0 * 2 }.to_array()

print(doubled)
```

Functions can capture surrounding values. A final closure argument can move outside the parentheses:

```tlk
func twice(_ body: () -> Void) {
    body()
    body()
}

twice {
    print("hello")
}
```

Functions are values, so they can be stored in records and structs, passed as arguments, and returned. If a stored function uses an effect, such as asking for input, it uses the handler that is active when you call it. It does not permanently remember the handler from where it was created. See [Effects](effects.md) for the full model.

## Methods

Method signatures have an implicit `self`; do not declare it as a parameter. A plain method shares `self`, `mut func` may update it, `consuming func` takes it, and `static func` is called through the type:

```tlk
struct Counter {
    let value: Int

    mut func increment() {
        self.value = self.value + 1
    }

    static func zero() -> Counter {
        Counter(value: 0)
    }
}

Counter.zero().value
```
