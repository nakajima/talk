# 2. Values and Types

TalkTalk checks that values are used consistently, but it usually figures out their types for you. It's kind of a joke around these parts that you should never have to annotate a type if you don't want to. Ok maybe not a joke. A goal? Sure.

You can still write a type when it makes the code clearer or when you want the compiler to check for one specific type.

## Primitive types

The built-in scalar types are:

- `Int` - a signed machine-sized integer
- `Float` - floating-point numbers
- `Bool` - `true` or `false`
- `Byte` - an eight-bit value
- `RawPtr` - a low-level raw pointer. (you don't want to use this probably. i don't like how it works and it could go away.)
- `Void`, also written `()` - the unit type and value
- `Never` - a computation that does not return

```tlk
let count: Int = 3
let ratio: Float = 0.5
let ready: Bool = true
let nothing: () = ()

(count, ratio, ready, nothing)
```

Integer and floating-point arithmetic do not mix implicitly.

## Integer overflow

`Int` is a signed 64-bit two's-complement integer with values from `-9223372036854775808` through `9223372036854775807`. Ordinary `+`, `-`, `*`, and unary `-` trap when their mathematical result is outside that range. Division traps on zero and on the one overflowing case, the minimum value divided by `-1`.

```tlk norun
// This traps instead of silently changing sign.
9223372036854775807 + 1
```

When overflow is an expected validation result, the checked methods return `.none` instead of trapping:

```tlk
let max = 9223372036854775807

(
    max.checked_add(1),
    20.checked_mul(2),
    1.checked_div(0)
)
```

This evaluates to `(Optional.none, Optional.some(40), Optional.none)`. The checked family is `checked_add(_:)`, `checked_sub(_:)`, `checked_mul(_:)`, `checked_div(_:)`, and `checked_neg()`.

Low-level code that deliberately needs arithmetic modulo `2^64` can opt out explicitly:

```tlk
let max = 9223372036854775807
max.unchecked_add(1)
```

This evaluates to `-9223372036854775808`. The wrapping family is `unchecked_add(_:)`, `unchecked_sub(_:)`, `unchecked_mul(_:)`, `unchecked_div(_:)`, and `unchecked_neg()`. `unchecked_div` wraps the minimum-value divided by `-1` case, but division by zero still traps because it has no modular result.

Use ordinary operators by default, checked methods when failure should be data, and `unchecked_*` only when modular arithmetic is intentional.

## Strings and characters

Strings are UTF-8. A character literal uses single quotes and produces a `Character`:

```tlk
let greeting = "héllo"
let letter = 'é'

print(greeting)
print(letter)
```

`String` owns text; `Substring` refers to part of a string. Normal iteration keeps visible characters together, including emoji made from several Unicode scalars. Use `.scalars()` when you need Unicode scalar values and `.utf8()` when you need the encoded bytes:

```tlk
let text = "héllo 👋🏽"

for character in text {
    print(character)
}

for scalar in text.scalars() {
    print(scalar)
}

print(text.count())
print(text.utf8().count())
```

## Arrays, inline arrays, tuples, and records

`[T]` is a growable `Array<T>`. `[T; N]` is an exact-size `InlineArray<T, N>` whose length is part of its type:

```tlk
let values: [Int] = [1, 2, 3]
let coordinates: [Int; 4] = [1, 2, 3, 4]

print(values)
```

Tuples are positional:

```tlk
let point: (Int, Int) = (10, 20)
print(point.0)
```

Records are structural values:

```tlk
let point = { x: 1, y: 2 }
let moved = { x: 3, y: point.y }

moved
```

The corresponding record type is `{ x: Int, y: Int }`.

## Optional and result values

`T?` is shorthand for `Optional<T>`, whose cases are `.some(T)` and `.none`. `Result<S, F>` has `.ok(S)` and `.error(F)`:

```tlk
let maybe_count: Int? = .some(3)
let parsed: Result<Int, String> = .error("not an integer")

maybe_count
```

On any two-case enum, postfix `?` extracts the first case or returns the second case from the enclosing function. Postfix `!` extracts the first case or panics:

```tlk norun
func increment(_ value: Int?) -> Int? {
    let n = value?
    return .some(n + 1)
}
```

Prefer `match`, `if let`, or `let ... else` when the two outcomes need local, explicit handling.

## Function and borrow types

A function type is `(A, B) -> R`. Effects, when written, appear before the arrow:

```tlk norun
let pure: (Int) '[] -> Int
let writes: (String) 'io -> Void
let fallible: () '[io, panic] -> String
```

`&T` is a shared borrow, `&mut T` an exclusive borrow, and `*T` a statically unique owned value. Most ordinary code does not write these types because parameters borrow and values share implicitly. Basically if you have to write these, it's either a talktalk bug or a you bug.

## Type aliases

Aliases give another name to an existing type:

```tlk norun
typealias Coordinate = (Int, Int)
```

Aliases do not create a distinct nominal type; use a `struct` when identity and an API boundary matter.
