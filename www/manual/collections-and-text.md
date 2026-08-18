# 8. Collections and Text

This chapter covers the containers and text tools used in everyday TalkTalk programs: arrays, ranges, loops, strings, and dictionaries.

## Arrays

`[T]` is a growable, copy-on-write array:

```tlk
let numbers = [10, 20, 30]
numbers.push(40)
print(numbers[1])
numbers[0] = 99
print(numbers.count)
```

Common operations include `get`, `push`, `pop`, `swap`, and indexed access. `get` returns an optional; subscript syntax is the direct form.

`[T; N]` is an `InlineArray` whose static length is part of the type. Use it for fixed-size data and static value generic APIs.

## Iteration

`for` uses `Iterable` and `Iterator`. Iterator adapters are lazy until collected:

```tlk
let result = [1, 2, 3, 4]
    .map { $0 * 10 }
    .skip(count: 1)
    .to_array()

print(result)
```

A user type can participate by conforming to `Iterator`:

```tlk
struct Countdown {
    let remaining: Int
}

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

`for x in consume values` consumes the source. `for x in mut values` iterates with writeback.

## Ranges

`lower..<upper` excludes the upper bound and `lower..upper` includes it:

```tlk
for i in 0..<3 { print(i) }  // 0, 1, 2
for i in 1..3 { print(i) }   // 1, 2, 3
```

Integer ranges conform to `Iterable` without allocating an array.

## Unicode text

Strings are UTF-8, and their user-facing character operations use extended grapheme clusters:

```tlk
print("héllo 👋🏽".count())
print("héllo 👋🏽".utf8().count())
print("👨‍👩‍👧‍👦".count())
```

Iterating a `String` or `Substring` produces `Character` values. Lower-level views are explicit:

- `.utf8()` iterates encoded bytes
- `.scalars()` iterates Unicode scalar values
- ordinary iteration produces grapheme-cluster `Character` values

The text surface includes searching, splitting, trimming, replacement, Unicode classification, case conversion, normalization, and cursor/index APIs. Index types carry provenance so an index from unrelated text cannot silently address a different string.

## String building and conversion

`StringBuilder` supports repeated construction without a chain of intermediate strings. `String` and `Substring` implement `StringMethods`; many operations therefore read naturally as methods on either owned text or a view.

`Showable` converts values for display through `.show()`, and `print` accepts any `Showable` value. `From<Source>` and `Into<Target>` describe general library conversions.

## Dictionaries

The standard library's `dict` module provides a growable string-keyed `Dict<Value>`:

```tlk
use dict::{ Dict }

let scores = Dict<Int>()
scores.insert(key: "ada", value: 100)

match scores.get(key: "ada") {
    .some(score) -> print(score),
    .none -> print("missing")
}
```

The standard library is still growing; consult the source modules for the complete current API.
