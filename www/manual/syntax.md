# 1. Syntax

TalkTalk uses braces around blocks of code, starts a new statement on each line, and uses `//` for comments. If the last line of a block produces a value, that value becomes the result of the block.

## Statements and blocks

A newline normally ends a statement. Semicolons are accepted but frowned upon (and the formatter will probably get rid of them anyway):

```tlk accumulate(syntax)
let width = 6
let height = 7
print(width * height)
```

Declarations, conditionals, loops, closures, and matches use braces:

```tlk accumulate(syntax)
if width == height {
    print("square")
} else {
    print("rectangle")
}
```

A function or closure returns its final expression implicitly:

```tlk
func absolute(_ n: Int) -> Int {
    if n < 0 { -n } else { n }
}

absolute(-5)
```

Use `return` for an early return.

## Comments

`//` comments run to the end of the line:

```tlk accumulate(syntax)
// Area in square units.
let area = width * height
```

## Control flow

`if` is an expression when both branches produce compatible values:

```tlk accumulate(syntax)
let label = if area > 100 { "large" } else { "small" }
```

`else if` chains are supported. A statement-position `if` may omit `else`.

`loop` is either infinite or while-like:

```tlk
let n = 3
loop n > 0 {
    print(n)
    n = n - 1
}
```

Use `break` and `continue` inside loops. `for` works through the `Iterable` and `Iterator` protocols:

```tlk
for n in 0..<3 {
    print(n)
}
```

`0..<3` is half-open; `0..3` is closed.

## Calls and member access

Calls use parentheses. Parameters without type annotations are positional, so this function is called as `repeat("ha", 3)`:

```tlk
func repeat(text, count) -> String {
    text.repeated(count)
}

repeat("ha", 3)
```

The compiler learns from the body that `text` is a `String` and `count` is an `Int`. You can add those types yourself; typed parameters use their names as call-site labels by default:

```tlk
func repeat(text: String, count: Int) -> String {
    text.repeated(count)
}

repeat(text: "ha", count: 3)
```

Use `_` to leave a parameter positional, or write a different label before its local name:

```tlk
func repeat(_ text: String, times count: Int) -> String {
    text.repeated(count)
}

repeat("ha", times: 3)
```

[Bindings and Functions](bindings-and-functions.md) covers labels and type inference in more detail.

Member access uses `.`, tuple fields use numeric members, and subscripts use brackets:

```tlk
let pair = (10, 20)
let numbers = [3, 5, 8]
print(pair.0 + numbers[1])
```

A final function argument can be written as a block after the call. Inside a short block, `$0` means the first argument, `$1` the second, and so on:

```tlk
[1, 2, 3].map { $0 * 10 }.to_array()
```

Here `map` calls the block once for each number. The compiler knows each `$0` is an `Int` because the array contains integers. You can name the argument when that reads better: `.map { number in number * 10 }`.

## Operators

The common operators are:

- arithmetic: `+`, `-`, `*`, `/`
- comparison: `==`, `!=`, `<`, `<=`, `>`, `>=`
- Boolean: `!`, `&&`, `||`
- bitwise: `&`, `|`, `^`, `~`, `<<`, `>>`
- propagation and force unwrap: postfix `?` and `!`
- conversion or existential packing: `as`

The usual precedence rules apply, so multiplication happens before addition. Strings use `+` for concatenation:

```tlk
let total = 2 + 3 * 4
let in_range = total >= 10 && total < 20
let greeting = "hello, " + "world"

print(greeting)
```

Operators can also work with user-defined types. The matching protocol, such as `Add` or `Comparable`, defines what the operator does; [Generics and Protocols](generics-and-protocols.md) explains how.

## Names and visibility

Each source file is a module. Declarations stay inside that file unless you prefix them with `pub`:

```tlk norun
pub func answer() -> Int { 42 }
```

Another file can then import `answer`. TalkTalk does not currently require type annotations on public declarations, though annotations often make a public API easier to understand. See [Modules and Packages](modules-and-packages.md) for imports and file layout.

A local name is available after its declaration and may reuse an earlier name. Function declarations are available throughout their enclosing block, including above the line where they are written.