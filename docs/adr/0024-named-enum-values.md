# 0024 - Labeled enum payloads

Status: accepted; implemented (2026-07-09)

## Decision

Enum payload fields may have labels. Payload labels do not participate in the
row system. The source syntax is:

```
enum Foo {
    case bar(fizz: Int, buzz: String)
    case ok(String)
}
```

Construction:

```
Foo.bar(fizz: 123, buzz: "sup")
```

The same labels are used in pattern matching:

```
match some_foo {
   .bar(fizz: _, buzz: s) -> { s },
   .ok(s) -> { s }
}
```
