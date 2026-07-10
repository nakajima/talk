# 0024 Labeled Enum Values

Let's add the ability to name enum values. I don't think (?) they need to partipate in the row system or anything like that yet. This is the syntax I have in mind:

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

It should work with pattern matching:

```
match some_foo {
   .bar(fizz: _, buzz: s) -> { s },
   .ok(s) -> { s }
}
```
