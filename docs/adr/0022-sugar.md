# 0022 - Syntax sugars

Status: proposed

## Allow call parens omission when the first arg is a string literal

So like, `foo "sup"` instead of `foo("sup")`

It also needs to work with trailing blocks like:

```
foo "sup" {
    // ..
}
```

## Allow parens for trailing block arg

So like, `foo({ a in })` instead of `foo { a in }`

## Positional blog args

So like, `foo { $0 * $1 }` instead of `foo { x, y in x * y }`

## Character literals

So like, `'a'`
