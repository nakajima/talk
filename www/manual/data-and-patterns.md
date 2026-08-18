# 4. Data and Patterns

TalkTalk has a few ways to group data. Structs define a reusable kind of value, records are handy one-off bundles of fields, and enums describe values that can be one of several cases. Patterns let you look inside all three.

## Structs

A struct declares stored fields and methods. It receives a memberwise initializer when it does not declare its own `init`:

```tlk accumulate(person)
pub struct Person {
    pub let first_name: String
    pub let last_name: String

    pub func greeting() -> String {
        "Hello, " + self.first_name
    }
}

let person = Person(first_name: "Ada", last_name: "Lovelace")

person.greeting()
```

A custom initializer assigns fields and returns `self`:

```tlk
struct Rectangle {
    let width: Int
    let height: Int

    init(square side: Int) {
        self.width = side
        self.height = side
        self
    }
}

Rectangle(square: 12)
```

## Records

Records need no declaration and are typed by their fields:

```tlk
let user = {
    name: "Pat",
    active: true,
    greeting: func(name) { "hi " + name }
}

print(user.greeting(user.name))
```

Use records for local structural values and structs for nominal identity, conformance, constructors, or a public API.

## Enums

Enum cases may be empty or carry values:

```tlk norun accumulate(enum)
enum Response {
    case ok(String)
    case redirect(to: String)
    case other(Int)
}

let response = Response.ok("all good")
let redirect: Response = .redirect(to: "/login")
```

Case qualification can be omitted when the expected enum type is known. Payload labels are used in construction and matching.

## Exhaustive matching

`match` is exhaustive and returns a value:

```tlk accumulate(enum)
func message(_ response: Response) -> String {
    match response {
        .ok(body) -> body,
        .redirect(to: path) -> "go to " + path,
        .other(code) -> "status " + code.show()
    }
}

message(.ok("sure"))
```

Adding a case to `Response` makes an old match incomplete until the new case is handled.

Patterns include literals, bindings, `_`, tuples, enum cases, records, structs, and alternatives:

```tlk
let token = "if"
let point = { x: 10, y: 0 }

print(match token {
    "if" | "else" -> "keyword",
    _ -> "name"
})

match point {
    { x, y: 0 } -> x,
    { y, .. } -> y
}
```

A struct pattern names the type and may ignore remaining fields with `..`:

```tlk accumulate(person)
match person {
    Person { first_name, .. } -> first_name
}
```

## Pattern conditions

`if let` tests a pattern. Comma-separated condition clauses run left to right, short-circuit, and make earlier bindings visible to later clauses:

```tlk norun
if let .some(user) = lookup(), user.active {
    print(user.name)
}
```

A `let ... else` guard makes the successful bindings available after the statement:

```tlk
func unwrap_or_zero(_ value: Int?) -> Int {
    let .some(n) = value else { return 0 }
    n
}

(
    unwrap_or_zero(.some(3)),
    unwrap_or_zero(.none)
)
```

## GADTs (Generalized Algebraic Data Types)

A case may refine the enum's result type. This supports generalized algebraic data types:

```tlk
enum Expr<Returns> {
    case int(Int) -> Expr<Int>
    case string(String) -> Expr<String>
}

func evaluate<T>(_ expression: Expr<T>) -> T {
    match expression {
        .int(value) -> value,
        .string(value) -> value
    }
}

evaluate(.int(42))
```

Inside each arm, the compiler learns the result type promised by that case. That is why the `Int` arm can return an `Int` and the `String` arm can return a `String` from the same generic function.

## Further reading

TalkTalk's GADTs follow the same broad idea described in [Simple unification-based type inference for GADTs](../../papers/peyton-jones-vytiniotis-weirich-washburn-2006-gadts.pdf). The compiler combines that idea with bidirectional checking; [Complete and easy bidirectional typechecking for higher-rank polymorphism](../../papers/dunfield-krishnaswami-2021-bidirectional-typing.pdf) is useful background.
