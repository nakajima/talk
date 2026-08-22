# 4. Data and Patterns

TalkTalk has a few ways to group data. Structs define a reusable kind of value, records are handy structural bundles of fields, and enums describe values that can be one of several cases. Patterns let you look inside all three.

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

Records need no declaration. A literal's field labels and value types determine its type:

```tlk
let user = {
    name: "Pat",
    active: true,
    greeting: func(name) { "hi " + name }
}

print(user.greeting(user.name))
```

The type of `user` is `{ active: Bool, greeting: (String) -> String, name: String }`. Source order is not part of record identity: labels, not positions, connect fields. The compiler stores a closed row in a canonical label order, so `{ x: 1, y: 2 }` and `{ y: 2, x: 1 }` have the same type.

Field access can infer an *open* record row. This function does not require one declared record shape; it accepts any record with an `x` field:

```tlk norun
func x_coordinate(point) {
    point.x
}

print(x_coordinate({ x: 3, y: 4 }))
print(x_coordinate({ name: "origin", x: 0 }))
```

The inferred parameter is approximately `{ x: T, ..row }`, and the return type is `T`. The hidden row tail means "possibly more fields." Each call fills in both `T` and the remaining fields, and compilation specializes the function for the concrete closed row used there.

Uses constrain field types in both directions:

```tlk norun
func shifted(point) {
    point.x + 1
}

shifted({ x: 41, label: "answer" })
```

`+ 1` constrains `point.x` to support integer addition, so the call resolves `x` as `Int`. Accessing several fields adds all of them to the required row. A record missing a required label, or with an incompatible field type, is a type error.

Open-row inference is currently a frontend feature with incomplete executable-backend coverage, so these two generic examples are shown as non-runnable reference code. Closed record literals, field reads, writes, and concrete record patterns execute on the supported targets.

Record patterns are structural too. `..` allows fields the pattern does not mention:

```tlk
let point = { x: 10, y: 0, label: "start" }

match point {
    { x, y: 0, .. } -> x,
    { y, .. } -> y
}
```

Use records for local structural values. Prefer structs when a value needs nominal identity, declared conformance, constructors, methods as a public API, or a stable exported name. [Type Inference Reference](type-inference#record-rows) describes row inference and specialization in detail.

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
