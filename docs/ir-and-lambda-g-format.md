# Talk IR and lambda G format

This page explains the formats you see while debugging the backend.
It uses plain language first, then gives the exact printed shapes.

There are three related things:

| Name | Where you see it | What it is |
|---|---|---|
| `@_ir` | Inside Talk source files | A way for core library code to ask for one low-level built-in operation. |
| lambda G, written `λ_G` in code | `talk lower file.tlk` and `show_ir` | Talk after type checking, before bytecode. This is the main compiler middle form. |
| VM bytecode | `talk ir file.tlk` | Numbered instructions that the interpreter runs. |

The flow is:

```text
Talk source
  -> type checked Talk
  -> lambda G listing       (`talk lower`)
  -> bytecode listing       (`talk ir`)
  -> interpreter
```

Use this rule of thumb:

- If you are debugging a strange `%0`, `$0`, or `@_ir`, read section 1.
- If you are debugging `func main(k: fn(...))`, `var main.k`, `br`, or
  `switch`, read section 2.
- If you are debugging `r0`, `chunk 0`, `jump`, or `ret`, read section 3.

## 1. `@_ir`: low-level operations in Talk source

`@_ir` is source syntax. It is not the same thing as the lambda G output
from `talk lower`.

The core library uses `@_ir` for things Talk should not expose as normal
language features: raw memory loads, raw memory stores, integer math,
float conversion, and direct writes to the IO layer.

### Basic shape

```talk
@_ir { %? = add Int %0 %1 }
@_ir(value, ptr) { store Element $0 $1 }
@_ir(fd, buffer, count) { %? = io_write $0 $1 $2 }
```

Read that as:

- `@_ir(...)` before the braces gives extra input values.
- The braces contain one low-level operation.
- `%?` means "the value produced by this whole `@_ir` expression".
- `%0`, `%1`, and so on read the current function's parameters.
- `$0`, `$1`, and so on read the values from the `@_ir(...)` input list.

### `%n`: current function parameters

In this core operator method:

```talk
func +(rhs: Int) -> Int {
    @_ir { %? = add Int %0 %1 }
}
```

`%0` is the method receiver, `self`.
`%1` is `rhs`.

So the operation means: add `self` and `rhs`, and make that the result of
this expression.

### `$n`: values passed into the splice

```talk
let sum: Int = @_ir(2, 3) { %? = add Int $0 $1 }
sum
```

Here `$0` is `2` and `$1` is `3`.

`talk lower` prints:

```text
func main(k: fn(int)) {
  let_x(add(2, 3))

  func let_x(int) {
    var main.k(var let_x)
  }
}
```

The `@_ir` operation became `add(2, 3)` in lambda G.

The values in `@_ir(...)` must be simple enough for the lowerer to place
inside one expression. Literal values, variables, field reads, tuples,
records, enum values, strings, function values, and other simple `@_ir`
expressions are accepted. Calls and control flow are not accepted there.

### Type words

Many `@_ir` operations include a type word:

```talk
%? = add Int %0 %1
%? = load Element $0
store Byte $0 $1
```

The word tells lowering which lambda G type or memory width to use.
Inside generic code, a word such as `Element` is replaced with the real
type for the concrete version being compiled.

Example:

```talk
func _load<Element>(ptr: RawPtr) -> Element {
    @_ir(ptr) { %? = load Element $0 }
}
```

If `_load<Byte>` is used, `Element` becomes `byte`.
If `_load<Int>` is used, `Element` becomes `int`.

Important: `@_ir` is trusted. The normal type checker does not prove the
operation is safe. The surrounding Talk type tells the expression what
result type it should have, and the low-level operation must match that.

### Operations that work today

The parser accepts only the operation names that lower to lambda G today.
Use normal Talk syntax for literals, calls, records, field access, and
assignment/update paths.

| Source form | Plain meaning |
|---|---|
| `%? = cmp T a == b` | Compare two values. Also supports `!=`, `<`, `<=`, `>`, `>=`. Result is `Bool`. |
| `%? = add T a b` | Add two values. |
| `%? = sub T a b` | Subtract `b` from `a`. |
| `%? = mul T a b` | Multiply two values. |
| `%? = div T a b` | Divide `a` by `b`. |
| `%? = trunc value` | Convert `Float` to `Int` by dropping the fractional part. |
| `%? = itof value` | Convert `Int` to `Float`. |
| `%? = alloc T count` | Allocate enough raw bytes for `count` values of type `T`. Result is `RawPtr`. |
| `%? = load T addr` | Read one value of type `T` from raw memory. |
| `store T value addr` | Write one value to raw memory. |
| `%? = gep T addr index` | Compute the address of item `index` in an array of `T`. |
| `copy T from to length` | Copy `length` bytes from one raw address to another. Core normally uses `Byte` here. |
| `%? = io_write fd buf count` | Write `count` bytes from `buf` to file descriptor `fd`. Returns an integer: non-negative means success, negative means an error code. |

### Memory examples

Allocate space for ten bytes:

```talk
let ptr: RawPtr = @_ir(10) { %? = alloc Byte $0 }
```

Store and load one integer:

```talk
@_ir(value, ptr) { store Int $0 $1 }
let value: Int = @_ir(ptr) { %? = load Int $0 }
```

Find the address of the third `Int` in an array:

```talk
let item_ptr: RawPtr = @_ir(base, 2) { %? = gep Int $0 $1 }
```

`gep Int base 2` means `base + 2 * size(Int)`.
Since `Int` is 8 bytes in raw memory, this means `base + 16`.

### IO example

Core uses this to write a Talk string's bytes:

```talk
public func write_string(fd: Int, s: String) -> Int {
    @_ir(fd, s.base, s.length) { %? = io_write $0 $1 $2 }
}
```

Read it as:

1. Use `fd` as `$0`.
2. Use `s.base` as `$1`.
3. Use `s.length` as `$2`.
4. Write those bytes.
5. Return the integer result.

## 2. Lambda G: the `talk lower` format

Lambda G is the compiler's main middle form. It looks like plain nested
functions, but it has one unusual rule:

**Functions do not return to their caller. They send their result to a
function that was passed in.**

That extra function is usually named `k` in the output. You can read `k`
as "where to send the answer".

### A first example

Talk source:

```talk
// no-core
func id(a: Int) { a }
id(123)
```

Lambda G output:

```text
func main(k: fn(int)) {
  id(123, var main.k)
}

func id(a: int, k: fn(int)) {
  var id.k(var id.a)
}
```

How to read it:

- `main(k: fn(int))` means `main` receives one hidden result function.
  When the program has an `int` answer, it calls `k` with that answer.
- `id(123, var main.k)` calls `id` with `123` and `main`'s result
  function.
- `var id.a` means "the `a` parameter of `id`."
- `var id.k(...)` means "send the result to `id`'s result function."

### Function headers

A lambda G function prints like this:

```text
func name(param: type, another: type) -> result_type {
  body
}
```

Most functions do not show `-> result_type`:

```text
func name(param: type) {
  body
}
```

When the result type is not printed, it means the function sends control
somewhere else and does not come back. Internally this result type is
called `never`.

Common header shapes:

| Header | Plain meaning |
|---|---|
| `func main(k: fn(int))` | `main` will eventually send an `int` to `k`. |
| `func then(())` | `then` takes no useful value. It is used as a branch body. |
| `func f(x: int) -> int` | Rare direct function shape: takes `int` and produces `int`. |
| `func f#12(...)` | Generated or duplicate name. `#12` keeps the printed name unique. |

### `var name` and `var name.field`

Each function has one input value. When the function has several printed
parameters, that one input value is a bundle of all parameters. The
printer hides most of that detail.

| Printed text | Meaning |
|---|---|
| `var main` | The whole input value of `main`. |
| `var main.k` | The `k` part of `main`'s input. |
| `var add.a` | The `a` part of `add`'s input. |
| `var let_x` | The single value received by helper function `let_x`. |

### Calls

A call looks normal:

```text
add(2, 3, var main.k)
```

But remember: the last argument is often the result function.
So this means:

1. Run `add` with `2` and `3`.
2. When `add` has an answer, it should call `var main.k`.

A return is just a call to the result function:

```text
var id.k(var id.a)
```

Read that as:

1. Take `id`'s `a` value.
2. Send it to `id`'s `k` function.

### `let` example

Talk source:

```talk
// no-core
let x: Int = 1
let y: Int = 2
x + y
```

Lambda G output:

```text
func main(k: fn(int)) {
  let_x(1)

  func let_x(int) {
    let_y(2)

    func let_y(int) {
      add(var let_x, var let_y, var main.k)
    }
  }
}

func add(self: int, rhs: int, k: fn(int)) {
  var add.k(add(var add.self, var add.rhs))
}
```

How to read it:

1. `main` sends `1` to helper function `let_x`.
2. Inside `let_x`, `var let_x` is the value of `x`.
3. `let_x` sends `2` to helper function `let_y`.
4. Inside `let_y`, `var let_y` is the value of `y`.
5. The final call adds `x` and `y`, then sends the answer to `main.k`.

So nested helper functions are often just "do the next line after this
value is available."

The separate `func add` at the bottom is the lowered form of `+` for
integers. The innermost `add(var add.self, var add.rhs)` is the built-in
integer addition operation.

### `if` example

Talk source:

```talk
// no-core
if true { 1 } else { 2 }
```

Lambda G output:

```text
func main(k: fn(int)) {
  br(true, then, else)

  func then(()) {
    var main.k(1)
  }

  func else(()) {
    var main.k(2)
  }
}
```

How to read it:

- `br(condition, then, else)` chooses one of two helper functions.
- `then(())` sends `1` to `main.k`.
- `else(())` sends `2` to `main.k`.
- `()` means there is no useful value to pass to the branch body.

### `match` example

Talk source:

```talk
// no-core
enum Maybe {
    case definitely(Int)
    case nope
}

let maybe = Maybe.definitely(1234)

match maybe {
    .definitely(_) -> 22,
    .nope -> 0
}
```

Lambda G output:

```text
func main(k: fn(int)) {
  let_maybe(variant_new(Maybe, 0, 1234))

  func let_maybe(variant(Maybe)) {
    switch(get_tag(var let_maybe), case_definitely, case_nope, match_failed)
  }

  func case_definitely(()) {
    arm()
  }

  func case_nope(()) {
    arm#5()
  }

  func arm() {
    var main.k(22)
  }

  func arm#5() {
    var main.k(0)
  }
}

func match_failed(()) {
  unset
}
```

How to read it:

- `variant_new(Maybe, 0, 1234)` builds the first enum case with payload
  `1234`.
- `get_tag(var let_maybe)` reads which enum case it is.
- `switch(...)` picks a helper function based on that tag.
- `case_definitely` runs the first match arm.
- `case_nope` runs the second match arm.
- `match_failed` is the fallback if no arm matches. For a complete match
  it should not run. Since it is a deliberate trap path, its body is
  printed as `unset`.

### Types in lambda G

| Printed type | Plain meaning |
|---|---|
| `int` | 64-bit signed integer. |
| `float` | 64-bit float. |
| `bool` | Boolean. |
| `byte` | One byte. |
| `ptr` | Raw memory address. |
| `()` | No useful value. |
| `never` | This function does not produce a value for its caller. |
| `(int, bool)` | A bundled value with an `int` and a `bool`. |
| `fn(int)` | Function that takes an `int` and does not come back. Usually a result function. |
| `fn(int) -> bool` | Function that takes an `int` and directly produces a `bool`. Rare in lowered Talk. |
| `boxed(Point)` | Heap value for a struct, string, array, or other record-like value. |
| `variant(Maybe)` | Enum value. |
| `cell(int)` | Mutable box holding an `int`. Used for mutable variables that must be shared. |

Raw memory sizes:

| Type | Raw memory size |
|---|---:|
| `byte` | 1 byte |
| `int`, `float`, `bool`, `ptr` | 8 bytes |
| `boxed(...)`, `variant(...)`, bundled values | 8-byte handle |
| `()`, `never`, `fn(...)`, `cell(...)` | Not stored directly in raw memory |

### Expressions in lambda G

| Printed form | Plain meaning |
|---|---|
| `123`, `1.5`, `true`, `false` | Literal value. |
| `7b` | Byte value 7. |
| `()` | No useful value. |
| `static+12` | Address of bytes stored with the program, starting at byte 12. |
| `slot#3` | Runtime cell slot. Usually only appears while using the reference evaluator. |
| `foo` | The function named `foo`. |
| `var foo` | The input value of function `foo`. |
| `var foo.x` | The `x` part of function `foo`'s input. |
| `callee(a, b)` | Call `callee` with `a` and `b`. |
| `(a, b)` | Bundle `a` and `b` together. |
| `x.0` | First item from a bundled value. |
| `op(a, b)` | Built-in operation. Examples below. |

### Built-in operations in lambda G

| Printed operation | Plain meaning |
|---|---|
| `add`, `sub`, `mul`, `div` | Arithmetic. Also used for simple pointer math when the values are pointers/offsets. |
| `cmp_eq`, `cmp_ne`, `cmp_lt`, `cmp_le`, `cmp_gt`, `cmp_ge` | Compare two values and produce `bool`. |
| `trunc` | Convert `float` to `int` by dropping the fractional part. |
| `i_to_f` | Convert `int` to `float`. |
| `alloc` | Allocate raw bytes. |
| `load` | Read from raw memory. |
| `store` | Write to raw memory. |
| `copy` | Copy raw bytes. |
| `record_new(Name, fields...)` | Build a heap record/struct/string/array value. |
| `get_field(index, record)` | Read a field from a heap value. |
| `set_field(index, record, value)` | Make a copy of a heap value with one field changed. |
| `variant_new(Name, tag, payloads...)` | Build an enum value. |
| `get_tag(value)` | Read which enum case a value holds. |
| `get_payload(index, value)` | Read an enum payload. |
| `cell_new(value)` | Create a mutable box. |
| `cell_get(cell)` | Read a mutable box. |
| `cell_set(cell, value)` | Write a mutable box. Produces `()`. |
| `br(condition, then, else)` | Pick one of two branch helper functions. |
| `switch(tag, arm0, arm1, ..., fallback)` | Pick a helper function by number. Used for matches. |
| `io_write`, `io_read`, `io_open`, ... | Talk runtime IO operations. |
| `io_perform` | Run an IO request value through the default IO path. |

### Data shapes you will see

#### Anonymous records

Anonymous records are printed as bundled values. Fields are sorted by
field name before lowering.

A source value like this:

```talk
{ y: true, x: 1 }
```

is stored in a fixed order, so field reads can become simple item reads.

#### Structs, strings, and arrays

These show up as `boxed(Name)` values.

You may see:

```text
record_new(Point, (), ())
get_field(0, var let_p)
set_field(1, old_point, new_y)
```

Read these as:

- build a `Point` value;
- read field 0;
- make a new `Point` value with field 1 changed.

Updates are value updates. They do not mutate an existing struct value in
place unless the value is inside a mutable cell.

#### Enums

Enums show up as `variant(Name)` values.

```text
variant_new(Maybe, 0, 1234)
get_tag(var maybe)
get_payload(0, var maybe)
```

Read these as:

- build enum case number 0 with payload `1234`;
- read the case number;
- read payload 0.

#### Mutable variables

Mutable variables that must be shared show up as cells:

```text
cell_new(0)
cell_get(var cell)
cell_set(var cell, 1)
```

Read these as:

- make a box with value `0`;
- read the box;
- write `1` into the box.

### Why helper functions are nested in the printout

Internally, lambda G stores all functions in one flat list. The printer
nests helper functions to make ownership easier to read.

A helper is printed inside `main` when it uses values from `main`, such
as `var main.k`. That means:

```text
func main(k: fn(int)) {
  ...

  func helper(...) {
    var main.k(...)
  }
}
```

The helper needs `main`'s `k`, so the printer places it under `main`.

### What the verifier checks

After lowering, and after each later rewrite, the compiler checks the
lambda G program again.

It checks:

- every call receives the right kind of value;
- every function body matches the function's printed result type;
- every `var name` points to a real function input;
- helper-function ownership has no impossible cycles.

In practice: if the lowerer builds broken lambda G, the compiler should
fail at verification instead of silently producing bad bytecode.

## 3. VM bytecode: the `talk ir` format

`talk ir` prints what the interpreter will run. This format is lower
level than lambda G.

The bytecode uses numbered temporary slots called registers: `r0`, `r1`,
`r2`, and so on. Each function call gets its own set of registers.

### Basic listing shape

```text
chunk 0: main (arity 0, regs 5)
  0: const r2 <- consts[0]
  1: branch r2 ? 4 : 2
  2: const r3 <- consts[1]
  3: ret r3
  4: const r4 <- consts[2]
  5: ret r4
```

Read this as:

- `chunk 0: main` is bytecode function 0, named `main`.
- `arity 0` means it takes 0 normal arguments. `arity` just means
  argument count.
- `regs 5` means this call frame has registers `r0` through `r4`.
- The number at the start of each line is the instruction position.
- `consts[0]` means a value from the module's constant table.
- `ret r3` returns the value in `r3` to the caller.

### `if` example from lambda G to bytecode

Talk source:

```talk
// no-core
if true { 1 } else { 2 }
```

Lambda G:

```text
func main(k: fn(int)) {
  br(true, then, else)

  func then(()) {
    var main.k(1)
  }

  func else(()) {
    var main.k(2)
  }
}
```

Bytecode:

```text
chunk 0: main (arity 0, regs 5)
  0: const r2 <- consts[0]
  1: branch r2 ? 4 : 2
  2: const r3 <- consts[1]
  3: ret r3
  4: const r4 <- consts[2]
  5: ret r4
```

How to read the bytecode:

1. Put `true` into `r2`.
2. If `r2` is true, jump to instruction 4. Otherwise jump to instruction
   2.
3. Instruction 2 returns `2`.
4. Instruction 4 returns `1`.

The lambda G helper functions `then` and `else` became jump targets in
one bytecode chunk. No real function call is needed for them.

### `@_ir` example from source to bytecode

Talk source:

```talk
let x: Int = @_ir(2, 3) { %? = add Int $0 $1 }
x
```

Lambda G:

```text
func main(k: fn(int)) {
  let_x(add(2, 3))

  func let_x(int) {
    var main.k(var let_x)
  }
}
```

Bytecode:

```text
chunk 0: main (arity 0, regs 4)
  0: const r1 <- consts[0]
  1: const r2 <- consts[1]
  2: add r3 <- r1, r2
  3: move r0 <- r3
  4: jump 5
  5: ret r0
```

How to read it:

1. Put `2` in `r1`.
2. Put `3` in `r2`.
3. Add them into `r3`.
4. Move the result into `r0`, the slot used for `x`.
5. Return `r0`.

### Common bytecode instructions

| Instruction shape | Plain meaning |
|---|---|
| `const rX <- consts[N]` | Copy a constant into register `rX`. |
| `move rX <- rY` | Copy register `rY` into `rX`. |
| `add rX <- rA, rB` | Put `rA + rB` into `rX`. Similar for `sub`, `mul`, `div`. |
| `cmp_eq rX <- rA, rB` | Compare values and put `true` or `false` in `rX`. Similar for other comparisons. |
| `trunc rX <- rY` | Convert float in `rY` to int in `rX`. |
| `itof rX <- rY` | Convert int in `rY` to float in `rX`. |
| `tuple rX <- (...)` | Build a bundled value. |
| `extract rX <- rY.N` | Read item `N` from a bundled value. |
| `record_new rX <- Name(...)` | Build a heap record/struct/string/array value. |
| `get_field rX <- rY.N` | Read field `N`. |
| `set_field rX <- rY with .N = rZ` | Make a copy of `rY` with field `N` changed to `rZ`. |
| `variant_new rX <- Name#tag(...)` | Build an enum value. |
| `get_tag rX <- rY` | Read enum case number. |
| `get_payload rX <- rY.N` | Read enum payload `N`. |
| `cell_new rX <- rY` | Create a mutable box holding `rY`. |
| `cell_get rX <- rY` | Read mutable box `rY`. |
| `cell_set rX <- rY` | Write a mutable box. |
| `alloc rX <- rY bytes` | Allocate `rY` raw bytes. |
| `load_i64 rX <- [rY]` | Read an `Int` from raw address `rY`. There are also `load_byte`, `load_f64`, `load_bool`, `load_ptr`, and `load_boxed`. |
| `store_i64 [rX] <- rY` | Write an `Int` to raw address `rX`. There are matching store forms for other memory kinds. |
| `copy [rTo] <- [rFrom], rLen bytes` | Copy raw bytes. |
| `io_write rX <- rFd, rBuf, rCount` | Run an IO write through the VM's IO layer. Other IO operations have similar names. |
| `call rX <- name(args...)` | Call another bytecode chunk. Put its result in `rX`. |
| `closure rX <- name capturing (...)` | Build a function value with saved outside values. |
| `env_get rX <- env[N]` | Read a saved outside value inside a closure. |
| `call_indirect rX <- rFunc(args...)` | Call a function value from a register. |
| `jump N` | Continue at instruction `N`. |
| `branch rCond ? N1 : N2` | Jump to `N1` if true, else `N2`. |
| `switch rTag -> [N0, N1] default Nf` | Jump by number, usually for `match`. |
| `ret rX` | Return value in `rX`. |
| `trap "message"` | Stop with a deliberate compiler/runtime hole. |

### How lambda G turns into bytecode

Lambda G has many tiny helper functions. The bytecode builder avoids
turning every helper into a real call.

It uses this simple split:

| Lambda G function kind | Bytecode result |
|---|---|
| Real function, `main`, or function value | A bytecode `chunk`. It has its own register frame. |
| Branch body, match arm, loop body, or "next line" helper | A jump target inside an existing chunk. |
| Call to the current result function | `ret`. |
| Call to a function value stored in a variable | `call_indirect`. |

So this lambda G:

```text
br(true, then, else)
```

can become this bytecode:

```text
branch r2 ? 4 : 2
```

And this lambda G:

```text
var main.k(1)
```

can become this bytecode:

```text
ret r3
```

## 4. Which format should I look at?

| Problem | Best format |
|---|---|
| Parser accepted or rejected an `@_ir` snippet | Source `@_ir` syntax and parser tests. |
| A low-level operation picked the wrong type or memory width | `@_ir` plus `talk lower`. |
| A Talk expression lowered to the wrong control flow | `talk lower`. |
| A function sends its result to the wrong place | `talk lower`. |
| A match chooses the wrong arm | `talk lower` first, then `talk ir` if scheduling is suspect. |
| Register values are wrong at runtime | `talk ir`. |
| A branch or loop jumps to the wrong instruction | `talk ir`. |
| Evaluator and VM disagree | Compare what `talk lower` says should happen with what `talk ir` says the VM will run. |

## 5. Small glossary

These words appear in code and comments, so this page defines them in
plain language.

| Word | Plain meaning here |
|---|---|
| IR | A compiler form between source code and final execution. |
| parser | The compiler step that turns source text into Talk syntax trees. |
| type checker | The compiler step that decides what type each Talk expression has. |
| lowering / lowerer | The compiler step, and code, that turns typed Talk into lambda G. |
| lambda G / `λ_G` | The specific middle form Talk lowers into before bytecode. |
| verifier | The checker that makes sure the lambda G program is still well formed. |
| splice | A piece of low-level source inserted with `@_ir`. |
| parameter | A value a function receives. |
| result function | The extra function that receives a function's answer. Often printed as `k`. |
| helper function | A generated function used for a branch, match arm, loop, or next step. |
| chunk | A bytecode function with its own register frame. |
| frame | One call's set of bytecode registers. |
| register | A numbered temporary value slot in bytecode, such as `r0`. |
| tag | The number used to identify an enum case. |
| payload | A value stored inside an enum case. |
| boxed value | A heap value referred to by a handle, used for structs, strings, arrays, and similar values. |
| cell | A mutable box used when a variable must be updated or shared. |
