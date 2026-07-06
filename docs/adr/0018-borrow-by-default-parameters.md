# 0018 — Borrow-by-default function parameters

Status: proposed (2026-07-06)

## Context

Talk's ownership model is deliberately closer to Rust than to Swift: moves,
borrows, exclusive access, linear resources, and drop scheduling are checked by
the compiler rather than left to convention. The surface syntax, however, still
makes the uncommon operation look like the default one.

Today a parameter annotation names the ownership mode directly:

```talk
func read(s: &String) -> Int       // shared borrow
func edit(s: &mut String)          // exclusive borrow
func take(s: String) -> Int        // owned/by-value parameter
```

That creates three practical problems.

1. **Read-only APIs pay the syntactic tax.** Most parameters are inspected, not
   stored or destroyed. Those signatures should be the quiet path, but today
   they carry `&` everywhere. ADR 0014 changed comparison requirements to
   borrow their right-hand side precisely because comparison is a read:

   ```talk
   protocol Equatable<RHS = Self> {
       func equals(rhs: &RHS) -> Bool
   }
   ```

   That was the right semantic decision, but it made a common API more noisy.

2. **Owned parameters invite accidental ownership leaks.** A by-value signature
   says the callee owns the argument and may store, return, move, or drop it.
   For APIs that only read, that is too strong. It forces the caller into move
   or clone reasoning even when the callee only needed access.

3. **Receivers and explicit parameters do not line up.** Method receivers
   already communicate intent in the Swift/Rust style:

   ```talk
   func show()             // shared receiver
   mut func bump()         // exclusive/inout receiver
   consuming func close()  // owned receiver
   ```

   Ordinary parameters should not use the inverse convention where plain `T`
   means owned.

The target feel is:

> Swift ergonomics at the source level, Rust power in the checker.

Borrowing should be the default, automatic copies/clones should be allowed for
value-semantic types when the language can prove they are valid, and linear or
resource-owning values should still have Rust-grade move checking. The
performance cost of inserted copies is acceptable when the type permits it, but
there must be explicit escape hatches when the programmer wants to force a
move, force a clone, or make mutation visible.

## Decision

Function parameters become borrow-by-default. Ownership mode is a property of a
parameter, not something users normally write as `&` in the parameter's type.

```talk
func inspect(foo: Foo)              // shared borrow, default
func update(mut foo: Foo)           // exclusive/inout borrow
func store(consume foo: Foo)        // owned parameter
func normalize(consume mut foo: Foo) -> Foo  // owned and locally mutable
```

The same modes apply to function types:

```talk
(Foo) -> Void             // borrows Foo
(mut Foo) -> Void         // receives exclusive/inout access
(consume Foo) -> Void     // takes ownership
(consume mut Foo) -> Foo  // takes ownership and may mutate its local storage
```

The same modes apply to closure and trailing-block parameters:

```talk
func walk(fn: (DirectoryEntry) -> Void) {
    for entry in self.entries() { fn(entry) }
}

func drain(fn: (consume DirectoryEntry) -> Void) { ... }
func rewrite(fn: (mut DirectoryEntry) -> Void) { ... }
```

`&T` and `&mut T` remain type constructors in the internal type system and may
remain accepted in non-parameter positions where explicit borrowed values are
being named. In parameter and function-type positions, they are no longer the
preferred spelling. The formatter and migration tool should rewrite:

```talk
func old(a: &A, b: &mut B, c: C)
```

to:

```talk
func new(a: A, mut b: B, consume c: C)
```

when `c` is semantically owned. If `c` is only read, it stays unadorned.

## Parameter mode semantics

### Borrow parameters: `foo: Foo`

An unadorned parameter is a shared borrow of a `Foo`.

```talk
func byte_count(s: String) -> Int {
    s.byte_count
}
```

The callee may read `s`, call shared methods, and derive non-escaping borrows
from it. The callee does not own `s`; it may not store it into an owned field,
return it as an owned value, pass it to an owned parameter without a valid copy
or clone, or drop it.

Returning a borrow-derived value from a borrow parameter remains legal because
the returned value is tied to caller-owned storage:

```talk
func first(s: String) -> Substring {
    s.utf8().slice(0, 1)
}
```

The same return from an owned local or owned parameter is still rejected if it
would let a borrow outlive storage owned by the function.

### Mutable parameters: `mut foo: Foo`

`mut` means exclusive borrowed access, not merely "the local binding may be
reassigned".

```talk
func bump(mut counter: Counter) {
    counter.count = counter.count + 1
}
```

The caller must provide an addressable mutable place. The call creates an
exclusive loan for the duration of the call. While that loan is active, no other
shared or exclusive access may overlap. Mutations are visible through the
caller-provided place, just like a `mut func` receiver.

A `mut` parameter is not owned. The callee may not move it into an owned field
or return it as an owned value unless it explicitly clones/copies a cloneable
value.

### Consuming parameters: `consume foo: Foo`

`consume` means the callee takes ownership.

```talk
func into_box(consume s: String) -> Box {
    Box(value: s)
}

func close(consume socket: Socket) {
    // owns the socket; may close/drop it
}
```

Inside the function, `foo` has today's by-value parameter semantics. It may be
moved, stored, returned, or dropped according to the existing ownership rules.
For linear values, `consume` is the explicit handoff point.

A consuming parameter may also be locally mutable:

```talk
func sorted(consume mut values: Array<Int>) -> Array<Int> {
    values.sort()
    values
}
```

`consume mut` does not write back to the caller; it owns a local value.

## Call-site behavior

The callee's parameter mode determines the required access. Call-site markers
are available as escape hatches and as documentation for non-default behavior.

```talk
read(value)             // borrow, default
update(mut value)       // require exclusive access
store(consume value)    // force a move into an owned parameter
store(copy value)       // force a copy/clone into an owned parameter
read(borrow value)      // force a shared borrow, useful for disambiguation
```

For labeled arguments, the marker belongs to the value expression:

```talk
buffer.write(bytes: bytes)          // borrow or auto-adapt as required
buffer.write(bytes: copy bytes)     // force a clone/copy
sink.send(value: consume message)   // force a move
counter.increment(by: mut amount)   // exclusive access to the argument value
```

Rules:

- Passing to a borrow parameter creates or forwards a shared borrow. It never
  moves the argument.
- Passing to a `mut` parameter requires an addressable mutable place and creates
  an exclusive loan. Temporaries are rejected for v1 unless a later design adds
  a clear owned-temporary rule.
- Passing to a `consume` parameter moves the value if the argument is owned and
  the move is legal.
- If the argument would otherwise need to remain usable, the compiler may insert
  a copy/clone only when the type's grade or bounds prove that this is valid.
- `consume value` disables automatic cloning and forces a move. A later use is
  an error.
- `copy value` disables last-use move selection and forces a copy/clone. It is
  an error when the type is not copyable/cloneable.
- `borrow value` disables owned adaptation and requires the selected callee to
  accept a borrow.

This keeps the normal path quiet while preserving explicit control over the
important ownership decisions.

## Automatic copy and clone insertion

Borrow-by-default only works ergonomically if value-semantic types can be
copied or cloned when an owned value is required.

```talk
func greet(name: String) -> String {
    "hello " + name
}
```

`name` is a borrowed parameter. If `+` consumes its right-hand side, the compiler
may insert the necessary copy/clone for `String` because `String` is a
value-semantic CoW type. For a linear resource, the same pattern is rejected:

```talk
struct Socket 'linear {
    let fd: Int
}

func bad(socket: Socket) -> Socket {
    socket       // error: borrowed parameter cannot be returned as owned Socket
}
```

Generic code must state the capability it relies on:

```talk
func duplicate<T: Clone>(value: T) -> (T, T) {
    (value, value)       // one inserted clone
}

func id<T>(consume value: T) -> T {
    value                // ownership was explicit
}
```

Without a copy/clone bound, this is no longer accepted:

```talk
func id<T>(value: T) -> T {
    value                // error: borrowed T cannot be returned owned
}
```

The exact clone mechanism should reuse the existing grade machinery first
(`Copy`, cheap CoW retain, and non-cloneable/linear classifications) and grow a
source-level `Clone` protocol only when the standard library is ready for it.
The important language rule is that the compiler may insert ownership-adapting
copies only when the type system proves the operation is valid.

## Protocols and witnesses

Ownership mode is part of a requirement's signature.

Read-only protocols become simpler:

```talk
public protocol Showable {
    func show() -> String
}

public protocol Equatable<RHS = Self> {
    func equals(rhs: RHS) -> Bool

    func notEquals(rhs: RHS) -> Bool {
        if self.equals(rhs: rhs) { false } else { true }
    }
}
```

Resource protocols stay explicit:

```talk
public protocol Closable {
    consuming func close()
}

public protocol Sink<Element> {
    func send(consume value: Element)
}
```

Mutation is explicit in both receiver and parameter position:

```talk
public protocol Accumulator<Element> {
    mut func append(value: Element)          // mutates self, borrows value
    mut func absorb(consume value: Element)  // mutates self, takes value
}
```

Witness matching is exact in v1 after generic substitution. A requirement that
borrows cannot be satisfied by a witness that consumes, because that would allow
the protocol caller to lose ownership through a read-only-looking API. A
requirement that consumes cannot be satisfied by a witness that only borrows,
because the caller is relying on ownership transfer and callee-side drop/store
semantics.

Copy-graded scalar witnesses may still erase to the same runtime calling
convention, but source-level mode matching should not depend on runtime erasure.
The mode is part of the contract.

## Standard library migration examples

### Comparisons

ADR 0014's comparison design becomes the default spelling:

```talk
// before
public protocol Equatable<RHS = Self> {
    func equals(rhs: &RHS) -> Bool
}

// after
public protocol Equatable<RHS = Self> {
    func equals(rhs: RHS) -> Bool
}
```

Implementations follow:

```talk
extend String: Equatable<String> {
    func equals(rhs: String) -> Bool {
        self.equals_string(rhs)
    }
}
```

### Directory walking

The fs walker no longer advertises borrows with `&` in its function type:

```talk
// before
func walk(fn: (&DirectoryEntry) -> ()) {
    for entry in self.entries() { fn(entry) }
}

// after
func walk(fn: (DirectoryEntry) -> Void) {
    for entry in self.entries() { fn(entry) }
}
```

If a visitor should take ownership of each entry, that is explicit:

```talk
func drain(fn: (consume DirectoryEntry) -> Void) { ... }
```

### Constructors and builders

Any parameter stored into a result needs `consume` unless the function intends
to clone it.

```talk
struct User {
    let name: String
}

func user(consume name: String) -> User {
    User(name: name)
}

func cloned_user(name: String) -> User {
    User(name: copy name)
}
```

### Operators

Operator protocols must be audited rather than mechanically rewritten. If a
protocol operation really takes ownership of an operand, its requirement should
say so:

```talk
public protocol Add<RHS> {
    associated Ret
    func add(consume rhs: RHS) -> Ret
}
```

If an operation is intended to be read-only and internally clone/copy as needed,
it should use the default borrowed parameter:

```talk
public protocol Distance<RHS> {
    associated Ret
    func distance(to rhs: RHS) -> Ret
}
```

The decision about each operator is semantic. The new syntax makes that decision
visible instead of encoding it accidentally in `RHS` versus `&RHS`.

## Grammar sketch

Parameter declarations:

```text
parameter_decl ::= param_mode? identifier (':' type_annotation)?
param_mode     ::= 'mut'
                 | 'consume'
                 | 'consume' 'mut'
```

Function type parameters:

```text
func_param_type ::= param_type_mode? type_annotation
param_type_mode ::= 'mut' | 'consume' | 'consume' 'mut'
func_type       ::= '(' func_param_type_list? ')' '->' type_annotation
```

Call arguments:

```text
call_arg        ::= label? ownership_arg_expr
label           ::= identifier ':'
ownership_arg_expr
                ::= arg_mode? expression
arg_mode        ::= 'mut' | 'consume' | 'copy' | 'borrow'
```

Legacy compatibility in parameter positions:

```text
x: &T       => x: T
x: &mut T   => mut x: T
x: T        => consume x: T   // only when migration proves ownership is needed
```

The parser should reject confusing combinations such as `mut consume x: T` and
`consume consume x: T`. `consume mut` is the only composed mode in v1.

## Implementation notes

### AST and HIR

Add a parameter mode to parsed and lowered parameters:

```rust
pub enum ParamMode {
    Borrow,
    Mut,
    Consume,
    ConsumeMut,
}
```

`Parameter` should carry `mode`, plus source spans for the mode keyword(s) so
formatting, diagnostics, semantic tokens, and rename/goto behavior stay precise.
HIR should copy the mode and continue carrying the checker-assigned type.

The checker should lower parameter annotations through a parameter-specific
entry point:

```text
lower_param(mode, T):
    Borrow     => &T
    Mut        => &mut T
    Consume    => T
    ConsumeMut => T plus local-mutability permission
```

Do not change the meaning of `let x: T`, fields, enum payloads, return types,
or type aliases. The default changes only in parameter and function-type
parameter positions.

### Type representation

The smallest implementation can keep using `Ty::Borrow(Perm::Shared, T)` and
`Ty::Borrow(Perm::Exclusive, T)` for default and `mut` parameters, with
consuming parameters represented as `T`. That reuses existing unification,
borrow-erasure, provenance, and lowering behavior.

Longer term, `Ty::Func` may want to store a small `ParamTy { mode, ty }` wrapper
instead of `Vec<Ty>` so source mode is not reconstructed from lowered types and
`consume mut` is not a side channel. This is especially useful for formatter
round-tripping, LSP hovers, protocol witness diagnostics, and future ABI work.

### Type checking

- Parameter seeding should treat default parameters exactly like today's `&T`
  parameters.
- `mut` parameters should use today's `&mut T` / exclusive-borrow machinery.
- `consume` parameters should use today's by-value parameter machinery.
- Returning borrow-derived values from default parameters should be accepted as
  returning borrow-derived values from today's `&T` parameters.
- Returning owned values from default parameters should require a valid copy or
  clone.
- Generic automatic clones require a bound or grade proof. Unknown `T` is not
  implicitly cloneable.
- Protocol requirement matching should compare modes, not just erased runtime
  types.

### Flow and ownership checking

The flow checker already distinguishes borrowed parameters from owned
parameters through their types and provenance. This ADR increases the number of
borrowed parameters; it should not require a new borrow model.

Updates needed:

- Seed default parameters as `Origin::BorrowedParam`.
- Seed `mut` parameters as borrowed parameters with exclusive permission.
- Seed `consume` parameters as `Origin::OwnedParam` and keep existing parameter
  drop scheduling.
- Treat `consume mut` as owned for move/drop purposes and mutable for assignment
  conversion.
- Add call-site ownership facts for explicit `consume`, `copy`, `borrow`, and
  `mut` markers.
- Record inserted clones/copies in flow facts so diagnostics and tooling can
  explain them.

### Lowering and runtime

Borrowed parameters erase the same way today's `&T` parameters erase, so most
runtime behavior should be unchanged. The migration primarily changes what type
is produced from source syntax.

Consuming parameters continue to use the existing callee-owned parameter/drop
convention. `mut` free-function parameters must use the same exclusive-access
semantics as today's `&mut` parameters. If any current lowering path only fully
supports mutable receivers and not free `&mut` parameters, that gap must be
closed before `mut foo: Foo` is stabilized.

Automatic clones should be explicit in the lowered representation, not hidden in
code generation, so the free-balance verifier and drop elaboration see the real
owned value being produced and consumed.

### Formatter, LSP, and diagnostics

The formatter should prefer the new spelling in parameter positions:

```talk
func f(a: A, mut b: B, consume c: C) { ... }
```

LSP hovers should distinguish source type from ownership mode, for example:

```text
s: String (borrowed parameter)
out: String (owned parameter)
counter: Counter (mutable borrowed parameter)
```

Diagnostics should avoid telling users to add `&` for ordinary borrowed
parameters. Suggested messages:

- "parameter `s` is borrowed; add `consume` if this function takes ownership"
- "cannot return borrowed parameter `value` as owned `T`; add a Clone bound and
  copy it, or make the parameter `consume value: T`"
- "argument to `mut` parameter must be a mutable place"
- "implicit clone inserted here" / "use `consume value` to force a move"

Semantic tokens should mark consuming, mutable, copied, and implicitly cloned
uses so the source retains ownership visibility even when the syntax is quiet.

## Migration plan

1. **Introduce parameter modes behind a parser/checker flag.** Add AST/HIR mode
   fields, parse `consume` and parameter-position `mut`, and keep old `&` forms
   accepted.
2. **Change default parameter lowering under the flag.** Unadorned parameters
   lower to shared borrows. Update flow seeding and diagnostics.
3. **Add explicit call-site markers.** Implement `consume`, `copy`, `borrow`,
   and `mut` argument markers as constraints on call resolution and flow.
4. **Build an ownership migration command.** For every existing `x: T`
   parameter, decide whether the body needs ownership. If yes, rewrite to
   `consume x: T`; otherwise leave it as `x: T`. Rewrite `x: &T` to `x: T` and
   `x: &mut T` to `mut x: T`.
5. **Migrate core and stdlib.** Start with read-only protocols (`Showable`,
   `Equatable`, `Comparable`), iterator/visitor callback types, and string/path
   APIs. Audit operator protocols separately.
6. **Turn on by default.** Keep legacy `&` parameter syntax accepted for one
   release with warnings, then decide whether to keep it as an explicit expert
   spelling or reject it in parameter positions.
7. **Tooling pass.** Add hovers, semantic tokens, formatter output, and a
   `talk check --copies` or equivalent report for implicit copies/clones.

The suite should stay green after each stage. Any migration that changes a
public API's ownership mode must update protocol witnesses and call sites in the
same stage.

## Potential gotchas

### Plain `T` becomes context-sensitive

`let x: Foo` still declares an owned local. `func f(x: Foo)` declares a borrowed
parameter. That is intentional but must be taught clearly and reflected in
hovers.

### Identity functions change meaning

This old pattern no longer means "take and return ownership":

```talk
func id<T>(x: T) -> T { x }
```

It must become either:

```talk
func id<T>(consume x: T) -> T { x }
```

or:

```talk
func id<T: Clone>(x: T) -> T { copy x }
```

### Constructors need `consume`

Any parameter stored into a result must be explicitly owned or explicitly
cloned. This is the largest migration category and the most useful place for an
automated fix-it.

### `mut` must not look like local mutability only

`mut foo: Foo` is an inout/exclusive borrow. It is not the same as taking an
owned `Foo` and allowing local reassignment. Use `consume mut foo: Foo` for
that.

### Function values need mode-aware types

A `(Foo) -> Void` callback is no longer the same contract as a
`(consume Foo) -> Void` callback. Higher-order APIs must be audited carefully,
especially visitors, iterators, handlers, and stored function fields.

### Automatic clones can hide costs

The compiler may insert real work. That is an accepted tradeoff for the default
experience, but tooling must expose it. At minimum, diagnostics and hovers should
identify inserted clones; a project-level copy report should come before this
ships as the default.

### Linear/resource values remain strict

Borrow-by-default does not weaken linearity. A borrowed `Socket` cannot be
closed by a function that only borrowed it, and it cannot be returned as an
owned value. APIs that transfer resources must spell `consume`.

### Overload and witness selection must not ignore mode

If two call candidates differ only by ownership mode, call-site markers should
participate in selection. V1 may reject mode-only overloads if that keeps the
solver simple, but protocol witness matching must still treat mode as part of
the requirement.

### Temporaries passed to `mut`

`update(mut Counter())` has no caller place to write back to. V1 should reject
it. If a later design wants owned temporary mutation, it should use
`consume mut` semantics instead of overloading `mut`.

## Consequences

- Common read-only APIs become shorter and safer.
- Ownership transfer becomes visually explicit at the declaration site.
- Existing receiver modes and ordinary parameter modes line up.
- ADR 0014 generalizes from comparisons to all parameters.
- More programs will rely on implicit clones for value-semantic types; tooling
  must make those costs visible.
- Generic code becomes more honest: returning or duplicating a borrowed `T`
  requires `consume` or a clone/copy bound.
- The implementation can reuse most existing borrow, move, provenance, and drop
  machinery by changing how parameter syntax lowers into types.

## Open questions

- Should `borrow` be accepted as an explicit parameter-mode keyword
  (`borrow x: T`) or only as a call-site marker? The default makes it
  unnecessary, but an explicit spelling may help generated code and education.
- Should mode-only overloads be accepted in v1, or should explicit call-site
  markers only constrain ordinary overload resolution?
- What is the source-level spelling of the clone capability: a `Clone` protocol,
  existing grade attributes, or both?
- Should legacy `&T` in parameter positions remain permanently accepted as an
  expert alias, or should the language fully remove it from parameter syntax?
- Should core arithmetic protocols consume operands, borrow operands and clone
  internally, or split into separate consuming and non-consuming protocols? This
  ADR requires the choice to be explicit but does not settle every operator.

## Non-goals

- This ADR does not remove borrowed types from the internal type system.
- This ADR does not weaken linear or exclusive-access checking.
- This ADR does not require adding a third-party dependency or runtime reference
  counting beyond what value-semantic types already use.
- This ADR does not redesign receiver modes; it aligns explicit parameters with
  them.
- This ADR does not require implementing a full `Clone` protocol before the
  syntax can land. Existing copy/cheap-clone grades can support the first
  version.
