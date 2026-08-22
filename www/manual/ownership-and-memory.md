# 7. Ownership and Memory

TalkTalk starts from a simple observable rule: ordinary values behave as independent values. Saving an array and later changing the original does not change the saved value. The compiler may share storage internally, but that optimization is not visible in the result of a correct program.

Ownership rules answer three practical questions: who may read a value, who may change it, and who is responsible for cleaning it up.

## Bindings hold values

`let` introduces a binding. Bindings can be assigned again, but assigning one value to another name does not create a permanently shared variable:

```tlk
let current = [1, 2, 3]
let snapshot = current

current.push(4)

print(current)   // [1, 2, 3, 4]
print(snapshot)  // [1, 2, 3]
```

`current` and `snapshot` may initially point at the same internal array buffer. Before mutation, the implementation separates them if necessary. This copy-on-write optimization preserves the source-level snapshot rule.

Strings, arrays, structs, enums, tuples, records, and functions follow value semantics. Scalars such as `Int` are already small independent values. Returning a value, storing it globally, or capturing it in a closure also preserves the snapshot that escaped.

## Reading values through parameters

A plain parameter borrows its argument for the duration of the call. Borrowing lets the function read without taking responsibility for the caller's value:

```tlk
func length(_ value: String) -> Int {
    value.count()
}

let text = "hello"
print(length(text))
print(length(text))
```

The caller can use `text` again because `length` only borrowed it. Most parameters and methods should use this default.

Several shared reads may overlap. A later value-semantic mutation is also fine: if a saved reader still needs the old snapshot, copy-on-write keeps that snapshot intact.

## Changing a caller's value

A `mut` parameter requests exclusive writable access to one caller-owned place. The caller marks that place with `mut`:

```tlk
func bump(mut value: Int) {
    value = value + 1
}

let count = 1
bump(value: mut count)
print(count) // 2
```

During the call, no overlapping access may use the same place. This exclusivity is what makes in-place writeback predictable. A `mut` argument must therefore be a writable binding, field, tuple position, or supported subscript rather than an arbitrary temporary.

Methods follow the same rule. A plain method reads `self`; `mut func` may update it; `consuming func` takes responsibility for it.

## Giving ownership to a function

A `consume` parameter says the callee receives an owned value rather than a temporary read:

```tlk
func store(consume value: String) -> String {
    value
}

store(value: "saved")
```

For an ordinary shareable value, `consume` is a callee-side contract, not always a promise that the caller's binding becomes unusable. If the caller uses its value later, the compiler may retain an independent snapshot before the call. If the call is the last use, ownership can move directly without that retain.

Use `consume` when the callee stores, returns, transfers, or dismantles the value. Use `consume mut` when it also needs to modify its owned local copy.

This repair is not available for every kind of value. Exclusive borrows, unique values, and linear resources cannot be duplicated merely to preserve a later use.

## Linear values

A declaration marked `'linear` creates values that must be consumed exactly once on every finite path. They cannot be implicitly copied or silently dropped:

```tlk
struct Ticket 'linear {
    let seat: Int

    consuming func tear() -> Int {
        self.seat
    }
}

func attend() -> Int {
    let ticket = Ticket(seat: 12)
    ticket.tear()
}

attend()
```

Calling `tear` twice is a compile error. Reaching the end of `attend` without consuming `ticket` is also an error. Linear types represent one-shot capabilities such as resumptions and resources whose abandonment would be incorrect.

`*T` is a statically unique owned value. Unique values likewise rule out implicit sharing while that uniqueness is required. Most application code encounters these types through an API rather than writing them directly.

## Heap values and identity

Ordinary values are snapshots, so mutating one value never gives another saved value observable shared mutation. `struct Name 'heap` and `enum Name 'heap` deliberately choose a different model: aliased identity, shared mutation, and cycles.

```tlk
struct Node 'heap {
    let value: Int
    let next: Node?
}

let first = Node(value: 1, next: .none)
let second = Node(value: 2, next: .some(first))
first.next = .some(second)

first.value + second.value
```

Every alias to one heap object observes its field changes. Heap declarations live in managed regions so connected cycles can be reclaimed together. Recursive nominal layouts infer heap indirection where recursion requires it, but an explicit `'heap` declaration is the clear API signal that identity and shared mutation are intentional.

Choose heap semantics for graphs and identity-bearing objects, not merely to avoid thinking about value copies.

## Deterministic cleanup

TalkTalk destroys owned values when their lifetime ends. Stored fields are torn down with their owner. A type can conform to `Deinit` when it also needs a cleanup action:

```tlk
struct Guard {
    let name: String
}

extend Guard: Deinit {
    consuming func deinit() -> Void {
        print("leaving " + self.name)
    }
}

func use_guard() {
    let guard = Guard(name: "example")
}

use_guard()
```

Cleanup runs on ordinary scope exit, early return, effect abort, and cancellation of a suspended resumption. A `Deinit` hook runs once for each independently owned value, followed by structural cleanup of its fields.

## Ownership marker protocols

Core defines protocols including `Copy`, `Clone`, `Borrowed`, `Owner`, `Deinit`, `Send`, and `Sync`.

- `Copy` permits a trivial independent copy.
- `Clone` supplies an explicit way to create another owned value.
- `Borrowed` and `Owner` describe storage roles used by low-level APIs.
- `Deinit` supplies deterministic cleanup.
- `Send` permits ownership transfer to another worker.
- `Sync` permits safe shared access across workers.

Payload-free enums are `Copy` automatically. Aggregates can satisfy transfer and sharing requirements structurally when all of their contents do. Most application code relies on these constraints through generic APIs instead of implementing low-level storage behavior itself.

## What the compiler still rejects

Implicit sharing repairs ordinary value duplication, but it cannot make every operation safe. Errors remain for overlapping exclusive access, use after moving a non-shareable value, failure to consume a linear value, uninitialized data, invalid heap placement, and unsafe operations outside `#unsafe`.

The useful mental model is:

1. ordinary values are independent snapshots;
2. plain calls borrow;
3. `mut` temporarily grants exclusive write access;
4. `consume` gives the callee ownership;
5. linear and unique values cannot be repaired by copying; and
6. `'heap` is the explicit opt-in to shared identity.

## Further reading

TalkTalk's automatic sharing and cleanup are influenced by:

- [Perceus: Garbage Free Reference Counting with Reuse](https://doi.org/10.1145/3453483.3454032), which places retains and releases from program use.
- [Counting Immutable Beans](https://arxiv.org/abs/1908.05647), which describes Lean's reference counting and reuse.
- [Linear types can change the world!](https://homepages.inf.ed.ac.uk/wadler/topics/linear-logic.html), the foundation for values that must be used exactly once.

[Ownership: implicit sharing and MIR dataflow](../../docs/ownership.md) records how TalkTalk combines those ideas with copy-on-write values, linear resources, and exclusive access.
