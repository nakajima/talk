# 7. Ownership and Memory

Most TalkTalk values behave like independent copies. You can save an array, change the original, and the saved value stays the same. The compiler shares storage behind the scenes when it can and cleans values up when they are no longer needed.

## Value snapshots

Assigning an array, string, struct, enum, tuple, record, or function creates an independent value snapshot. The implementation may share storage until one copy changes:

```tlk
let current = [1, 2, 3]
let snapshot = current

current.push(4)

print(current)   // [1, 2, 3, 4]
print(snapshot)  // [1, 2, 3]
```

The same rule applies when a value escapes through a return, global store, or closure capture: the compiler retains what is needed so the escaped value owns its snapshot.

## Borrowing and mutation

Plain parameters and methods borrow by default. Shared borrows do not prevent later value-semantic mutation; copy-on-write preserves the reader's snapshot. A live `&mut` loan is different: it promises exclusive in-place access, so an overlapping outside access is an error.

```tlk
func read(_ value: String) -> Int { value.count() }

let text = "hello"
print(read(text))
print(read(text))
```

`mut func` and `mut` parameters express writable access. See [Bindings and Functions](bindings-and-functions.md) for call syntax.

## Consuming values

`consume` is a callee-side ownership contract. The callee receives ownership, but a caller may still use a shareable value afterward: the compiler retains a copy before the call when needed. The last use can move without a retain.

This is different from a linear value, which cannot be duplicated.

## Linear values

A declaration marked `'linear` must be consumed exactly once on every finite path. It cannot be implicitly copied or dropped:

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

Calling `tear` twice is a compile error, as is reaching the end of `attend` without consuming the ticket. Linear types are for one-shot capabilities and resources where duplication or silent abandonment would be incorrect.

## Heap declarations

`struct Name 'heap` and `enum Name 'heap` opt into aliased, region-allocated reference semantics. They provide identity, shared mutation, and cycles:

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

Recursive nominal layouts infer heap indirection where it is required. Heap values are the explicit escape hatch from ordinary snapshot semantics.

## Destruction

A type can conform to `Deinit` to run deterministic cleanup:

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

Stored fields are torn down as their owner is destroyed. Cleanup also runs when control leaves through an effect abort or when a suspended resumption is cancelled.

## Ownership marker protocols

Core defines `Copy`, `Clone`, `Borrowed`, `Owner`, `Deinit`, `Send`, and `Sync` to state representation and transfer roles. Payload-free enums are `Copy` automatically. Most application code observes their constraints rather than implementing low-level storage behavior directly.

The remaining ownership errors cover cases the compiler cannot safely repair by making another shared copy: overlapping exclusive access, misuse of linear or unique values, uninitialized data, invalid declarations, unsupported heap placement, and unsafe operations outside an unsafe block.

## Further reading

TalkTalk's automatic sharing and cleanup are influenced by:

- [Perceus: Garbage Free Reference Counting with Reuse](https://doi.org/10.1145/3453483.3454032), which places retains and releases from program use.
- [Counting Immutable Beans](https://arxiv.org/abs/1908.05647), which describes Lean's reference counting and reuse.
- [Linear types can change the world!](https://homepages.inf.ed.ac.uk/wadler/topics/linear-logic.html), the foundation for values that must be used exactly once.

[Ownership: implicit sharing and MIR dataflow](../../docs/ownership.md) records how TalkTalk combines those ideas with copy-on-write values, linear resources, and exclusive access.
