# How it works

a compiler in six polite movements

## Lex
source → tokens with start/end positions and kinds (Ident, StringLit, Comma…).

```in
let a = 1 + 2
```

```out
Let@0..3  Ident("a")@4..5  Eq@6..7  Int(1)@8..9
Plus@10..11  Int(2)@12..13  Eof@13..13
```

## Parse
tokens → AST. Recursive descent, Pratt precedence for expressions.

```in
Let@0..3  Ident("a")  Eq  Int(1)  Plus  Int(2)
```

```out
Let {
  name: "a",
  value: Binary {
    op: Add,
    lhs: IntLit(1),
    rhs: IntLit(2),
  },
}
```

## Resolve
names → symbols. Replace `Name::Raw(string)` with `Name::Resolved(symbol, string)`.

```in
Let { name: "a", value: Binary {…} }
```

```out
Let {
  name: Resolved(#42, "a"),
  value: Binary { op: Add, lhs: IntLit(1), rhs: IntLit(2) },
}
// SCC graph built so we check recursion in order
```

## Check
the big one. infer + check types. constraint generation, unification.

```in
Let { name: #42 "a", value: Binary { Int, Int } }
```

```out
TypedAST::Let {
  sym: #42,
  ty: Int,
  value: TypedBinary {
    op: IAdd,
    ty: Int,
    lhs: IntLit(1): Int,
    rhs: IntLit(2): Int,
  },
}
```

## Lower
TypedAST → lil IR. basic blocks, SSA-ish, explicit allocs.

```in
TypedLet { sym: #42, ty: Int, value: … }
```

```out
fn main():
  %0 = const 1 : Int
  %1 = const 2 : Int
  %2 = iadd %0, %1 : Int
  store #42, %2
  ret ()
```

## Interp
lil IR → lil interpreter. we just walk it. blazing? no. legible? yeah.

```in
bytecode + stack frame
```

```out
PC=0  iadd  a=1 b=2  -> 3
PC=1  store #42 ← 3
PC=2  ret
=> ()
```
