# Talk Backend: λ_G IR (SSA without Dominance) → Bytecode VM

*The approved backend plan, inlined into the repo for handoff. This is the
point-in-time design document (June 2026). For the current memory,
ownership, and FFI roadmap see
`docs/adr/0008-managed-storage-and-ffi.md`. Milestones M0–M3 are
complete.*

## Context

Frontend complete (parse → resolve → OutsideIn(X); all 27 examples + core check clean); nothing executes. The backend is rebuilt as: AST + TypeOutput → **λ_G**, the graph-based λ-calculus of Leißa & Griebler, *SSA without Dominance for Higher-Order Programs* (arXiv:2604.09961v2; **full text in repo at `ssa-paper.md` — the canonical spec for the IR core**) → IR-level transformations (inlining, closure conversion, effect wiring) → nesting-tree scheduling → **register bytecode VM** (user decision), with **mutable value semantics and source receiver modes** (user decision). House rules: faithful implementations of published work, cited in code; deviations and unproven seams flagged; correctness over convenience; TDD.

Why λ_G over the previous register-IR draft (user direction, and on the merits):
- Talk is higher-order; λ_G is the SSA-style IR *designed* for higher-order programs — functions float in a soup, φs are function variables, dominance is replaced by free-variable nesting (paper Thm. 1: nesting ⟹ dominance), and the metatheory is Lean-verified.
- Monomorphization, inlining, loop peeling, and witness specialization all become one operation: dependency-aware β-reduction (paper §3.3–3.4, Table 2).
- Statically-routed effect handlers (our resolver's `effect_handlers`) become *direct references to handler functions in the soup* — no frame-mark/unwind machinery in the VM, and M9's resumable handlers are just first-class continuations, which λ_G already has.

## Verified constraints (unchanged)

- `@_ir` dialect: core uses 13 opcodes (`cmp add sub mul div trunc itof alloc load store gep copy io_write`); all other I/O is `'io(.variant(args))` performs. Core allocation is `public effect 'alloc(allocation: Allocation) -> Void`, and `_alloc<Element>(count)` lowers to `alloc Element`.
- TypeOutput (node_types, instantiations, member_resolutions, catalog witnesses/derivable/EffectSig) + ResolvedNames (captures, mutated_symbols, effect_handlers) are the lowerer's complete input. `mutated_symbols` still informs assignment conversion and mutable capture handling, but mutating method write-back is keyed by receiver mode after implicit receiver insertion.
- `ArrayIterator.next()` is `mut func next()`: it mutates `self` observably and uses the inout receiver calling convention. No example needs resumable effects today. core.rs must cache typed artifacts (ASTs + TypeOutput + ResolvedNames) for whole-program lowering.

---

# IR Specification: λ_G for Talk

## Formal foundations

| Component | Published basis |
|---|---|
| The calculus: program = flat label→function map; one variable per function (`var ℓ`); bodies expr-or-unset (↑) for knot-tying; mutation allowed; functions returning ⊥ are continuations | Leißa & Griebler §2 (Fig. 2 syntax), §3 (typing T-App/T-Fun/T-Var/T-Body/T-Prog; evaluation E-App/E-β; Progress/Preservation — Lean-verified). Lineage: Thorin (Leißa, Köster & Hack, CGO 2015), MimIR (Leißa et al., POPL 2025), Guile's CPS soup (Wingo 2023). |
| Well-formedness replaces SSA dominance | Paper Property 2 (nesting antisymmetric), Rule WF; Thm. 1 nesting ⟹ dominance. The verifier checks T-Prog + WF. |
| Free-variable framework: LV/LF precomputed on immutable, hash-consed expressions; FV as least fixed point with mark/run iteration (≤ d(G)+2 passes, Kam & Ullman JACM 1976); users-set (UF) invalidation on mutation | Paper §3.1 + §3.1.1, including the acyclic fast path and Table 1's worked example (which becomes a unit test). Hash-consing gives semi-global value numbering as in MimIR (paper §6.1, fn. 2; Sea of Nodes: Click & Cooper, TOPLAS 1995). |
| Dependency-aware substitution & β-reduction (= inlining = mono specialization = loop peeling, Table 2) | Paper §3.3–3.4: substitution rewrites exactly the expressions whose FV sets intersect the substituted variables; threading V/F/P maps; stub functions resolve recursion. Lemma 3 + Thm. 2/3 give WF/type preservation. |
| η-expansion / known vs well-known functions (signature changes, critical edges) | Paper §3.5 (+ Steele, *RABBIT*, 1978 for well-known functions). Used when specializing witness signatures and removing dead parameters. |
| Nesting tree + sibling dependencies + SCCs (loops/recursion; virtual root = call graph) | Paper §4 (Fig. 8 construction; SIBL rule; Tarjan SIAM 1972). §4.1's translation-to-lexical-scoping case study **is our scheduling pass** to bytecode functions/blocks; §4.2 grounds later code motion. |
| FV set representation | Paper §5: v1 uses hash-consed ordered arrays only (paper: best for small sets; empirically ≤16 threshold); the indexed trie (splay/link-cut: Sleator & Tarjan JCSS 1983/JACM 1985) is the documented scaling path, not v1 scope. |
| CPS as the lowering target; calls/returns reconstructed at codegen | SSA↔CPS: Kelsey (IR'95), Appel (SIGPLAN 1998); compiling with continuations: Appel 1992, Kennedy ICFP 2007; Thorin CGO 2015 §codegen for recovering calls/returns/blocks from a CPS soup. Join points discipline: Maurer, Downen, Ariola & Peyton Jones, *Compiling without Continuations* (PLDI 2017) — our well-known continuations are exactly join points and stay free (become blocks, never closures). |
| Closure conversion (only for functions with *unknown* occurrences) | Flat closures: Cardelli LFP 1984; safe-for-space: Shao & Appel LFP 1994; assignment conversion for mutable captures: Kranz et al., ORBIT 1986; environments read off λ_G FV sets directly. |
| Monomorphization at the AST→IR boundary (worklist), β-reduction for inlining after | MLton whole-program; rustc monomorphization collector; Jones, *Dictionary-free Overloading by Partial Evaluation* (PEPM 1994). The IR stays simply-typed (paper's λ_G + Talk ground types) — MimIR's dependent types not needed in v1. |
| Pattern matching → decision trees → `switch` builtin | Maranget (ML 2008), first-column heuristic; or-patterns by row expansion; non-exhaustive → trap. |
| Value semantics + receiver modes | Racordon et al., *Implementation Strategies for Mutable Value Semantics* (JOT 2022); CoW Rc records; source `mut func` methods use an internal mutable receiver and ret continuations carry [result, Self] — the caller's continuation performs the write-back through a `KeyPath`-shaped target. Source `func` uses a shared receiver; source `consuming func` uses an owned receiver. Ownership and borrow checking runs on a source-near CFG ownership MIR before λ_G so flow-sensitive ownership facts do not have to be reconstructed from CPS. This tracks Rust's MIR borrow-checking shape ([borrow check](https://rustc-dev-guide.rust-lang.org/borrow-check.html), [region inference](https://rustc-dev-guide.rust-lang.org/borrow-check/region-inference.html), [drop elaboration](https://rustc-dev-guide.rust-lang.org/mir/drop-elaboration.html)), uses origin/loan facts compatible in spirit with [Polonius](https://github.com/rust-lang/polonius), and follows the path/place model in [Oxide](https://arxiv.org/abs/1903.00982) and [Place Capability Graphs](https://arxiv.org/abs/2503.21691). |
| Boxed/unboxed in raw memory | Leroy, *Unboxed Objects and Polymorphic Typing* (POPL 1992): scalars unboxed bytes; aggregates as 8-byte handles into a VM slot arena (CoW value semantics preserved on load). |
| Effects | Handlers: Plotkin & Pretnar (LMCS 2013). Static routing makes the handler a *known function reference at the perform site* — evidence passing with compile-time-constant singleton evidence (Xie & Leijen, ICFP 2020/2021, degenerate case). Abort (`-> Never`): perform = apply handler, then apply the handling scope's end continuation (skipping intervening returns — sound because everything is CPS; semantics frozen by Effects.tlk's expected output). M9 resumable: the perform's own continuation is already a λ_G function — pass it to the handler; one-shot per Bruggeman, Waddell & Dybvig (PLDI 1996). No VM support needed in either milestone. |
| Reference evaluator as executable spec | The paper's small-step semantics (§3.4) implemented directly (~200 lines) as a definitional interpreter (Reynolds 1972); every program runs on both it and the bytecode VM, and the results must agree. |
| Bytecode & VM | Register bytecode: Shi, Casey, Ertl & Gregg (VEE 2005); Lua 5.0 (Ierusalimschy et al., J.UCS 2005); dispatch: Ertl & Gregg (JILP 2003). Frames are plain data (M9 continuation capture per Hieb, Dybvig & Bruggeman, PLDI 1990). |

**Flagged seams (ours):**
1. **λ_G in Rust, subset of MimIR** — the paper's implementation is C++/MimIR with dependent types; we reimplement the simply-typed core + Talk ground types. The Lean metatheory covers the calculus we implement; the engineering (arena, interning) is ours.
2. **Scheduling to bytecode** — §4.1 targets OCaml (lexical scoping); we target bytecode functions/blocks. The mapping (nesting tree children of a CPS function = its blocks; sibling SCCs = loops; ret-continuation recognition = call/return reconstruction per Thorin CGO 2015) is a composition of published pieces; the encoder is checked against the reference evaluator on every test program.
3. **Abort-resume point** (rest-of-scope handler regions) and **Array shallow-copy** (struct-over-RawPtr) — same flags as before; pinned by frozen expected output.
4. **Handles in raw bytes** — slot-arena indices stored in the linear heap (Leroy boxing composed with a byte heap; nearest practice JNI handle tables).

## The IR, concretely

```
Program:  labels ℓ → Function { ty: [t,…] → u, body: Expr | Unset, uf: UserSet, fv: Cache }
Types t:  I64 | F64 | Bool | Byte | Ptr | Void | ⊥ | [t,…] (tuple) | t → u | Boxed(RecordId) | Variant(EnumId)
Exprs e (immutable, hash-consed; LV/LF stored at construction):
          Const(c) | ℓ | var ℓ | App(e, e) | Tuple(e,…) | Extract(e, i) | PrimOp(op, [e,…], t)
PrimOps:  the @_ir dialect in direct style (cmp/add/sub/mul/div/trunc/itof/alloc/free/load/store/copy/gep/io_write)
          + records/get_field/set_field + variant/get_tag/get_payload + io_* + io_perform + cell_new/cell_get/cell_set
Builtins: br_⊥(cond, then_k, else_k) ; switch_⊥(tag, [k_0…k_n], default_k)   (paper §2.2's br, plus tags)
```
- Continuations (codomain ⊥) are basic blocks/join points/loop headers/return continuations — per Table 2.
- Multiple parameters = tuple-typed variable + `Extract` (paper Fig. 4: `var iter.0`).
- `Unset` bodies tie recursive knots during construction and substitution (paper Eq. 18).
- One variable per function, label-identified — no separate binder bookkeeping (paper §7 "Binders").
- `ref` from the parsed dialect: rejected at splice with a diagnostic (its register-reference semantics is superseded by CPS + write-back; core never uses it).

## Pipeline

1. **Semantic MIR (typed AST → source-near CFG MIR):** after type checking and before λ_G, each source body is projected into one shared MIR under `src/mir`, not an ownership-private IR. Bodies carry owner symbols, locals, `KeyPath` projections, operands/rvalues, explicit points/scopes/storage live-dead/drop candidates, branch/switch/loop terminators, and cached source-order use counts. The ownership checker executes move, borrow, assignment, call, return, and explicit closure-capture events with a per-body worklist over CFG successors, so branch joins and loop backedges merge ownership state in MIR instead of relying on source-order traversal. It emits internal origin/loan/storage/move/assignment/drop facts, and drop elaboration writes checked static/dead/conditional/open annotations back onto MIR drop candidates. Needs-drop is type based, with borrowed nominals overriding owned fields; use-before-initialization is rejected; escaping closure values are summarized through locals, returns, by-value arguments, aggregates, and trailing blocks. Closure literals support explicit `copy`, `consuming`, `&`, and `&mut` capture modes; implicit ownership-sensitive captures are rejected; borrowed captures cannot escape; compiler-managed cells for mutated `Copy` locals remain allowed. Safe sources reject `RawPtr` and inline IR unless they opt into `// unsafe`. Remaining precision work is richer lifetime dataflow for more nonescaping borrow cases and executable dynamic drop flags for conditional/open obligations.
2. **Lower (Semantic MIR + typed AST payloads → λ_G, CPS):** every Talk function becomes a CPS λ_G function (extra `ret` continuation parameter; `mut func` methods have an internal mutable `self` receiver and `ret` takes `[result, Self]`). The MIR lowering consumer in `src/lower/mir_lowering.rs` is the only body/control-flow driver: blocks, branches, switches, loops, source returns, block-tail values, handler scopes, abort-capable call splits, resumable perform splits, and outer-loop `break`/`continue` exits are represented in MIR and consumed from MIR. Typed AST nodes remain as payloads for expression lowering, call resolution, pattern-match compilation, source IDs, and type lookup. `if`/`match` lower to `br`/`switch` over join continuations (Maranget trees emit the switch nests); loops are recursive continuations; locals are let-bound expressions (sharing via hash-consing); deterministic local scope and MIR-static assignment-replacement drops lower to ordered λ_G `free` glue where a managed storage wrapper exposes a `RawPtr`. `@_ir` splices become PrimOps ($n → lowered bind exprs, %n → parameter extracts, type args θ-resolved). Mono worklist keyed (Symbol, concrete type args) from `instantiations` ∘ θ; `member_resolutions` resolve to witness/default/derived function labels; derived `show` and memberwise inits synthesized as λ_G functions. String literals → static_mem + String record. Unhandled `'io` performs → `io_perform` PrimOp (total dispatch); handled performs → apply the statically-known handler capability (+ scope-end continuation for aborts, resumption continuation for resumable handlers).
3. **IR passes:** β-inline trivial wrappers (single-PrimOp bodies — the operator witnesses; paper §3.4 machinery), assignment conversion (mutated ∩ captured → cells), closure conversion of functions with unknown occurrences (η-expansion first where a function has both known and unknown occurrences, §3.5.1); verifier (T-Prog + WF) after every pass.
4. **Schedule (λ_G → bytecode):** nesting tree (+ sibling SCCs) per §4; each non-continuation function becomes a bytecode chunk; its nested well-known continuations become blocks; applications of ret-continuations become `Ret`, of sibling continuations become jumps, of functions become `Call` (Thorin-style reconstruction); λ_G variables/extracts get registers (naive per-chunk assignment v1); `br`/`switch` become terminators.
5. **VM:** register frames, match dispatch, `Rc`/CoW values, byte heap with allocation records, slot arena, `IO` trait (StdioIO/CaptureIO/wasm stub, ported from a41ff388 — CaptureIO's fd loopback is load-bearing).
6. **Reference evaluator:** paper §3.4 semantics over λ_G directly — the trusted baseline the VM is compared against, and the executable spec for every lowering milestone before the scheduler exists.

## Module layout (~7k + tests)

```
src/lambda_g/            the calculus (paper core)
  expr.rs                hash-consed exprs, LV/LF at construction          ~350
  program.rs             label map, functions, Unset, mutation + UF        ~250
  fv.rs                  mark/run fixed-point FV cache + invalidation      ~300   (§3.1.1; Table 1 as test)
  sets.rs                hash-consed ordered arrays (trie = later path)    ~200   (§5.1)
  subst.rs               dependency-aware substitution + β-reduction       ~350   (§3.3–3.4)
  eta.rs                 η-expansion, known/well-known analysis            ~150   (§3.5)
  nest.rs                nesting tree, sibling deps, SCCs, virtual root    ~300   (§4, Fig. 8)
  check.rs               T-* rules + WF verifier                           ~250
  print.rs               paper-style text (`hi ↦ λ int → ⊥. …`) for show_ir ~250
  eval.rs                reference evaluator (E-App/E-β)                   ~250
src/lower/               Semantic MIR + typed AST payloads → λ_G
  mod.rs                 worklist, θ, expressions, calls, effects, types    ~4150
  statements.rs          block entry, assignment, drop helpers               ~650
  mir_lowering.rs        Semantic MIR body/control flow → λ_G               ~800
  patterns.rs            Maranget decision trees
  derive.rs              derived Showable/memberwise functions
src/mir/
  mod.rs                 typed AST → source-near semantic CFG MIR           ~1100
src/ownership/
  mod.rs                 ownership, borrow, and drop elaboration over MIR   ~4500
src/vm/
  schedule.rs            nesting-tree → chunks/blocks/registers            ~450
  bytecode.rs            encoding, jump patching, pools                    ~350
  value.rs / heap.rs / interp.rs / io.rs                                   ~1800
```

## Testing (TDD)

1. M0 failing tests: paper examples as fixtures — Fig. 3b/c FV table (Table 1 transitions, including the xj mutation/invalidation episode), Fig. 4 iter/pow nesting forest, Fig. 5/6 WF, β-peeling of Fig. 3.
2. Reference-evaluator expectations per lowering construct; the bytecode VM runs the same programs and must agree with the evaluator.
3. `interpret(src) -> (Value, stdout)` integration helper; per-example expected stdout in `examples/expected/*.stdout` under CaptureIO (server examples scripted at the IO milestone).
4. Verifier (T-Prog + WF) asserted after every pass in tests and debug builds.

## Milestones

| M | Contents | Unlocks |
|---|---|---|
| M0 | λ_G core: exprs/program/FV/sets/subst/β/check/print/eval; paper fixtures green | calculus unit tests |
| M1 | AST→λ_G: literals/lets/blocks/if(br)/calls(CPS)/@_ir splices; mono worklist; wrapper β-inlining; runs on **reference evaluator** | `2+3*3`, Fib, Identity via evaluator; REPL eval (slow path) |
| M2 | nesting tree + scheduler + bytecode + VM core; VM must agree with the evaluator | Fib/Identity/Loop on the VM; `talk run` |
| M3 | strings/statics, structs, inits, field access + inout write-back via ret-tuples, io_perform print, multi-file | HelloWorld, Strings, Struct, Imports/Exports |
| M4 | enums (variant/get_tag/switch), Maranget, record patterns, Optional | MatchBind, StructuralTyping |
| M5 | generic structs (Array; fix `_alloc` sizing), conditional conformance, Iterable/for, slot arena | Array, Sum, Iteratin, ForLoop, Protocols |
| M6 | closure conversion + cells + trailing blocks; derived Showable | AnonFunc, Capture, TrailingBlock, Show |
| M7 | abort effects (handler refs + scope-end continuations) | Effects |
| M8 | full IO surface; scripted server tests; wasm run_program/show_ir | FileIO, Sleep, Chat*, Http, WebApi, Website |
| M9 | resumable handlers / yield / 'async (perform continuation passed to handler; one-shot) | future async stdlib |

## Critical files

- New: `src/lambda_g/*`, `src/lower/*`, `src/vm/*`, `tests/examples.rs`, `examples/expected/*.stdout`.
- Modified: `src/compiling/driver.rs` (Lowered phase), `src/compiling/core.rs` (cache typed artifacts), `src/bin/talk.rs`, `src/repl.rs`, `wasm/src/lib.rs`, `src/lib.rs`, `core/Memory.tlk`+`core/Array.tlk` (M5 alloc fix).
- Read-only contracts: `src/types/output.rs`, `src/types/catalog.rs`, `src/parsing/node_kinds/inline_ir_instruction.rs`, `src/name_resolution/name_resolver.rs`, `ssa-paper.md` (canonical λ_G spec).

## Verification

`cargo test` green per milestone; verifier clean after every IR pass; VM agrees with the reference evaluator on all lowering fixtures; end state: every example runs under CaptureIO matching its frozen expected output; `talk run` works natively; wasm `run_program`/`show_ir` live (show_ir prints λ_G text).
