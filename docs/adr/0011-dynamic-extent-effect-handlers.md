# 0011 — Dynamic-extent effect handlers compile capability-passing CPS

Status: implemented (2026-07-03)

## Context

Handler routing was decided **lexically at name resolution**: a perform
routed to a handler only when the `@handle` sat in an ancestor lexical
scope (`lookup_handler_in_scope`), recorded per perform node in
`resolved.effect_handlers`. A handler installed in a *caller* never
covered a perform in a callee — `examples/Throwsies.tlk` fell through to
the IO fallback and died with "perform with a computed request". The
machinery behind the lexical scheme was heavy: the checker discharged
routed performs at the perform site and kept four side tables
(`performs_into`, `binder_refs`, `handlers_defined`,
`handler_payload_tys`); the lowerer ran a transitive abort analysis
(`collect_abortable`) and gave abort-capable functions a special calling
convention (an explicit normal-return continuation plus a return slot
reserved for abort propagation), with a statement-spine splitter for
resumable performs and abortable calls. Signatures depended on handler
sites (`abort_scope_ty` baked the handled scope's result type into every
intermediate slot), so one function could not perform into two handlers,
resumable performs were confined to the statement spine, and handlers
could not live in caller frames at all.

## Decision

Effects are **dynamic-extent**, compiled in capability-passing style:

- **Typing.** A perform always joins the ambient effect row; unannotated
  functions infer their latent effects (rows propagate through calls as
  before). `@handle 'e` delimits *the rest of its block*: the remaining
  statements check under the ambient row extended with `e`, so a callee
  row's `e` is absorbed at the handler boundary and never escapes the
  installing function (`Ctx::with_handled_effect`; the block walkers in
  `generate/func.rs`). Top-level ambient rows are **closed** over the
  core effects ('io, 'async, 'alloc — the runtime's implicit handler,
  identified by `ModuleId::Core`) plus prescanned top-level `@handle`s;
  a user effect reaching a closed row is `TypeError::UnhandledEffect` at
  the node where it tried to flow in. The zonked scheme rows are the
  single source of routing truth — no per-node tables.

- **Lowering.** A specialization takes one **capability parameter** per
  user effect in its row (sorted; between source params and `k` —
  `demand`/`lower_function`), and call sites supply them from `ctx.caps`
  (`lower_call`); a monomorphized evidence vector in the sense of Xie &
  Leijen. `@handle` builds the capability closure in the installing
  frame — its dom comes from `cap_dom_items`, shared with `demand`, so
  the types cannot drift — capturing the handled scope's return
  continuation (`ctx.raw_ret_k`) as its delimiter. The capability's
  final parameter is the **resumption**, which is also the λ_G calling
  convention's return slot: `continue v` compiles to the capability
  returning, and a perform passes its own continuation as the resumption
  (a Never effect passes a dead placeholder). Abort = the handler body
  finishing into the captured delimiter; the frames between the perform
  and the handled scope simply never resume. Nearest handler wins by
  construction (`ctx.caps` insertion order). Trailing blocks keep the
  caps of their creation site (Effekt-style lexical capture); function
  literals clear them and reject performs.

- **VM.** The bytecode machine gained the minimal M9 slice —
  `Value::Cont` (frame index + identity), `Insn::MakeCont` (reify the
  current frame's return), `Insn::CallCont` (unwind to the frame, then
  return from it) — one-shot, downward-only, validated by frame identity
  so an escaped handler traps cleanly instead of smashing the stack.
  The scheduler materializes a captured parent's ret slot as a `Cont`
  at index `arity` of the captured parameter tuple, and compiles a
  bare-value application of a computed callee to `CallCont`. Resumption
  needs no new machinery: the capability's `Ret` IS the resume.

Deleted outright: the resolver's handler scope-walk and `effect_handlers`
/ `effect_handler_definitions` maps; the checker's perform-site discharge
and all four capability tables; `collect_abortable`, `abort_shape`,
`abort_scope_ty`, the abort-capable calling convention (`normal_k`,
`abort_ok`, `local_handlers`, the `ret_normal` prologue), the statement
splitter (`try_mir_effect_split`, `rest_mir_closure`), `HandlerCap` /
`handler_caps`, `lower_routed_perform`, `abortable_callee`,
`normal_result_ty`.

## Consequences

- `Throwsies.tlk` runs as written: a caller-installed handler catches an
  unannotated callee's perform; nested handlers pick the nearest extent;
  one function can perform several effects under different handlers; and
  resumable performs work in any expression position, across frames
  (`tests/programs/{caller_locals_handler,nested_handlers,
  resume_across_frames,multi_effect_handlers}.tlk`).
- Callee signatures are handler-site-independent — the "performs into
  more than one handler" and "demanded before its handler is installed"
  restrictions are gone; mono keys are unchanged. This departs from
  Schuster et al. (PLDI 2022)'s answer-type-polymorphic slots: caps
  capture the delimiter continuation instead, sound because λ_G
  continuations are heap closures on the evaluator and reified one-shot
  `Cont`s on the VM.
- Aborts still skip frame cleanups (drops, region write-backs) between
  the perform and the delimiter — unchanged from the slot design;
  abort-heavy corpus programs sit in the container-leak fence until
  Track B lands.
- Residual v1 fences, all clean diagnostics: effectful functions as
  *values* (eta-expansion capturing caps is the follow-up), performs
  inside function literals, generic-effect handlers, a top-level `let`
  calling an effectful function before its `@handle` lowers to "perform
  before its handler is installed" (typing accepts it via the prescan —
  a documented order wart).
- One-shot is enforced dynamically by frame identity (multi-shot resume
  is out of scope; cells make it semantically fraught).

Citations: capabilities as first-class handler values — Brachthäuser,
Schuster & Ostermann, OOPSLA 2020; capability-passing CPS — Schuster,
Brachthäuser & Ostermann, ICFP 2020; typed CPS for lexical handlers —
Schuster et al., PLDI 2022 (departure noted above); CPS handlers,
resume-as-continuation — Hillerström, Lindley, Atkey & Sivaramakrishnan,
FSCD 2017; row-typed effects and inference — Leijen, Koka
(MSR-TR-2013-79); implicit top-level handler — Plotkin & Pretnar, LMCS
2013; per-effect evidence at call boundaries — Xie et al., ICFP 2020,
Xie & Leijen, ICFP 2021; abort-only as double-barrelled CPS — Thielecke,
HOSC 2002; one-shot stack slices — Hieb, Dybvig & Bruggeman, PLDI 1990.
