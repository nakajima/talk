# 0068 - Clause-derived suspension

Status: accepted, implemented (bytecode format 10; the `'suspending`
marker, its grammar reservation, ABI slot, and both blocking-fallback
trampolines are gone)

## Context

ADR 0064 introduced one-shot resumptions behind a declaration-site
marker: `pub effect 'pause() -> () 'suspending`. The marker decides,
per effect, which of two clause protocols every handler must use —
ADR 0011's call protocol (`'continue` returns to the perform site) or
ADR 0064's capture protocol (the clause binds a `Resumption<R, A>`).
Living on the declaration, far from the clauses it governs, the bit
must be ferried through every layer, and each leg of the trip is its
own special case:

- the lexeme `suspending` is string-compared in three places in
  `stdlib/syntax/Parser.tlk` so `-> () 'suspending` parses in bare row
  positions — it looks like a row entry but is not one, silently
  reserves the name, and accepts repetition;
- an 8th `Bool` on `effect_decl` crosses the frontend ABI as
  positional slot 7 with a defaulted absence, which every AST consumer
  must know to preserve (the formatter didn't — dropping the marker
  changes which protocol the checker demands of every handler);
- the checker carries `EffectSig.suspending`, publishes
  `EffectContract.suspending` at both perform and handle sites, and
  forks the clause typing (binder arity, body type, `'continue`
  rejection) on it;
- MIR forks both the perform lowering (`Inst::Suspend` beside
  `FindHandler` + call) and the `#handle` lowering (delimiter, env
  base, k binder) on it;
- the VM's `Insn::Suspend` re-implements the stale-entry trim and
  nearest-live handler search that `Insn::FindHandler` already
  performs.

The marker also misprices the machinery it guards. The same park
effects are handled blocking-style in `core/Host.tlk` and
capturing-style in `stdlib/coop.tlk`, but the declaration forces both
into the capture protocol — so the blocking fallbacks, whose entire
job is "block the worker, then continue," must reify a resumption per
park and trampoline through the `HostPark` enum to avoid the
resume-inside-a-clause stack tower. And because `Inst::Suspend` is
emitted unconditionally at perform sites, the C target's resumable
fixpoint (ADR 0065) heap-frames every channel-touching function even
in programs whose only handlers are the blocking fallbacks.

Three facts make the concept removable outright:

- **`'continue` is a terminator** (the checker types it divergent), so
  every call-protocol clause is tail-resumptive by construction —
  control never returns to a clause after it continues.
- **Abort is already cancel-plus-return**: a clause that completes
  without consuming its resumption delivers its value where the
  installer would have returned (ADR 0064 §4, deliberately the
  existing abort typing), and `cancel` unwinds through the same
  ADR 0027 cleanup entries the abort path uses.
- **The floor discipline equalizes the two protocols**: a call-protocol
  clause runs at the perform site over the live extent, a capture
  clause at the installer with the extent removed, but both search for
  handlers under the same floor and therefore see the identical
  handler environment.

So the call protocol is not a second semantics — it is the standard
tail-resumptive optimization of the suspend semantics, applicable to
exactly the clauses that use it today.

## Decision

1. **One handler semantics: every perform suspends its extent, and the
   clause decides what happens to it.** `'continue v` is the implicit
   tail-resume; completing without resuming cancels the extent and
   aborts with the clause's value; binding the resumption reifies the
   suspended extent as a value. This is the model of Koka (every
   operation semantically yields; clauses are `fun` or `ctl`) and of
   OCaml's effect handlers (every handler receives a one-shot
   continuation), with the in-place execution of tail-resumptive
   clauses proven sound by Xie & Leijen (ICFP 2021).

2. **The classification is derived from the clause, and the marker is
   deleted.** A `#handle` clause that binds `params + 1` binders is a
   resumption-binding clause; its final binder is typed
   `Resumption<R, A>` exactly as today (the construction in
   `stmt.rs` survives verbatim — only its trigger changes from
   `sig.suspending` to the binder count). Zero or `params` binders is
   a tail-resumptive clause with `'continue`, as today. The arity is
   unambiguous against both existing forms, misuse is loud through
   existing machinery (the binder types as `Resumption`, linearity
   forces it to be consumed, and the `'continue`-in-a-binding-clause
   diagnostic keys off the same classification), and the entire
   carrier chain retires: the parser lexeme reservation, the AST
   `Bool`, ABI slot 7, `EffectSig.suspending`, and both
   `EffectContract.suspending` publications. Effect declarations are
   uniform; any effect may be handled either way, and the same effect
   may be handled both ways in one program — which the Host/coop split
   already wants.

3. **Both lowerings survive; the dispatch unifies.** Tail-resumptive
   clauses keep ADR 0011's call protocol byte-for-byte — it is the
   optimization, not a protocol. Resumption-binding clauses keep
   ADR 0064's capture lowering. `PushHandler` records the clause kind
   (one field, known at the `#handle` from the clause shape), perform
   sites compile to one sequence, and the VM branches on the entry
   kind — entering the existing capture body or the existing call
   protocol — which deletes `Insn::Suspend`'s duplicated handler
   search. On the C target, perform sites of effects with any
   resumption-binding clause emit both paths behind the entry-kind
   branch; since such effects can carry neither type generics nor
   `mut` performs (point 5), both paths handle plain payloads only.

4. **The resumable fixpoint seeds from the handler census.** ADR 0065's
   whole-program fixpoint is unchanged except its seed: instead of
   "functions containing `Inst::Suspend`," it marks performs of
   effects that have at least one resumption-binding clause anywhere
   in the finalized program, with the same conservative closure rule.
   Effects handled only tail-resumptively — `'io`, `'alloc`, and every
   park effect in a blocking-only program — never seed, so such
   programs compile with no heap frames at all: the cost tracks the
   paths that can actually be captured, not the paths that were
   declared capturable.

5. **The ADR 0064 phase-1 restrictions relocate to the classification
   site — and all of them turn out clause-local.** A resumption-binding
   clause is rejected for an effect with type generics or with `mut`
   parameters, and the borrowed-installer-params rejection already
   lives at the clause. Static generics are the exception established by
   ADR 0035: the operation identity and clause are monomorphized, so no
   static evidence crosses the suspension boundary. No whole-program
   consistency check is needed: `mut`-ness is a declaration fact (a
   call-site `mut` marker demands an exclusive-borrow parameter, and
   effect parameters lower their declared modes into the signature), so
   "bindable" is derivable from the `EffectSig` alone and perform lowering
   reads it off the published contract — non-bindable effects (type
   generics, `mut` parameters) keep the call protocol statically, which is
   also why the branch arms never carry witness blocks or writebacks.

6. **The Host trampoline dissolves.** The blocking park fallbacks in
   `core/Host.tlk` become three-line `'continue` clauses
   (register → park → unregister → continue); `HostPark`,
   `_host_extent`, and the resume loop delete. The `coop` scheduler is
   unchanged — its clauses already bind `k` and return `TaskStep`
   values, which is precisely the derived classification.

## Consequences

- The concept "suspending effect" leaves the language: one handler
  semantics, one classification derived from what the clause already
  states, and a net-negative diff across parser, AST, ABI, catalog,
  checker, MIR, and VM.
- Existing `'continue` clauses keep their exact lowering and cost;
  existing resumption-binding handlers keep theirs. The observable
  change is where machinery was forced, not chosen: every blocking
  park stops paying segment capture, and blocking-only programs stop
  paying the C heap-frame tax.
- The trade: "this effect never suspends" is no longer a declaration
  guarantee but a derived whole-program fact. Adding a
  resumption-binding clause for an effect widens the resumable set at
  a distance — the same action-at-a-distance the fixpoint already
  accepts for address-taken closures, and one the census makes
  precise rather than assumed.
- One-shot linearity, `resume`/`cancel` as core functions, and the
  ADR 0065 native divergence (a suspension crossing a resumption
  boundary traps) are all untouched.
- Bootstrap churn is real and mechanical: the grammar change requires
  frontend artifact regeneration (`talk bootstrap`), ABI slot 7
  retires with the descriptor, and `PushHandler`'s new field bumps the
  bytecode format.

## Validation

1. The ADR 0064 corpus (generator roundtrip, stepper interleave,
   cancel-releases) is green on both targets with the markers deleted
   from every declaration — the clauses alone carry the semantics.
2. The channel/timer/select behavioral pins (ADR 0067) hold with the
   Host fallbacks rewritten as `'continue` clauses, and the emitted C
   for a blocking-only channel program contains no resumable
   functions (pinned).
3. A program handles the same effect tail-resumptively in one extent
   and with a bound resumption in another; both dynamic routes through
   one perform site behave per their clause, VM and C.
4. Diagnostics: an unconsumed final binder is a linearity error;
   `'continue` inside a resumption-binding clause keeps its dedicated
   diagnostic; a resumption-binding clause for a type-generic effect and
   a `mut`-argument perform of a bound-handled effect reject with the
   relocated messages.

## Relationship to existing decisions

- **ADR 0011:** the call protocol survives unchanged as the
  tail-resumptive case; `'continue` keeps its syntax and typing.
- **ADR 0027:** the shared abort/cancel unwinding is what makes
  clause-completion mean one thing under one semantics.
- **ADR 0039:** strengthened — no effect is compiler-privileged, and
  now none is declaration-privileged either.
- **ADR 0064:** semantics preserved exactly; the declaration marker it
  introduced (and its stated rationale, that native lowering would key
  on it) retires — the backend keys on the handler census instead.
- **ADR 0065:** emission unchanged; only the fixpoint's seed moves.
- **ADR 0067:** the direct-style surface is unchanged; its Host
  fallbacks simplify and its scheduler is untouched.
- **ADR 0053:** the one-catalog model is what makes the whole-program
  census and the `mut`-consistency check a lookup rather than a link
  step.

## References

- Xie and Leijen, *Generalized Evidence Passing for Effect Handlers:
  Efficient Compilation of Effect Handlers to C*, ICFP 2021 —
  tail-resumptive operations execute in place, no capture.
- *The Koka Programming Language* (book, §handlers) — the per-clause
  `fun`/`ctl` split: `fun` clauses are tail-resumptive and called
  in-place; `ctl` clauses receive the resumption. The clause, not the
  effect declaration, chooses.
- Sivaramakrishnan, Dolan, White, Kelly, Jaffer, and Madhavapeddy,
  *Retrofitting Effect Handlers onto OCaml*, PLDI 2021 — one-shot
  continuations with `continue`/`discontinue`; no declaration-site
  suspension marker.
- Plotkin and Pretnar, *Handlers of Algebraic Effects* — the handler,
  not the operation, gives effects their meaning.
