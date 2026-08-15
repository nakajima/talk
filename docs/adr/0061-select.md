# 0061 - select

Status: accepted (implemented 2026-08-08 — `Either`, `Select2`, and
`select2` in stdlib `task`; corpus pin tests/programs/select_channels.tlk;
no runtime changes)

## Context

ADRs 0050 and 0059 deferred `select` behind one obligation: prove that a
losing waiter cannot lose a wake or a value. Classic executors claim a
value at wake time (the woken waiter owns it), so racing waiters need a
handoff protocol. This design never did that: an ADR 0059 wake is a
broadcast readiness hint, values are claimed only at poll time under the
status check, and spurious re-polls are legal. The proof obligation
dissolved before select existed.

## Decision

1. **`select2(a, b)` is an ordinary stdlib future** — `Select2<A, B>` with
   `Output = Either<A.Output, B.Output>` — that polls `a` then `b` with its
   own context. No runtime operation, no bytecode, no executor change.

2. **Left bias is the tie rule.** When both children are ready in one
   poll, `a` wins — deterministic and documented, not fair. Fairness
   rotation is a caller concern (swap the arguments) until real demand
   arrives.

3. **Losing is dropping.** `ready` from one child completes the select;
   the loser stays inside the `Select2` value and cancels through its own
   drop when the select drops — for a pending `Recv`, the ADR 0059
   unregister-on-drop path, `DropToken`-gated (ADR 0060). A value the
   loser never claimed stays queued for the next receive.

4. **Why no wake is lost:** each pending child registered its own external
   wait; the executor parks only after re-checking every registered
   channel under the registry lock (ADR 0059's check-then-park); any send
   or close broadcasts; a woken select re-polls both children. A child
   woken for a value another waiter drained re-registers and re-parks —
   the spurious-wake law, doing the work a claim protocol would.

## Consequences

- Select composes with everything already built: `select2(recv, sleep)`
  is the timeout pattern once ADR 0063 lands timers.
- N-ary and fair select remain follow-ups; both are surface sugar over
  this shape, not new machinery.

## Validation

1. Ready-vs-pending resolves to the ready side; both-ready resolves left
   (corpus, all backends).
2. A select parked on two empty channels wakes and resolves when either
   side's producer sends, cross-worker (corpus).
3. The loser's registration dies with the select: a later poll round
   reports genuine deadlock rather than parking on a stale registration.

## Relationship to existing decisions

- **ADR 0050:** the poll laws made select a plain combinator.
- **ADR 0059:** broadcast wakes + poll-time claiming discharge the
  lost-wake obligation; drop-cancellation reuses `Recv`'s.
- **ADR 0060:** loser cancellation is exactly-once via `DropToken`.
