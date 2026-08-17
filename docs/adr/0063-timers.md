# 0063 - Timers

Status: accepted, implemented; direct-style and nanosecond amendments from
ADR 0067 are incorporated below

## Context

A timer is a worker wake source whose readiness comes from a monotonic clock
rather than another worker. The runtime needs one clock, worker-local deadline
registrations, and a park operation bounded by the earliest deadline.

## Decision

1. **`sleep(Duration)` is direct-style.** It computes an absolute
   `Instant` deadline, checks that clock, and performs
   `'wait_until(deadline:)` until the deadline has passed. Spurious wakes are
   legal because the loop re-checks the clock.

2. **Deadlines are worker-local registrations.** Channel interests and timer
   deadlines are both reasons a worker may block. Runtime park computes the
   earliest registered deadline and uses it as the wait timeout; registering
   and unregistering use the existing `chan_ctl` surface.

3. **The clock and deadline unit is nanoseconds.** `Instant.now`, control op
   13, and deadline ops 14/15 use the same monotonic anchor. Native reads
   `CLOCK_MONOTONIC`; the VM routes both surfaces through its IO clock; wasm
   scales `Date.now` to nanoseconds but retains the browser's millisecond
   resolution. Wall-clock calendars remain host-effect territory.

4. **Wait precision follows the host primitive.** Rust condition variables
   and native `pthread_cond_timedwait` receive nanosecond durations. A host
   with coarser resolution may wake late, never early. Single-threaded wasm
   busy-waits to the earliest deadline because blocking its only thread is
   necessarily a spin.

## Consequences

- Sub-millisecond durations are preserved end to end; there is no conversion
  to integer milliseconds at the Talk/runtime boundary.
- No timer wheel is needed: registration lists are worker-sized and scanned
  when parking.
- Timer waiting composes with channel waiting through the same registration
  and wake path.

## Validation

1. `sleep(duration)` returns no earlier than its monotonic deadline on VM and
   C.
2. A 100-microsecond sleep retains and satisfies its sub-millisecond deadline
   on both backends.
3. Channel waits and worker-delayed sends continue to compose with timers.

## Relationship to existing decisions

- **ADR 0059:** timers are a second wake source using the same
  check-then-park protocol.
- **ADR 0067:** direct-style `wait_until` replaces the retired future surface.
- **ADR 0039:** monotonic instants are host-backed; wall-clock time remains a
  separate concern.
