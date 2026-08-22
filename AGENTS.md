## How to finish work

**Finish the feature.** Don't stop at the first viable point and hand back a
deferral list. The only acceptable stops: (a) a hard external blocker — name
it in one line; (b) a concern this file marks as wanting its own session
(shape bounds, param inference, spans). If a task decomposes, complete every
part.

**Work as a stack of small drafts** (rev, not git — `rev llm` for the
manual; this repo is draft-only, human merges). There is almost always
already an open draft when you start — land your first coherent green step
into it with `rev save -m`; do NOT open a new draft first. Run
`rev draft -s "title"` only to stack the *next* coherent step on top (titles
starting with `-` need `--`). Each draft: gate green, real description
(`rev describe "..."` — design rationale + genuine blockers only, no
wishlist; avoid backticks, bash eats them). If a draft's description is a
prompt, follow it, then replace it when done. Keep stacking until the
feature is done — human reviews the whole stack, not each draft. `.ignore`
covers `cove`: if `./cove` won't exec, rebuild via bare `cove build`; if that
fails too, stop and report.
