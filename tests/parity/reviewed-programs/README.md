# Reviewed replacement program oracles

These files record deliberate post-reset behavior changes without modifying the
frozen output captured from `pre-backend-reset-2026-07-13`.

`handlers.stdout` replaces the old CLI implementation detail `I64(0)` with the
Talk-syntax final result `0` under TOOL-06. All preceding program output and the
trailing newline remain byte-for-byte unchanged.
