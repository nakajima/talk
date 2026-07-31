#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")/.."

usage() {
  cat <<'EOF'
Usage: scripts/c-backend-sweep.sh [--jobs N] [--cc PROGRAM] [PATH...]

Compiles every Talk program in the corpora twice -- once for the
interpreter, once through the C backend -- and fails if the two disagree
on a single byte of output.

This is the differential check that keeps the two targets honest. The
`cargo test` suite already gates the bench and tests/programs corpora;
this sweep adds the reference corpora and the examples, which are too
slow to put in the default suite.

A program the type checker rejects, or one with nothing to run, is
skipped -- neither reaches a backend. A program the C backend refuses is
a failure: coverage is complete, so a rejection is a regression.

  --jobs N      parallel workers (default: all cores)
  --cc PROGRAM  C compiler (default: $CC, else cc)
  PATH...       corpora to sweep (default: the full set)
EOF
}

jobs="$(getconf _NPROCESSORS_ONLN 2>/dev/null || echo 4)"
cc_program="${CC:-cc}"
paths=()

while [[ $# -gt 0 ]]; do
  case "$1" in
    --jobs) jobs="$2"; shift 2 ;;
    --cc) cc_program="$2"; shift 2 ;;
    -h|--help) usage; exit 0 ;;
    *) paths+=("$1"); shift ;;
  esac
done

if [[ ${#paths[@]} -eq 0 ]]; then
  paths=(bench tests/programs tests/reference examples)
fi

talk="target/release/talk"
if [[ ! -x "$talk" ]]; then
  echo "building the compiler first" >&2
  cargo build --release --locked
fi
talk="$PWD/$talk"

work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT

# Servers and interactive clients block on the network; they are compiled
# but not run.
compile_only='ChatClient|ChatServer|Http|WebApi|Website'

sweep_one() {
  local program="$1"
  local name
  name="$(printf '%s' "$program" | tr '/.' '__')"
  local emitted="$work/$name.src.c"
  local binary="$work/$name.bin"

  if ! "$talk" c "$program" >"$emitted" 2>"$work/$name.err"; then
    # A program with no entry never reaches a backend, and one the type
    # checker refuses is not this sweep's business. Anything else -- an
    # unsupported construct, an internal emitter error -- is a backend
    # failure, so ask the checker rather than pattern-matching the
    # message and letting unfamiliar errors through as skips.
    if grep -q "nothing to run" "$work/$name.err"; then
      printf 'skip %s\n' "$program"
      return 0
    fi
    if ! "$talk" check "$program" >/dev/null 2>&1; then
      printf 'skip %s\n' "$program"
      return 0
    fi
    printf 'BACKEND FAILED %s: %s\n' "$program" "$(head -1 "$work/$name.err")"
    return 1
  fi

  if ! "$cc_program" -O2 -std=c11 -Wall -Werror "$emitted" -o "$binary" 2>"$work/$name.cc"; then
    printf 'CC FAILED %s: %s\n' "$program" "$(grep -m1 'error:' "$work/$name.cc" || true)"
    return 1
  fi

  if [[ "$program" =~ $compile_only ]]; then
    printf 'compiled %s\n' "$program"
    return 0
  fi

  # Into files and compared byte for byte, including exit status.
  # Command substitution strips trailing newlines, so a difference in
  # trailing output would read as agreement; `|| true` would hide a
  # crash or a timeout the same way.
  local interpreted_status=0 compiled_status=0
  timeout 60 "$talk" run "$program" >"$work/$name.vm.out" 2>"$work/$name.vm.err" \
    || interpreted_status=$?
  timeout 60 "$binary" >"$work/$name.c.out" 2>"$work/$name.c.err" \
    || compiled_status=$?

  if [[ "$interpreted_status" -ne "$compiled_status" ]]; then
    printf 'STATUS MISMATCH %s: interpreter %d, compiled %d\n  interpreter stderr: %s\n  compiled stderr   : %s\n' \
      "$program" "$interpreted_status" "$compiled_status" \
      "$(head -c 200 "$work/$name.vm.err")" "$(head -c 200 "$work/$name.c.err")"
    return 1
  fi
  if ! cmp -s "$work/$name.vm.out" "$work/$name.c.out"; then
    printf 'MISMATCH %s\n  interpreter: %s\n  compiled   : %s\n' \
      "$program" \
      "$(head -c 200 "$work/$name.vm.out")" "$(head -c 200 "$work/$name.c.out")"
    return 1
  fi

  # stderr is program output too, so on a successful run it has to match
  # byte for byte. On a failing one it carries the diagnostic, and the
  # two targets word those differently by design (the interpreter adds
  # chunk and offset); there the requirement is only that both actually
  # said something.
  if [[ "$interpreted_status" -eq 0 ]]; then
    if ! cmp -s "$work/$name.vm.err" "$work/$name.c.err"; then
      printf 'STDERR MISMATCH %s\n  interpreter: %s\n  compiled   : %s\n' \
        "$program" \
        "$(head -c 200 "$work/$name.vm.err")" "$(head -c 200 "$work/$name.c.err")"
      return 1
    fi
  elif [[ ! -s "$work/$name.vm.err" || ! -s "$work/$name.c.err" ]]; then
    printf 'SILENT FAILURE %s: both targets must diagnose a failure\n  interpreter: %s\n  compiled   : %s\n' \
      "$program" \
      "$(head -c 200 "$work/$name.vm.err")" "$(head -c 200 "$work/$name.c.err")"
    return 1
  fi
  printf 'ok %s\n' "$program"
}
export -f sweep_one
export talk work cc_program compile_only

programs="$(find "${paths[@]}" -name '*.tlk' | sort)"
total="$(printf '%s\n' "$programs" | wc -l | tr -d ' ')"
echo "sweeping $total programs with $jobs workers, cc = $cc_program"

if printf '%s\n' "$programs" | xargs -P "$jobs" -I{} bash -c 'sweep_one "$@"' _ {} > "$work/log" 2>&1; then
  status=0
else
  status=1
fi

agreed="$(grep -c '^ok ' "$work/log" || true)"
compiled="$(grep -c '^compiled ' "$work/log" || true)"
skipped="$(grep -c '^skip ' "$work/log" || true)"
grep -vE '^(ok|skip|compiled) ' "$work/log" || true
echo "--- $agreed agreed, $compiled compiled only, $skipped skipped, of $total ---"

if [[ "$status" -ne 0 ]]; then
  echo "the C backend and the interpreter disagree" >&2
  exit 1
fi
