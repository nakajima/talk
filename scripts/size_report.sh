#!/bin/bash
# Backend size accounting against the ADR 0034 budget.
#
# Counts non-blank, non-comment Rust lines in three categories, reported
# separately so reductions cannot be manufactured by moving lines between
# them (docs/adr/0034-lean-bytecode-backend-architecture.md). After the
# ADR 0047 crate extraction the modules are:
#   1. compiler MIR work (src/compiling/mir) and the public MIR data
#      (talk-mir/src);
#   2. target adapters (talk-bytecode/src, talk-c/src) and the reused
#      runtime (talk-vm/src, talk-native-runtime/src);
#   3. seam additions since the frontend-only base a1d20d27 (driver, CLI,
#      core cache, embeddings) — added lines only, from a read-only git diff.
#
# Budget (docs/adr/0034-lean-bytecode-backend-architecture.md): 13,400
# production lines at full parity, 50% of the archived baseline's 26,798.
set -euo pipefail
cd "$(dirname "$0")/.."

BASE=a1d20d27
BUDGET=13400

count_files() {
  find "$@" -name '*.rs' 2>/dev/null | while read -r f; do
    awk '/^[[:space:]]*$/{b++;next} /^[[:space:]]*\/\//{c++;next} {n++}
         END{printf "%d %d %d\n", n+0, c+0, b+0}' "$f"
  done | awk '{p+=$1;c+=$2;b+=$3} END{printf "%d %d %d\n", p+0, c+0, b+0}'
}

split_tests() { # production vs #[cfg(test)] tail, code lines only
  find "$@" -name '*.rs' 2>/dev/null | while read -r f; do
    awk '/#\[cfg\(test\)\]/{t=1}
         /^[[:space:]]*$/{next} /^[[:space:]]*\/\//{next}
         {if(t) tl++; else pl++} END{printf "%d %d\n", pl+0, tl+0}' "$f"
  done | awk '{p+=$1;t+=$2} END{printf "%d %d\n", p+0, t+0}'
}

echo "== compiler MIR work (src/compiling/mir) =="
read -r prod comments blanks <<<"$(count_files src/compiling/mir)"
read -r prod_split test_split <<<"$(split_tests src/compiling/mir)"
echo "code=$prod (production=$prod_split, in-file tests=$test_split) comments=$comments blanks=$blanks"
backend=$prod_split

echo "== public MIR data (talk-mir/src) =="
read -r prod comments blanks <<<"$(count_files talk-mir/src)"
read -r prod_split test_split <<<"$(split_tests talk-mir/src)"
echo "code=$prod (production=$prod_split, in-file tests=$test_split) comments=$comments blanks=$blanks"
backend=$((backend + prod_split))

echo "== bytecode adapter (talk-bytecode/src) =="
read -r prod comments blanks <<<"$(count_files talk-bytecode/src)"
read -r prod_split test_split <<<"$(split_tests talk-bytecode/src)"
echo "code=$prod (production=$prod_split, in-file tests=$test_split) comments=$comments blanks=$blanks"
backend=$((backend + prod_split))

echo "== C adapter (talk-c/src) =="
read -r prod comments blanks <<<"$(count_files talk-c/src)"
read -r prod_split test_split <<<"$(split_tests talk-c/src)"
echo "code=$prod (production=$prod_split, in-file tests=$test_split) comments=$comments blanks=$blanks"
backend=$((backend + prod_split))

echo "== reused runtime (talk-vm/src) =="
read -r rprod rcomments rblanks <<<"$(count_files talk-vm/src)"
echo "code=$rprod comments=$rcomments blanks=$rblanks"

echo "== shared native runtime (talk-native-runtime/src) =="
read -r nprod ncomments nblanks <<<"$(count_files talk-native-runtime/src)"
echo "code=$nprod comments=$ncomments blanks=$nblanks"

echo "== seam additions since $BASE (non-backend, non-test .rs) =="
seams=$(git diff "$BASE" --numstat -- 'src/bin' 'src/cli' 'src/compiling' 'src/repl.rs' 'wasm/src' 'talk-ffi/src' 'talk-vm/src' \
  | awk '{a+=$1} END{print a+0}')
echo "added_lines=$seams (includes comments/blanks; upper bound)"

total=$((backend + rprod + seams))
echo
echo "== total against budget =="
echo "backend=$backend runtime=$rprod seams<=$seams total<=$total budget=$BUDGET remaining>=$((BUDGET - total))"
