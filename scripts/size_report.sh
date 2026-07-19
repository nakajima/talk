#!/bin/bash
# Backend size accounting against the ADR 0034 budget.
#
# Counts non-blank, non-comment Rust lines in three categories, reported
# separately so reductions cannot be manufactured by moving lines between
# them (lean-backend-rebuild-plan.md, "What success means"):
#   1. backend modules (src/backend);
#   2. reused runtime (talk-runtime/src);
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

echo "== backend modules (src/backend) =="
read -r prod comments blanks <<<"$(count_files src/backend)"
read -r prod_split test_split <<<"$(split_tests src/backend)"
echo "code=$prod (production=$prod_split, in-file tests=$test_split) comments=$comments blanks=$blanks"
backend=$prod_split

echo "== reused runtime (talk-runtime/src) =="
read -r rprod rcomments rblanks <<<"$(count_files talk-runtime/src)"
echo "code=$rprod comments=$rcomments blanks=$rblanks"

echo "== seam additions since $BASE (non-backend, non-test .rs) =="
seams=$(git diff "$BASE" --numstat -- 'src/bin' 'src/cli' 'src/compiling' 'src/repl.rs' 'wasm/src' 'talk-c/src' 'talk-runtime/src' \
  | awk '{a+=$1} END{print a+0}')
echo "added_lines=$seams (includes comments/blanks; upper bound)"

total=$((backend + rprod + seams))
echo
echo "== total against budget =="
echo "backend=$backend runtime=$rprod seams<=$seams total<=$total budget=$BUDGET remaining>=$((BUDGET - total))"
