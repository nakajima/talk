#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")/.."

output_dir="${TALK_FRONTEND_VM_STATS_DIR:-profiles/frontend-vm}"

usage() {
  cat <<'EOF'
Usage: scripts/frontend-vm-stats.sh [--output-dir DIR]

Builds the self-hosted frontend twice, records each stage's optimization
counts, runs the stable frontend source corpus with exact VM instruction
statistics, and writes a commit-addressed report.
EOF
}

while (($#)); do
  case "$1" in
    --output-dir)
      if (($# < 2)); then
        echo "error: --output-dir requires a directory" >&2
        exit 2
      fi
      output_dir="$2"
      shift 2
      ;;
    -h|--help)
      usage
      exit 0
      ;;
    *)
      echo "error: unknown argument: $1" >&2
      usage >&2
      exit 2
      ;;
  esac
done

mkdir -p "$output_dir"

commit=$(git rev-parse HEAD)
short_commit=$(git rev-parse --short=12 HEAD)
status=$(git status --porcelain=v1 --untracked-files=all -- . \
  ':(exclude)profiles/frontend-vm/**')

if [[ -n "$status" ]]; then
  worktree=dirty
  fingerprint=$(
    {
      git diff --binary HEAD -- . ':(exclude)profiles/frontend-vm/**'
      git ls-files --others --exclude-standard | sort | while IFS= read -r path; do
        case "$path" in
          profiles/frontend-vm/*) continue ;;
        esac
        printf '%s\n' "$path"
        sha256sum "$path"
      done
    } | sha256sum | awk '{print $1}'
  )
  result_id="${short_commit}-dirty-${fingerprint:0:12}"
else
  worktree=clean
  fingerprint=none
  result_id="$short_commit"
fi

output="$output_dir/$result_id.txt"
body=$(mktemp)
report=$(mktemp)
trap 'rm -f "$body" "$report"' EXIT

previous=$(find "$output_dir" -maxdepth 1 -type f -name '*.txt' ! -path "$output" \
  -printf '%T@ %p\n' 2>/dev/null | sort -nr | head -1 | cut -d' ' -f2-)

export TALK_FRONTEND_VM_STATS_OUTPUT="$body"
echo "== building and profiling frontend candidate =="
cargo test --locked --lib \
  compiling::frontend::tests::write_vm_stats_profile \
  -- --ignored --exact --nocapture

generated_at=$(date -u +'%Y-%m-%dT%H:%M:%SZ')
rustc_version=$(rustc --version)
host=$(uname -srm)

{
  echo "frontend_vm_stats_format: 2"
  echo "commit: $commit"
  echo "worktree: $worktree"
  echo "worktree_fingerprint: $fingerprint"
  echo "generated_at: $generated_at"
  echo "rustc: $rustc_version"
  echo "host: $host"
  echo
  cat "$body"
} > "$report"

mv "$report" "$output"
echo
echo "wrote $output"
if [[ -n "$previous" ]]; then
  echo "compare with: diff -u '$previous' '$output'"
fi
