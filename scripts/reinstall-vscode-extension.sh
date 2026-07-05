#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
extension_dir="$repo_root/dev/editors/vscode"
vsix_path="${VSIX_PATH:-$repo_root/.tmp/talktalk.vsix}"

resolve_code_bin() {
  if [[ -n "${CODE_BIN:-}" ]]; then
    command -v "$CODE_BIN" 2>/dev/null || return 1
    return 0
  fi

  for name in code code-insiders codium; do
    if command -v "$name" >/dev/null 2>&1; then
      command -v "$name"
      return 0
    fi
  done

  local ps_snapshot
  ps_snapshot="$(mktemp)"
  ps -eo args= >"$ps_snapshot"

  local server_dir candidate
  for server_dir in \
    "$HOME"/.vscode-server/cli/servers/* \
    "$HOME"/.vscode-server-insiders/cli/servers/* \
    "$HOME"/.vscode-oss-server/cli/servers/*
  do
    candidate="$server_dir/server/bin/remote-cli/code"
    if [[ -x "$candidate" && "$candidate" != *.staging/* ]] && grep -F -- "$server_dir/" "$ps_snapshot" >/dev/null 2>&1; then
      rm -f "$ps_snapshot"
      printf '%s\n' "$candidate"
      return 0
    fi
  done
  rm -f "$ps_snapshot"

  local candidate
  if [[ -n "${VSCODE_AGENT_FOLDER:-}" ]]; then
    for candidate in \
      "$VSCODE_AGENT_FOLDER"/bin/*/bin/remote-cli/code \
      "$VSCODE_AGENT_FOLDER"/cli/servers/*/server/bin/remote-cli/code
    do
      if [[ -x "$candidate" && "$candidate" != *.staging/* ]]; then
        printf '%s\n' "$candidate"
        return 0
      fi
    done
  fi

  for candidate in \
    "$HOME"/.vscode-server/cli/servers/*/server/bin/remote-cli/code \
    "$HOME"/.vscode-server-insiders/cli/servers/*/server/bin/remote-cli/code \
    "$HOME"/.vscode-oss-server/cli/servers/*/server/bin/remote-cli/code \
    "$HOME"/.vscode-server/bin/*/bin/remote-cli/code \
    "$HOME"/.vscode-server-insiders/bin/*/bin/remote-cli/code \
    "$HOME"/.vscode-oss-server/bin/*/bin/remote-cli/code \
    "$HOME"/.vscodium-server/bin/*/bin/remote-cli/codium
  do
    if [[ -x "$candidate" && "$candidate" != *.staging/* ]]; then
      printf '%s\n' "$candidate"
      return 0
    fi
  done

  return 1
}

if [[ "${1:-}" == "--help" || "${1:-}" == "-h" ]]; then
  cat <<'EOF'
Usage: scripts/reinstall-vscode-extension.sh

Builds the debug talk binary, compiles/packages the VSCode extension, and
installs the VSIX into VSCode.

Environment variables:
  CODE_BIN    VSCode command to use. Defaults to auto-detecting code,
              code-insiders, codium, or VSCode Remote SSH's remote CLI.
  VSIX_PATH   Output VSIX path, default: .tmp/talktalk.vsix

Examples:
  scripts/reinstall-vscode-extension.sh
  CODE_BIN=code-insiders scripts/reinstall-vscode-extension.sh
  CODE_BIN="$HOME/.vscode-server/cli/servers/Stable-<commit>/server/bin/remote-cli/code" scripts/reinstall-vscode-extension.sh
EOF
  exit 0
fi

mkdir -p "$(dirname "$vsix_path")"

echo "==> Building talk debug binary"
cargo build --manifest-path "$repo_root/Cargo.toml"

echo "==> Installing VSCode extension npm dependencies"
npm --prefix "$extension_dir" install

echo "==> Compiling VSCode extension"
npm --prefix "$extension_dir" run compile

echo "==> Packaging VSCode extension to $vsix_path"
(
  cd "$extension_dir"
  if command -v vsce >/dev/null 2>&1; then
    vsce package --out "$vsix_path"
  else
    npx --yes @vscode/vsce package --out "$vsix_path"
  fi
)

if ! code_bin="$(resolve_code_bin)"; then
  cat >&2 <<EOF
==> Packaged VSCode extension to $vsix_path

Could not find the VSCode CLI. In a Remote SSH terminal, VSCode usually has one at:
  ~/.vscode-server/cli/servers/Stable-<commit>/server/bin/remote-cli/code

Re-run with CODE_BIN set to that path, for example:
  CODE_BIN=\$HOME/.vscode-server/cli/servers/Stable-<commit>/server/bin/remote-cli/code $0

Or install the VSIX manually from VSCode with "Extensions: Install from VSIX...".
EOF
  exit 1
fi

echo "==> Installing VSCode extension with $code_bin"
"$code_bin" --install-extension "$vsix_path" --force

cat <<'EOF'

Done.
Next steps:
  1. In VSCode, run "Developer: Reload Window".
  2. Run "TalkTalk: Restart Language Server".

If TALK_CORE_PATH matters, launch VSCode from an environment where it is set.
EOF
