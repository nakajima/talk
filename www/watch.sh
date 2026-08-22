#!/bin/bash
set -euo pipefail

cleanup() {
    echo "stopping..."
    tailscale funnel reset >/dev/null 2>&1 || true
    for pid in $(jobs -p); do
        kill "$pid" 2>/dev/null || true
    done
}

trap cleanup EXIT

echo "building Talk compiler for documentation and examples"
pushd .. >/dev/null
cargo build --bin talk
popd >/dev/null

echo "starting dev server"
tailscale funnel reset >/dev/null 2>&1 || true
TALK_COMPILER=../target/debug/talk cargo run -- dev &
server_pid=$!

echo "waiting for the dev server to accept connections"
until curl --silent --fail --max-time 1 http://127.0.0.1:8000/ >/dev/null; do
    if ! kill -0 "$server_pid" 2>/dev/null; then
        wait "$server_pid"
        exit $?
    fi
    sleep 0.25
done

echo "serving with tailscale funnel"
tailscale funnel --yes 8000 &

wait "$server_pid"
