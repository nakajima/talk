#!/bin/bash

cleanup() {
    echo "stopping..."
    tailscale funnel reset
    kill $(jobs -p) 2>/dev/null
}

trap cleanup EXIT

echo "starting dev server"
cargo run -- dev &
server_pid=$!
sleep 1

echo "serving with tailscale funnel"
tailscale funnel 8000 &

wait "$server_pid"
