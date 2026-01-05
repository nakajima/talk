#!/bin/bash

cleanup() {
    echo "stopping..."
    tailscale funnel reset
    kill $(jobs -p) 2>/dev/null
}

trap cleanup EXIT

echo "starting server"
python -m http.server 8000 -d ./assets &
sleep 1

echo "serving"
tailscale funnel 8000 &
sleep 1

echo "watching"
watchexec --exts css,template,md,rs,js "(cargo run > ./assets/index.html)"
