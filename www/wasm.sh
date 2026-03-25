#!/bin/bash
set -euo pipefail

rm -rf assets/pkg/
pushd ../wasm
npm run build
mv pkg/ ../www/assets/pkg
popd