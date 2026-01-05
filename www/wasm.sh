#!/bin/bash

rm -rf assets/pkg/
pushd ../wasm
npm run build
mv pkg/ ../www/assets/pkg
popd