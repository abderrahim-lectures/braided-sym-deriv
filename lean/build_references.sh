#!/usr/bin/env bash
# Elaborate the per-reference modules of Research/BraidedSymDeriv/References.
#
# lean/lean-toolchain pins v4.36.0-rc2, which is not installed in this VM: the
# `lean` on PATH is 4.33.1 and the Mathlib on LEAN_PATH is built for it. This
# script therefore does not use lake. Every .olean goes to .scratch/olean/, so
# the working tree stays clean and no build artifact lands next to a source
# file.
#
# Usage: lean/build_references.sh [module ...]
#   with no argument it builds the whole catalogue in dependency order.
set -euo pipefail
cd "$(dirname "$0")"
repo_root="$(cd .. && pwd)"
out="$repo_root/.scratch/olean"
export LEAN_PATH="$out:$PWD${LEAN_PATH:+:$LEAN_PATH}"

build() {
  local mod="$1"
  local src="${mod//.//}.lean"
  local dst="$out/${mod//.//}.olean"
  if [ ! -f "$src" ]; then
    echo "== skip $mod (missing $src)"
    return 0
  fi
  mkdir -p "$(dirname "$dst")"
  echo "== $mod"
  lean -o "$dst" "$src"
}

if [ "$#" -gt 0 ]; then
  for m in "$@"; do build "$m"; done
  echo "OK: requested modules elaborate"
  exit 0
fi

# Dependencies of the bridge module, then the shared prelude, then the
# per-reference modules (each imports only the prelude, so their order is free),
# then the aggregator.
build Research.BraidedSymDeriv.TwistedCommutative
build Research.BraidedSymDeriv.Paper
build Research.BraidedSymDeriv.References.Basic
for m in Reduced Hochschild HochschildComplex HochschildGeneral JordanHerstein \
         JordanProduct FDerivation \
         Nonassoc AlphaDerivation Involution BraidedDerivation; do
  build "Research.BraidedSymDeriv.References.$m"
done
build Research.BraidedSymDeriv.References.PaperBridge
build Research.BraidedSymDeriv.References.All
echo "OK: every reference module elaborates"
