#!/usr/bin/env bash
# Elaborate the per-reference modules of References/ (top level of lean/).
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

# The Lean to use: $LEAN if set, otherwise the one on PATH. In this VM the
# elan shim in $HOME/.elan/bin comes first on PATH and may have no default
# toolchain configured, so $LEAN=/opt/lean/bin/lean is the reliable choice.
LEAN="${LEAN:-lean}"
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
  "$LEAN" -o "$dst" "$src"
}

if [ "$#" -gt 0 ]; then
  for m in "$@"; do build "$m"; done
  echo "OK: requested modules elaborate"
  exit 0
fi

# Dependencies of the bridge module, then the shared prelude, then the
# per-reference modules (each imports only the prelude, so their order is free),
# then the aggregator.
# PaperBridge imports TwistedCommutative (the paper's §3 computations). Paper.lean
# and BraidedSymmetric.lean are deliberately not dependencies: the paper session is
# restructuring them, and this catalogue must build from a clean clone.
build Research.BraidedSymDeriv.TwistedCommutative
build References.Basic
for m in Reduced Hochschild HochschildComplex HochschildGeneral JordanHerstein \
         JordanProduct FDerivation \
         Nonassoc AlphaDerivation Involution BraidedDerivation; do
  build "References.$m"
done
build References.PaperBridge
build References.All
echo "OK: every reference module elaborates"
