#!/usr/bin/env bash
# Fetch the Lean dependencies for CI without pulling all of Mathlib.
#
# A plain `lake build` full-clones every package in lean/lake-manifest.json (Mathlib's history
# alone is ~500 MB) and, with `lake exe cache get`, downloads and unpacks every Mathlib olean
# (~6.4 GB). This script instead:
#   1. shallow-clones each package at its manifest revision (~170 MB total); Lake accepts the
#      checkout because HEAD and origin match the manifest, so it does not re-clone;
#   2. runs `lake exe cache get` on only the Mathlib modules lean/ imports; the cache tool
#      downloads their transitive closure (~80 MB compressed, ~850 MB unpacked).
# `lake build` then compiles nothing from Mathlib. Runnable from any directory.
set -euo pipefail

repo="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo/lean"

python3 -c '
import json
for p in json.load(open("lake-manifest.json"))["packages"]:
    print(p["name"], p["url"], p["rev"])
' | while read -r name url rev; do
  dir=".lake/packages/$name"
  if [ "$(git -C "$dir" rev-parse HEAD 2>/dev/null || true)" = "$rev" ]; then
    continue
  fi
  rm -rf "$dir"
  git init -q "$dir"
  git -C "$dir" remote add origin "$url"
  git -C "$dir" fetch -q --depth 1 origin "$rev"
  git -C "$dir" checkout -q FETCH_HEAD
done

# Only the Mathlib modules imported directly; the cache tool adds their closure.
mapfile -t mods < <(grep -rhoE '^import Mathlib(\.[A-Za-z0-9_]+)+' Libpetri ProofGraph* \
  | awk '{print $2}' | sort -u)
if [ "${#mods[@]}" -gt 0 ]; then
  lake exe cache get "${mods[@]}"
fi
