#!/usr/bin/env bash
# Build the canonical libpetri diagram viewer and distribute the IIFE
# bundle + CSS to every embedder (Java javadoc taglet, Rust docgen, the
# TypeScript doclet).
#
# Source of truth: typescript/src/viewer/
# Outputs:
#   typescript/dist/viewer/viewer.iife.js
#   typescript/dist/viewer/viewer.css
# Distributed to (filename kept as `petrinet-diagrams.{js,css}` so the
# consumer-side classpath / include_str! paths don't have to move):
#   java/src/main/resources/javadoc/petrinet-diagrams.{js,css}
#   rust/libpetri-docgen/resources/petrinet-diagrams.{js,css}
#   typescript/src/doclet/resources/petrinet-diagrams.{js,css}
# Digests of both files are recorded in spec/viewer-bundle.sha256, which the
# per-port drift tests check against.

set -euo pipefail

cd "$(dirname "$0")/.."
REPO_ROOT="$(pwd)"

echo "==> Building canonical viewer (typescript/)..."
(cd "$REPO_ROOT/typescript" && npm run build:viewer)

VIEWER_JS="$REPO_ROOT/typescript/dist/viewer/viewer.iife.js"
VIEWER_CSS="$REPO_ROOT/typescript/dist/viewer/viewer.css"

if [[ ! -f "$VIEWER_JS" ]]; then
  echo "ERROR: $VIEWER_JS missing after build" >&2
  exit 1
fi
if [[ ! -f "$VIEWER_CSS" ]]; then
  echo "ERROR: $VIEWER_CSS missing after build" >&2
  exit 1
fi

DESTS=(
  "$REPO_ROOT/java/src/main/resources/javadoc"
  "$REPO_ROOT/rust/libpetri-docgen/resources"
  "$REPO_ROOT/typescript/src/doclet/resources"
)

for dest in "${DESTS[@]}"; do
  mkdir -p "$dest"
  cp "$VIEWER_JS" "$dest/petrinet-diagrams.js"
  cp "$VIEWER_CSS" "$dest/petrinet-diagrams.css"
  echo "==> Wrote $dest/petrinet-diagrams.{js,css}"
done

echo "==> Verifying byte-identical mirrors..."
diff "${DESTS[0]}/petrinet-diagrams.js"  "${DESTS[1]}/petrinet-diagrams.js"  >/dev/null
diff "${DESTS[0]}/petrinet-diagrams.js"  "${DESTS[2]}/petrinet-diagrams.js"  >/dev/null
diff "${DESTS[0]}/petrinet-diagrams.css" "${DESTS[1]}/petrinet-diagrams.css" >/dev/null
diff "${DESTS[0]}/petrinet-diagrams.css" "${DESTS[2]}/petrinet-diagrams.css" >/dev/null
echo "==> All three consumer dirs hold byte-identical petrinet-diagrams.{js,css}."

# Record the canonical digests. Each port has a test that hashes its own copy
# of petrinet-diagrams.{js,css} and compares against this file, so a mirror
# left behind on an older bundle fails that port's build instead of silently
# rendering a stale viewer (which is how a doc page can end up with diagonal
# spline edges long after the orthogonal routing landed).
CHECKSUMS="$REPO_ROOT/spec/viewer-bundle.sha256"
{
  printf '%s  petrinet-diagrams.js\n'  "$(sha256sum "$VIEWER_JS"  | cut -d' ' -f1)"
  printf '%s  petrinet-diagrams.css\n' "$(sha256sum "$VIEWER_CSS" | cut -d' ' -f1)"
} > "$CHECKSUMS"
echo "==> Wrote $CHECKSUMS"
