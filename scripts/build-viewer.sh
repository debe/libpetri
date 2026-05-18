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
#
# Consumer-side loader migration is a separate task — this script is the
# input each consumer migration will lean on.

set -euo pipefail

cd "$(dirname "$0")/.."
REPO_ROOT="$(pwd)"

echo "==> Building canonical viewer (typescript/)..."
(cd "$REPO_ROOT/typescript" && npm run build:viewer)

VIEWER_JS="$REPO_ROOT/typescript/dist/viewer/viewer.iife.js"
VIEWER_STATIC_JS="$REPO_ROOT/typescript/dist/viewer/viewer-static.iife.js"
VIEWER_CSS="$REPO_ROOT/typescript/dist/viewer/viewer.css"

if [[ ! -f "$VIEWER_JS" ]]; then
  echo "ERROR: $VIEWER_JS missing after build" >&2
  exit 1
fi
if [[ ! -f "$VIEWER_STATIC_JS" ]]; then
  echo "ERROR: $VIEWER_STATIC_JS missing after build" >&2
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

# Slim bundle: only the Java javadoc taglet currently pre-renders SVG via
# `dot -Tsvg` and inlines this stripped-down viewer (WASM blob stubbed out).
# Rust/TS doc generators have no pre-render path yet, so they don't consume
# it — adding the file to their resources would just bloat the published
# crate / npm package. Wire them up here when a consumer lands.
cp "$VIEWER_STATIC_JS" "${DESTS[0]}/petrinet-diagrams-static.js"
echo "==> Wrote ${DESTS[0]}/petrinet-diagrams-static.js (Java-only)"

echo "==> Verifying byte-identical mirrors..."
diff "${DESTS[0]}/petrinet-diagrams.js"  "${DESTS[1]}/petrinet-diagrams.js"  >/dev/null
diff "${DESTS[0]}/petrinet-diagrams.js"  "${DESTS[2]}/petrinet-diagrams.js"  >/dev/null
diff "${DESTS[0]}/petrinet-diagrams.css" "${DESTS[1]}/petrinet-diagrams.css" >/dev/null
diff "${DESTS[0]}/petrinet-diagrams.css" "${DESTS[2]}/petrinet-diagrams.css" >/dev/null
echo "==> All three consumer dirs hold byte-identical petrinet-diagrams.{js,css}."
