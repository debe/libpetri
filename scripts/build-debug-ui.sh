#!/usr/bin/env bash
set -euo pipefail

# Build the debug UI and copy output to Java resources and TypeScript dist.
#
# Usage: ./scripts/build-debug-ui.sh
#
# Prerequisites: Node.js installed, npm dependencies installed in debug-ui/

REPO_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
DEBUG_UI_DIR="$REPO_ROOT/debug-ui"
JAVA_RESOURCES="$REPO_ROOT/java/src/main/resources/debug-ui"
TS_DIST="$REPO_ROOT/typescript/dist/debug-ui"

echo "Building debug UI..."
cd "$DEBUG_UI_DIR"
npm ci --silent
npm run build

echo "Copying to Java resources: $JAVA_RESOURCES"
rm -rf "$JAVA_RESOURCES"
mkdir -p "$JAVA_RESOURCES"
cp -r dist/* "$JAVA_RESOURCES/"

echo "Copying to TypeScript dist: $TS_DIST"
rm -rf "$TS_DIST"
mkdir -p "$TS_DIST"
cp -r dist/* "$TS_DIST/"

echo "Debug UI build complete."
