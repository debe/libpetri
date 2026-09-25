#!/usr/bin/env bash
# Fixture test for the proofgraph extractor (lean/graph/README.md, "Testing the
# extractor"): extract lean/ProofGraphFixture.lean and compare the output with
# lean/graph/test/fixture.expected.json. Exit 0 when identical, 1 otherwise.
#
#   scripts/test_proofgraph_extractor.sh [EXPECTED]
#
# EXPECTED defaults to lean/graph/test/fixture.expected.json. Needs `lake build`
# first (the fixture library and the exe are default targets). The comparison
# is the extractor's own `--check` mode, so this is the same as running, from
# lean/:
#
#   lake exe proofgraph --root ProofGraphFixture --prefix PGFixture \
#     --lock graph/test/fixture-locked.txt --coverage graph/test/fixture-coverage.json \
#     --check graph/test/fixture.expected.json
set -euo pipefail
repo=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
expected=$(realpath "${1:-$repo/lean/graph/test/fixture.expected.json}")
cd "$repo/lean"
exec lake exe proofgraph --root ProofGraphFixture --prefix PGFixture \
  --lock graph/test/fixture-locked.txt --coverage graph/test/fixture-coverage.json \
  --check "$expected"
