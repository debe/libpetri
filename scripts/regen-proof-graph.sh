#!/usr/bin/env bash
# Regenerate every committed proof-graph file from the current commit:
#   lean/graph/proof-graph.json      (lake exe proofgraph, Lean's own extraction)
#   lean/graph/requirements/*.md     (scripts/proof-graph.py)
#   lean/graph/modules.md            (scripts/proof-graph.py)
#   docs/proof-graph/index.html      (scripts/proof-graph.py, template in scripts/proof-graph-html/;
#                                     GitHub Pages serves it at https://libpetri.org/proof-graph/)
# No arguments, no gate data. Runnable from any directory. Never edit the outputs by hand.
set -euo pipefail

repo="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo/lean"

# Plain `lake build`: the default targets are `Libpetri` and `proofgraph`. The extractor loads
# the Libpetri oleans at run time, so `lake build proofgraph` alone can read stale ones.
lake build
# Guard the extractor first: its fixture module must still extract to the expected graph
# (set -e makes a failed check abort the script with its non-zero status). The fixture's own
# lock and coverage files are required: with the defaults the fixture's locked theorems
# extract as unlocked and the check fails (lean/graph/README.md, "Testing the extractor").
lake exe proofgraph --root ProofGraphFixture --prefix PGFixture \
  --lock graph/test/fixture-locked.txt --coverage graph/test/fixture-coverage.json \
  --check graph/test/fixture.expected.json
lake exe proofgraph

cd "$repo"
# Mermaid pages, modules.md and the interactive index.html; fails if proof-coverage.json lists
# a theorem that is not a graph node.
python3 scripts/proof-graph.py \
  --in lean/graph/proof-graph.json \
  --out lean/graph \
  --html docs/proof-graph/index.html \
  --coverage lean/proof-coverage.json
