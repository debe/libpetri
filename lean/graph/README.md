# Proof-dependency graph

This directory maps which Lean declarations every libpetri proof depends on, from the spec
requirement down to the lemmas. Lean extracts it from the elaborated environment, so every file
here is generated: regenerate it, never edit it.

The interactive view is [`index.html`](index.html). It is checked in and CI fails if it is stale.
Open it from a checkout in any browser; it is self-contained and works offline.

## What is here

| File | Contents |
|---|---|
| [`index.html`](index.html) | Interactive view of the whole graph |
| [`requirements/<SPEC-ID>.md`](requirements/) | One page per spec requirement: the theorems that prove it and their proof trees as Mermaid |
| [`modules.md`](modules.md) | File-level overview with declaration counts |
| `proof-graph.json` | The raw graph (schema below) |
| `locked-theorems.txt` | Theorems whose statements are frozen; marked 🔒 |
| `test/` | Extractor fixture: expected output, lock and coverage |

## Using the interactive page

- The start view shows the files. Click a file to list its declarations.
- Search by declaration name.
- Pick a spec ID to list its theorems and limit the search to their proof trees.
- Click a node to see its neighbourhood: dependents on the left, dependencies on the right. The
  side panel shows kind, `file:line`, lock, spec IDs, axioms, and direct and external dependencies.

## Regenerate

From anywhere in the repository:

```bash
bash scripts/regen-proof-graph.sh
```

The script builds `lean/` and checks the extractor against its fixture. It then extracts
`proof-graph.json` with `lake exe proofgraph` and renders the pages with
`scripts/proof-graph.py`. It deletes requirement pages that no longer apply. It fails if
`lean/proof-coverage.json` names a theorem that is not in the graph. Output is deterministic:
on an unchanged commit, `git status lean/graph` stays clean. CI enforces this in the `lean` job.

Commit the regenerated files with any change to `Libpetri/` or `proof-coverage.json`.

## How the graph is built

A node is a declaration under `Libpetri.*`. An edge `A → B` means B's constant occurs in A's
type or value. Compiler auxiliaries (matchers, recursors, equation lemmas, `_proof_n`,
`_unsafe_rec`, …) are not nodes. They are contracted: A inherits what the auxiliary uses.
Constants outside `Libpetri` are listed on the node as `external` and never expanded.

The requirement pages keep each Mermaid diagram at 60 nodes or fewer. An oversize requirement is
drawn one theorem at a time. An oversize theorem collapses other files to one node each. As a
last resort, the diagram splits by direct dependency. Dependencies too small to draw on their own
are listed as shared leaves.

## Extractor reference

```text
lake exe proofgraph [--root <module>] [--prefix <namespace>] [--lock <file>]
                    [--coverage <proof-coverage.json>] [--out <file> | OUT] [--check <expected>]
```

Run it from `lean/` after `lake build`. The defaults are root and prefix `Libpetri`, lock
`graph/locked-theorems.txt`, coverage `proof-coverage.json`, and output
`graph/proof-graph.json`. `--check` compares the output with a file instead of writing it. It
prints PASS or FAIL and exits 0 or 1.

`ProofGraphFixture.lean` is the extractor's test module. It is small, uses only Lean core, and
`Libpetri` never imports it. It covers the tricky shapes: a diamond, matchers and splitters,
structural, mutual and well-founded recursion, private declarations, structures with default
fields, and a classical axiom. `scripts/test_proofgraph_extractor.sh` checks it against
`test/fixture.expected.json`. Regenerate that file (`--out`) only when the fixture or the
extractor deliberately changes, and re-check its edges by hand.

### Schema `libpetri-proofgraph/1`

```json
{"schema": "libpetri-proofgraph/1",
 "nodes": [{"name": str, "kind": str, "module": str, "file": str, "line": int,
            "specs": [str], "locked": bool, "axioms": [str], "external": [str]}],
 "edges": [[from, to]]}
```

- One node or edge per line. Nodes are sorted by name. Edges are sorted and deduplicated. Every
  list is sorted. No timestamps, hashes or absolute paths.
- `kind`: `theorem | def | inductive | structure | ctor | opaque | axiom | instance | other`.
- `file` is relative to `lean/`. `line` is the declaration's start line (0 if unknown).
- `specs`: the spec IDs that `proof-coverage.json` assigns to the theorem.
- `locked`: the theorem is listed in `locked-theorems.txt`. Private names match without their
  `_private.<module>.0.` prefix.
- `axioms`: as `#print axioms` reports them.
- `external`: constants outside `Libpetri` used directly or through contracted auxiliaries.
