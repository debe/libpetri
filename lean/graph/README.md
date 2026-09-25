# Proof-dependency graph

`proof-graph.json` is the dependency graph of every declaration under
`Libpetri.*`, extracted by Lean itself from the elaborated environment. Nothing
in it is written by hand: regenerate it, never edit it.

## Regenerate

From `lean/`:

    lake build
    lake exe proofgraph

`lake exe proofgraph [--root <module>] [--prefix <namespace>] [--lock <file>]
[--coverage <proof-coverage.json>] [--out <file> | OUT] [--check <expected>]`
writes `OUT` (default `graph/proof-graph.json`). `--root` (the module imported)
and `--prefix` (the namespace whose declarations become nodes) default to
`Libpetri`; `--lock` defaults to `graph/locked-theorems.txt`, `--coverage` to
`proof-coverage.json`. The committed JSON comes from the defaults. The output
depends only on the commit, and two runs are byte-identical.

## Testing the extractor

`ProofGraphFixture.lean` (namespace `PGFixture`, a default target, core only,
never imported by `Libpetri`) is a module with a known dependency shape: a
diamond (`a` uses `b` and `c`, both use `d`), an inductive with constructors,
a definition by `match` (`isRed.match_1`), structural recursion (`count._f`),
a proof through an equation lemma (`count.eq_1`), a proof by `split` through
the nested, private `isRed.match_1.splitter`, a `private` definition, core
constants that must stay `external`, a proof using `Classical.em` (axioms
include `Classical.choice`), mutual recursion both well-founded
(`isEven`/`isOdd`, compiled through `isEven._mutual`) and structural
(`evenS`/`oddS`, through `evenS._f`/`oddS._f`), well-founded recursion with
`termination_by` (`halvings`), and a structure with a default field
(`Point`, `Point.mk`, projections, `Point.y._default`). The mutual
definitions have no edge to each other: their elaborated values go through
the shared `_mutual`/`_f` auxiliaries, which name neither definition (Lean
ties the knot with `WellFounded.fix`/`brecOn`); only the equation lemmas
mention both, so a theorem that uses them depends on both. `graph/test/fixture-locked.txt` locks two names
(one `_private` entry) and `graph/test/fixture-coverage.json` gives one spec.

From `lean/`, after `lake build`:

    lake exe proofgraph --root ProofGraphFixture --prefix PGFixture \
      --lock graph/test/fixture-locked.txt --coverage graph/test/fixture-coverage.json \
      --check graph/test/fixture.expected.json

(`scripts/test_proofgraph_extractor.sh` runs the same.) `--check` compares
the output with `graph/test/fixture.expected.json` instead of writing it, prints
PASS, or FAIL with the first differing line, and exits 0 or 1. The expected
file is the extractor's own output, checked edge by edge against the fixture
source; regenerate it with `--out graph/test/fixture.expected.json` only when
the fixture or the extractor deliberately changes, and re-check the edges.

## Schema `libpetri-proofgraph/1`

```json
{"schema": "libpetri-proofgraph/1",
 "nodes": [{"name": str, "kind": str, "module": str, "file": str, "line": int,
            "specs": [str], "locked": bool, "axioms": [str], "external": [str]}],
 "edges": [[from, to]]}
```

- One node per line, one edge per line. Nodes are sorted by `name`; edges are
  sorted by `(from, to)` and deduplicated; every list inside a node is sorted.
  Keys inside a node object are in alphabetical order. No timestamps, hashes
  or absolute paths.
- `name`: the full constant name. A `private` declaration appears under the
  name it was declared with (`privateToUserName?`).
- `kind`: `theorem | def | inductive | structure | ctor | opaque | axiom |
  instance | other` (`instance` is a def registered as an instance,
  `structure` an inductive that is a structure).
- `module`: the declaring module (`Libpetri.Ring.Core`); `file`: that module's
  source path relative to `lean/` (`Libpetri/Ring/Core.lean`); `line`: the
  declaration's start line from `findDeclarationRanges?` (0 if Lean has none).
- `specs`: the spec IDs `proof-coverage.json` lists for this theorem. An entry
  is matched by its short `name` and `module` file to the node with that last
  name component in that file.
- `locked`: the name is a theorem in the gate's statement lock. The lock
  lock-check reads is the lab's `$LAB_GATE_DATA/baseline.lock.json` (gate data
  outside this repo; `verify.sh` passes it to the oracle). Its 297 theorem
  names, sorted, are committed unchanged as `graph/locked-theorems.txt` (copied
  from the lab board's `exports/locked-theorems.txt`), which the extractor reads
  by default, so regenerating needs no private data. `_private.<module>.0.<name>`
  entries match the node `<name>`. `--lock <baseline.lock.json>` reads the gate
  file itself instead (the keys of every top-level map whose entries carry a
  `typeHash`). The lock source is the single function `ProofGraph.readLock`.
  This is not `lean/fidelity.lock`, which pins Rust source spans, not Lean
  names.
- `axioms`: `collectAxioms` of the constant, as `#print axioms` reports it.
- `external`: constants outside `Libpetri.*` that the node uses directly or
  through contracted auxiliaries. They are leaves and are not expanded.
- An edge `[A, B]` means B's constant occurs in A's type or value
  (`Expr.getUsedConstants`), after contraction. Self-edges are dropped.

## Nodes and contraction

A constant becomes a node when its name (after stripping a `private` prefix)
is under `Libpetri` and it is not auxiliary. It is auxiliary when any of:

- `Name.isInternal` (a name component starts with `_`: `_proof_`, `_unfold`,
  `_sunfold`, `_cstage`, `_spec`, `_f`, `_unary`, `_sparseCasesOn`, …);
- `isAuxRecursor` (`casesOn`, `recOn`, `brecOn`, `binductionOn`, `below`, …)
  or `isNoConfusion`;
- `Meta.isMatcherCore` (a `match_<n>` matcher);
- it is a recursor (`.rec`);
- its last component is one of `rec recOn casesOn brecOn binductionOn below
  ibelow noConfusion noConfusionType ctorIdx toCtorIdx ctorElim ctorElimType
  injEq inj sizeOf_spec eq_def splitter`;
- any component — not only the last — is `eq_<n>`, `match_<n>` or
  `proof_<n>`. Checking only the last component lets constants such as
  `f.match_1.splitter` through as nodes.

When A uses an auxiliary B, B is replaced by what B itself uses, recursively
and memoised: the Libpetri nodes become A's edges and the constants outside
`Libpetri` join A's `external` list. Auxiliaries never appear as nodes or
edge ends. Auxiliaries can reference each other in a cycle (e.g.
`isEven._unsafe_rec` ↔ `isOdd._unsafe_rec`); the expansion keeps the
auxiliaries on the current path with their depths, cuts a re-entered one, and
memoises a result only when it did not cut into an auxiliary still open above
it (a Tarjan-style low-link), so no partial result is ever stored.

## Regenerate everything (extract, then render)

From anywhere in the repository:

    bash scripts/regen-proof-graph.sh

It runs, in order:

1. `lake build` in `lean/` (both default targets: the extractor reads the
   `Libpetri` oleans at run time, so building `proofgraph` alone can read stale
   ones);
2. the extractor's fixture check, exactly as in "Testing the extractor" above,
   with the fixture's own lock and coverage files
   (`--lock graph/test/fixture-locked.txt --coverage graph/test/fixture-coverage.json
   --check graph/test/fixture.expected.json`; without them the fixture's locked
   theorems extract as unlocked and the check fails). A failed check stops the
   script;
3. `lake exe proofgraph`, writing `graph/proof-graph.json`;
4. `python3 scripts/proof-graph.py --in lean/graph/proof-graph.json --out lean/graph --coverage lean/proof-coverage.json`,
   which writes

- `graph/requirements/<SPEC-ID>.md`: for each spec ID, the theorems carrying it
  and their proof tree as Mermaid (everything they transitively use inside
  `Libpetri`, transitively reduced, grouped by file, 🔒 on locked theorems, the
  axioms each root uses). Size rule, limit 60 nodes: a requirement whose whole
  tree is over the limit is drawn as one diagram per theorem carrying it; a
  theorem whose own tree is still over the limit has every file other than its
  own collapsed into one node per file; only if that is still over the limit is
  it split into one diagram per direct dependency. A diagram with fewer than 3
  nodes is never drawn on its own: those dependencies are listed as shared
  leaves. The page states the size note, and every diagram of an oversize page
  carries the rule that produced it.
- `graph/modules.md`: the file-level overview, transitively reduced, with the
  declaration count per file.
- `graph/index.html`: one self-contained interactive page over the whole graph
  (plain JavaScript and SVG from `scripts/proof-graph-html/`, no library, the
  graph data inlined). It opens from disk with no network access. The start
  view is the file overview (click a file for its declarations); search by
  name, pick a spec ID to list its theorems and restrict search to their proof
  tree, click any node for its neighbourhood (dependents left, dependencies
  right, highlighted) and a panel with kind, file:line, 🔒 lock, spec IDs,
  axioms, dependency and dependent lists and external constants. Files are
  coloured consistently, with a legend.

The renderer deletes requirement pages it did not produce, so a removed spec
leaves no stale page. It fails (exit 3) if `proof-coverage.json` lists a
theorem that is not a node carrying its spec ID (renamed, moved or missing), or
if the page count differs from the number of spec IDs there. Every output is
generated: never edit it by hand. The script needs no arguments and no gate
data; on an unchanged commit it leaves `git status lean/graph` clean.
