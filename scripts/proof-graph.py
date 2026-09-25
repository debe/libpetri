#!/usr/bin/env python3
"""Render the Lean proof-dependency graph (``proof-graph.json``, schema v1) as Mermaid.

Usage::

    python3 scripts/proof-graph.py --in lean/graph/proof-graph.json --out lean/graph

Writes

* ``<out>/requirements/<SPEC-ID>.md``: one per spec ID carried by a node. It names the
  theorems carrying the ID and draws, as a Mermaid flowchart, everything they transitively use
  inside the graph, transitively reduced and grouped by source file.
* ``<out>/modules.md``: the file-level overview (file -> file when any edge crosses them),
  transitively reduced, with the declaration count per file.
* ``<out>/index.html`` (or ``--html``): one self-contained interactive page over the whole graph (template and
  script in ``scripts/proof-graph-html/``, plain JS + SVG, no library, no network access).

The input is the only source: nothing is annotated by hand. Output is deterministic, with
sorted iteration and no timestamps, so the same JSON gives byte-identical files.

Size rule: a requirement whose tree has more than ``--threshold`` nodes is drawn per theorem.
A theorem whose own tree is still too large has every file other than its own collapsed into
one node per file, and if that is still too large it is split into one diagram per direct
dependency. A diagram with fewer than 3 nodes is never drawn on its own: such dependencies are
listed as shared leaves. Every diagram of an oversize requirement carries the rule applied.

Python 3 standard library only.
"""

from __future__ import annotations

import argparse
import json
import os
import sys

SCHEMA = "libpetri-proofgraph/1"
KINDS = {"theorem", "def", "inductive", "structure", "ctor", "opaque", "axiom", "instance", "other"}
DEFAULT_THRESHOLD = 60


class SchemaError(Exception):
    pass


class CoverageError(Exception):
    pass


# ---------------------------------------------------------------- loading


def load(path: str) -> dict:
    with open(path, encoding="utf-8") as f:
        data = json.load(f)
    validate(data)
    return data


def validate(data: dict) -> None:
    if not isinstance(data, dict):
        raise SchemaError("top level must be a JSON object")
    schema = data.get("schema")
    if schema != SCHEMA:
        raise SchemaError(f"unsupported schema {schema!r}: this renderer reads {SCHEMA!r} only")
    names = set()
    for n in data.get("nodes", []):
        for key, typ in (("name", str), ("kind", str), ("module", str), ("file", str),
                         ("line", int), ("specs", list), ("locked", bool), ("axioms", list),
                         ("external", list)):
            if not isinstance(n.get(key), typ):
                raise SchemaError(f"node {n.get('name')!r}: field {key!r} missing or not {typ.__name__}")
        if n["kind"] not in KINDS:
            raise SchemaError(f"node {n['name']!r}: unknown kind {n['kind']!r}")
        names.add(n["name"])
    for e in data.get("edges", []):
        if not (isinstance(e, list) and len(e) == 2 and all(isinstance(x, str) for x in e)):
            raise SchemaError(f"edge {e!r} is not a [from, to] pair of names")


# ---------------------------------------------------------------- graph algorithms


def adjacency(nodes: set, edges) -> dict:
    """Successor sets restricted to `nodes`, self loops dropped."""
    adj = {n: set() for n in nodes}
    for a, b in edges:
        if a in adj and b in adj and a != b:
            adj[a].add(b)
    return adj


def reachable(adj: dict, starts) -> set:
    seen = set()
    stack = sorted(starts, reverse=True)
    while stack:
        u = stack.pop()
        if u in seen:
            continue
        seen.add(u)
        stack.extend(sorted(adj.get(u, ()), reverse=True))
    return seen


def sccs(adj: dict) -> dict:
    """Map each node to a representative of its strongly connected component (Tarjan)."""
    index, low, on, stack, comp = {}, {}, set(), [], {}
    counter = [0]

    def visit(v):
        # iterative Tarjan to avoid recursion limits on long chains
        work = [(v, iter(sorted(adj[v])))]
        index[v] = low[v] = counter[0]
        counter[0] += 1
        stack.append(v)
        on.add(v)
        while work:
            node, it = work[-1]
            advanced = False
            for w in it:
                if w not in index:
                    index[w] = low[w] = counter[0]
                    counter[0] += 1
                    stack.append(w)
                    on.add(w)
                    work.append((w, iter(sorted(adj[w]))))
                    advanced = True
                    break
                if w in on:
                    low[node] = min(low[node], index[w])
            if advanced:
                continue
            work.pop()
            if work:
                low[work[-1][0]] = min(low[work[-1][0]], low[node])
            if low[node] == index[node]:
                members = []
                while True:
                    w = stack.pop()
                    on.discard(w)
                    members.append(w)
                    if w == node:
                        break
                rep = min(members)
                for w in members:
                    comp[w] = rep

    for v in sorted(adj):
        if v not in index:
            visit(v)
    return comp


def transitive_reduction(adj: dict) -> dict:
    """Drop u -> v when v is reachable from u through another path.

    Computed on the condensation, so cycles (mutual definitions) keep their internal edges and
    never lose their connection to the rest of the graph."""
    comp = sccs(adj)
    cadj = {}
    for u, vs in adj.items():
        cu = comp[u]
        cadj.setdefault(cu, set())
        for v in vs:
            if comp[v] != cu:
                cadj[cu].add(comp[v])
    reach = {}
    for c in sorted(cadj):
        reach[c] = reachable(cadj, cadj[c])  # everything reachable in >= 1 step
    keep_c = {}
    for c, succ in cadj.items():
        keep = set()
        for d in succ:
            if not any(d in reach[o] for o in succ if o != d):
                keep.add(d)
        keep_c[c] = keep
    out = {}
    for u, vs in adj.items():
        out[u] = set()
        for v in vs:
            if comp[u] == comp[v] or comp[v] in keep_c[comp[u]]:
                out[u].add(v)
    return out


# ---------------------------------------------------------------- mermaid helpers


def label(text: str) -> str:
    """A quoted Mermaid label: only entity codes inside the quotes."""
    out = []
    for ch in text:
        if ch == '"':
            out.append("#quot;")
        elif ch == "<":
            out.append("#lt;")
        elif ch == ">":
            out.append("#gt;")
        elif ch == "#":
            out.append("#35;")
        else:
            out.append(ch)
    return '"' + "".join(out) + '"'


class Ids:
    """Stable Mermaid ids: every declaration gets n<i> by its position in the sorted name list,
    every collapsed file c<i> by its position in the sorted file list."""

    def __init__(self, names, files=()):
        self.ids = {n: f"n{i}" for i, n in enumerate(sorted(names))}
        for i, f in enumerate(sorted(files)):
            self.ids[collapsed_name(f)] = f"c{i}"

    def __getitem__(self, name):
        return self.ids[name]


def mermaid(nodes: list, edges: list, groups: dict, ids, labels: dict, classes: dict) -> list:
    """`groups`: group label -> sorted member list (subgraphs); `classes`: name -> class."""
    lines = ["```mermaid", "flowchart TD"]
    grouped = set()
    for gi, g in enumerate(sorted(groups)):
        members = [m for m in sorted(groups[g]) if m in nodes]
        if not members:
            continue
        lines.append(f"  subgraph g{gi}[{label(g)}]")
        for m in members:
            lines.append(f"    {ids[m]}[{label(labels[m])}]")
            grouped.add(m)
        lines.append("  end")
    for m in sorted(nodes):
        if m not in grouped:
            lines.append(f"  {ids[m]}[{label(labels[m])}]")
    for a, b in sorted(edges):
        lines.append(f"  {ids[a]} --> {ids[b]}")
    lines.append("  classDef root stroke-width:3px")
    lines.append("  classDef locked fill:#fff3cd,stroke:#b8860b")
    lines.append("  classDef collapsed fill:#eeeeee,stroke-dasharray:4 4")
    for cls in ("root", "locked", "collapsed"):
        members = sorted(n for n in nodes if cls in classes.get(n, ()))
        if members:
            lines.append(f"  class {','.join(ids[m] for m in members)} {cls}")
    lines.append("```")
    return lines


# ---------------------------------------------------------------- requirement pages


def node_label(n: dict) -> str:
    return ("🔒 " if n["locked"] else "") + n["name"]


def collapsed_name(file: str) -> str:
    return "\u0000file:" + file  # cannot clash with a Lean name


def build_view(by_name, adj, names: set, roots: list, collapse: bool):
    """Nodes, reduced edges, groups, labels and classes of one diagram over `names`."""
    root_files = {by_name[r]["file"] for r in roots}
    rep = {}
    counts = {}
    for n in names:
        f = by_name[n]["file"]
        if collapse and f not in root_files:
            rep[n] = collapsed_name(f)
            counts[f] = counts.get(f, 0) + 1
        else:
            rep[n] = n
    vnodes = set(rep.values())
    vedges = set()
    for u in names:
        for v in adj[u]:
            if v in names and rep[u] != rep[v]:
                vedges.add((rep[u], rep[v]))
    vadj = adjacency(vnodes, vedges)
    red = transitive_reduction(vadj)
    edges = [(u, v) for u in red for v in red[u]]
    labels, classes, groups = {}, {}, {}
    for v in vnodes:
        if v.startswith("\u0000file:"):
            f = v[len("\u0000file:"):]
            labels[v] = f"📁 {f} ({counts[f]} declarations, collapsed)"
            classes[v] = {"collapsed"}
        else:
            n = by_name[v]
            labels[v] = node_label(n)
            cls = set()
            if v in roots:
                cls.add("root")
            if n["locked"]:
                cls.add("locked")
            classes[v] = cls
            groups.setdefault(n["file"], []).append(v)
    return vnodes, edges, groups, labels, classes


def requirement_page(spec: str, by_name, adj, roots: list, threshold: int) -> str:
    ids = Ids(by_name, {n["file"] for n in by_name.values()})
    out = [f"# {spec}", "", "Generated by `scripts/proof-graph.py` from `proof-graph.json`. Do not edit.", ""]
    out.append("Theorems carrying this ID:")
    out.append("")
    for r in roots:
        n = by_name[r]
        lock = " 🔒 locked" if n["locked"] else ""
        out.append(f"- `{r}` ({n['kind']}, `{n['file']}:{n['line']}`){lock}")
    out.append("")
    closure = reachable(adj, roots)
    full = build_view(by_name, adj, closure, roots, collapse=False)
    if len(full[0]) <= threshold:
        vnodes, edges, groups, labels, classes = full
        out.extend(mermaid(vnodes, edges, groups, ids, labels, classes))
        out.append("")
    else:
        if len(roots) > 1:
            out.append(f"> **Note:** the full tree has {len(closure)} nodes (limit {threshold}), "
                       f"so it is drawn as one diagram per theorem ({len(roots)} theorems).")
        else:
            out.append(f"> **Note:** the full tree has {len(closure)} nodes (limit {threshold}).")
        out.append("")
        for r in roots:
            out.extend(root_section(r, by_name, adj, ids, threshold, len(roots) > 1))
    out.append("Axioms used:")
    out.append("")
    for r in roots:
        ax = by_name[r]["axioms"]
        out.append(f"- `{r}`: " + (", ".join(f"`{a}`" for a in ax) if ax else "none"))
    out.append("")
    return "\n".join(out)


MIN_SPLIT_NODES = 3


def root_section(r: str, by_name, adj, ids, threshold: int, heading: bool) -> list:
    """Diagrams for one theorem of an oversize requirement, each with the rule that produced it:
    its whole tree if that fits, else its tree with other files collapsed, else one diagram per
    direct dependency. A diagram under `MIN_SPLIT_NODES` nodes is never drawn on its own: those
    dependencies are listed as shared leaves instead."""
    out = []
    if heading:
        out.extend([f"### `{r}`", ""])
    tree = reachable(adj, [r])
    full = build_view(by_name, adj, tree, [r], collapse=False)
    diagrams = []   # (title, rule, view)
    leaves = []
    if len(full[0]) < MIN_SPLIT_NODES:
        leaves = sorted(d for d in adj[r])
        if not leaves:
            out.extend(["This theorem uses nothing else inside `Libpetri`.", ""])
    elif len(full[0]) <= threshold:
        diagrams.append((None, f"this theorem's whole tree, {len(full[0])} nodes.", full))
    else:
        coll = build_view(by_name, adj, tree, [r], collapse=True)
        if len(coll[0]) <= threshold:
            diagrams.append((None, f"this theorem's tree has {len(tree)} nodes (limit {threshold}); "
                                   "every file other than its own is collapsed into one node, "
                                   f"leaving {len(coll[0])}.", coll))
        else:
            for d in sorted(adj[r]):
                part = reachable(adj, [d]) | {r}
                sub_adj = {u: (adj[u] if u != r else {d}) for u in part}
                v = build_view(by_name, sub_adj, part, [r], collapse=True)
                if len(v[0]) < MIN_SPLIT_NODES:
                    leaves.append(d)
                else:
                    diagrams.append((f"`{r}` → `{d}`",
                                     f"this theorem's tree has {len(tree)} nodes, still "
                                     f"{len(coll[0])} with other files collapsed, so it is split "
                                     f"by direct dependency; this part has {len(v[0])} nodes, "
                                     "other files collapsed.", v))
    for title, rule, (vnodes, edges, groups, labels, classes) in diagrams:
        if title:
            out.extend([f"#### {title}", ""])
        out.extend([f"> Rule: {rule}", ""])
        out.extend(mermaid(vnodes, edges, groups, ids, labels, classes))
        out.append("")
    if leaves:
        out.append(f"Shared leaves of `{r}` (direct dependencies too small for a diagram of "
                   f"their own, fewer than {MIN_SPLIT_NODES} nodes):")
        out.append("")
        for d in leaves:
            out.append(f"- `{d}` (`{by_name[d]['file']}`)")
        out.append("")
    return out


# ---------------------------------------------------------------- modules page


def modules_page(by_name, edges) -> str:
    files = sorted({n["file"] for n in by_name.values()})
    count = {f: 0 for f in files}
    for n in by_name.values():
        count[n["file"]] += 1
    fedges = set()
    for a, b in edges:
        if a in by_name and b in by_name:
            fa, fb = by_name[a]["file"], by_name[b]["file"]
            if fa != fb:
                fedges.add((fa, fb))
    red = transitive_reduction(adjacency(set(files), fedges))
    ids = {f: f"f{i}" for i, f in enumerate(files)}
    out = ["# Module overview", "",
           "Generated by `scripts/proof-graph.py` from `proof-graph.json`. Do not edit.", "",
           "An arrow `A --> B` means a declaration in file A uses one in file B "
           "(transitively reduced).", "", "```mermaid", "flowchart TD"]
    for f in files:
        out.append(f"  {ids[f]}[{label(f'{f} ({count[f]})')}]")
    for f in files:
        for g in sorted(red[f]):
            out.append(f"  {ids[f]} --> {ids[g]}")
    out.extend(["```", ""])
    return "\n".join(out)


# ---------------------------------------------------------------- driver


# ---------------------------------------------------------------- interactive page

HTML_DIR = os.path.join(os.path.dirname(os.path.abspath(__file__)), "proof-graph-html")


def html_data(data: dict) -> str:
    """The graph as compact JSON for the page: files by index, nodes as arrays, edges as index
    pairs. `</` and `<!--` can only occur inside JSON strings; they are escaped (`<\\/`,
    `<\\u0021--`, both valid JSON escapes) so the data cannot close or disturb its <script>."""
    files = sorted({n["file"] for n in data["nodes"]})
    fidx = {f: i for i, f in enumerate(files)}
    nodes = sorted(data["nodes"], key=lambda n: n["name"])
    idx = {n["name"]: i for i, n in enumerate(nodes)}
    compact = {
        "files": files,
        "nodes": [[n["name"], n["kind"], fidx[n["file"]], n["line"], 1 if n["locked"] else 0,
                   sorted(n["specs"]), sorted(n["axioms"]), sorted(n["external"])] for n in nodes],
        "edges": sorted([idx[a], idx[b]] for a, b in data["edges"]
                        if a in idx and b in idx and a != b),
    }
    text = json.dumps(compact, ensure_ascii=False, separators=(",", ":"))
    return text.replace("</", "<\\/").replace("<!--", "<\\u0021--")


def html_page(data: dict) -> str:
    with open(os.path.join(HTML_DIR, "template.html"), encoding="utf-8") as f:
        template = f.read()
    with open(os.path.join(HTML_DIR, "app.js"), encoding="utf-8") as f:
        app = f.read()
    if "</script" in app.lower():
        raise ValueError("app.js must not contain </script")
    head, sep, tail = template.partition("__PROOF_GRAPH_DATA__")
    assert sep and "__PROOF_GRAPH_DATA__" not in tail
    head2, sep2, tail2 = tail.partition("__PROOF_GRAPH_APP__")
    assert sep2 and "__PROOF_GRAPH_APP__" not in tail2
    return head + html_data(data) + head2 + app + tail2


def write(path: str, text: str) -> None:
    os.makedirs(os.path.dirname(path), exist_ok=True)
    with open(path, "w", encoding="utf-8", newline="\n") as f:
        f.write(text)


def check_coverage(data: dict, coverage: dict) -> list:
    """Every (theorem, spec ID) of `proof-coverage.json` must be a node carrying that ID.

    An entry is matched as the extractor matches it: by the last name component and the file.
    Returns the sorted spec IDs the coverage file lists; raises `CoverageError` naming every
    entry that has no such node (a renamed, moved or missing theorem)."""
    by_key = {}
    for n in data["nodes"]:
        by_key.setdefault((n["name"].rsplit(".", 1)[-1], n["file"]), []).append(n)
    missing = []
    ids = set()
    for entry in coverage.get("theorems", []):
        for s in entry.get("specIds", []):
            sid = s["id"]
            ids.add(sid)
            nodes = by_key.get((entry["name"], entry["module"]), [])
            if not any(sid in n["specs"] for n in nodes):
                missing.append(f"{sid}: theorem {entry['name']!r} in {entry['module']!r}")
    if missing:
        raise CoverageError("proof-coverage.json lists theorems that are not graph nodes "
                            "carrying their spec ID:\n  " + "\n  ".join(sorted(missing)))
    return sorted(ids)


def render(data: dict, out_dir: str, threshold: int = DEFAULT_THRESHOLD,
           html_path: str | None = None) -> list:
    by_name = {n["name"]: n for n in data["nodes"]}
    edges = [tuple(e) for e in data["edges"]]
    adj = adjacency(set(by_name), edges)
    specs = {}
    for n in data["nodes"]:
        for s in n["specs"]:
            specs.setdefault(s, []).append(n["name"])
    written = []
    for spec in sorted(specs):
        path = os.path.join(out_dir, "requirements", f"{spec}.md")
        write(path, requirement_page(spec, by_name, adj, sorted(specs[spec]), threshold))
        written.append(path)
    # a spec that no longer has a theorem must not leave its old page behind
    req_dir = os.path.join(out_dir, "requirements")
    if os.path.isdir(req_dir):
        for f in sorted(os.listdir(req_dir)):
            path = os.path.join(req_dir, f)
            if f.endswith(".md") and path not in written:
                os.remove(path)
    path = os.path.join(out_dir, "modules.md")
    write(path, modules_page(by_name, edges))
    written.append(path)
    path = html_path or os.path.join(out_dir, "index.html")
    write(path, html_page(data))
    written.append(path)
    return written


def main(argv=None) -> int:
    p = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    p.add_argument("--in", dest="inp", required=True, help="proof-graph.json (schema v1)")
    p.add_argument("--out", required=True, help="output directory")
    p.add_argument("--html", help="path of the interactive page (default <out>/index.html)")
    p.add_argument("--threshold", type=int, default=DEFAULT_THRESHOLD,
                   help=f"max nodes per diagram before collapsing (default {DEFAULT_THRESHOLD})")
    p.add_argument("--coverage", help="proof-coverage.json: fail unless every listed theorem is "
                                      "a node carrying its spec ID")
    args = p.parse_args(argv)
    try:
        data = load(args.inp)
    except SchemaError as e:
        print(f"proof-graph: {args.inp}: {e}", file=sys.stderr)
        return 2
    cov_ids = None
    if args.coverage:
        with open(args.coverage, encoding="utf-8") as f:
            coverage = json.load(f)
        try:
            cov_ids = check_coverage(data, coverage)
        except CoverageError as e:
            print(f"proof-graph: {args.coverage}: {e}", file=sys.stderr)
            return 3
    written = render(data, args.out, args.threshold, args.html)
    for path in written:
        print(f"proof-graph: wrote {path}")
    pages = sum(1 for p_ in written if os.path.basename(os.path.dirname(p_)) == "requirements")
    if cov_ids is not None:
        print(f"proof-graph: {len(cov_ids)} spec IDs in {args.coverage}, {pages} requirement pages")
        if pages != len(cov_ids):
            print("proof-graph: page count differs from the coverage file's spec IDs",
                  file=sys.stderr)
            return 3
    return 0


if __name__ == "__main__":
    sys.exit(main())
