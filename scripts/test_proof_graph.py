#!/usr/bin/env python3
"""Tests for scripts/proof-graph.py against scripts/testdata/proof-graph.sample.json.

Run: python3 scripts/test_proof_graph.py
"""

import filecmp
import importlib.util
import json
import os
import subprocess
import sys
import tempfile
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
SCRIPT = os.path.join(HERE, "proof-graph.py")
SAMPLE = os.path.join(HERE, "testdata", "proof-graph.sample.json")

_spec = importlib.util.spec_from_file_location("proof_graph", SCRIPT)
pg = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(pg)


def run(out_dir, *extra, inp=SAMPLE):
    return subprocess.run([sys.executable, SCRIPT, "--in", inp, "--out", out_dir, *extra],
                          capture_output=True, text=True)


def read(path):
    with open(path, encoding="utf-8") as f:
        return f.read()


def mermaid_blocks(page):
    return page.split("```mermaid\n")[1:]


def node_count(block):
    """Node declarations (n<i>[…] or c<i>[…]) in one Mermaid block."""
    body = block.split("```", 1)[0]
    return sum(1 for line in body.splitlines()
               if line.strip()[:1] in ("n", "c") and "[" in line and "-->" not in line
               and not line.strip().startswith(("classDef", "class ")))


def all_files(root):
    out = []
    for d, _, files in os.walk(root):
        for f in files:
            out.append(os.path.relpath(os.path.join(d, f), root))
    return sorted(out)


class ProofGraphTest(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.out = self.tmp.name
        with open(SAMPLE, encoding="utf-8") as f:
            self.data = json.load(f)
        self.ids = pg.Ids([n["name"] for n in self.data["nodes"]])

    def tearDown(self):
        self.tmp.cleanup()

    def test_a_transitive_reduction_diamond(self):
        top, left, right, bottom = (f"Libpetri.Sample.diamond{s}" for s in ("Top", "Left", "Right", "Bottom"))
        adj = {top: {left, right, bottom}, left: {bottom}, right: {bottom}, bottom: set()}
        red = pg.transitive_reduction(adj)
        self.assertEqual(red[top], {left, right})
        self.assertEqual(red[left], {bottom})
        self.assertEqual(red[right], {bottom})
        # and in the rendered page: the shortcut top -> bottom is gone, the diamond stays
        r = run(self.out)
        self.assertEqual(r.returncode, 0, r.stderr)
        page = read(os.path.join(self.out, "requirements", "DEMO-001.md"))
        self.assertNotIn(f"{self.ids[top]} --> {self.ids[bottom]}\n", page)
        for a, b in ((top, left), (top, right), (left, bottom), (right, bottom)):
            self.assertIn(f"{self.ids[a]} --> {self.ids[b]}\n", page)
        # a longer shortcut: right -> Marking is implied by right -> bottom -> fire_mono -> fire -> Marking
        self.assertNotIn(f"{self.ids[right]} --> {self.ids['Libpetri.Sample.Marking']}\n", page)
        self.assertIn(f"{self.ids['Libpetri.Sample.fire']} --> {self.ids['Libpetri.Sample.Marking']}\n", page)

    def test_a_reduction_keeps_cycles_connected(self):
        adj = {"u": {"v", "w"}, "v": {"w"}, "w": {"v"}}
        red = pg.transitive_reduction(adj)
        self.assertTrue(red["u"], "u must stay connected to its cycle")
        self.assertEqual(red["v"], {"w"})
        self.assertEqual(red["w"], {"v"})

    def test_b_collapse_above_threshold(self):
        r = run(self.out, "--threshold", "6")
        self.assertEqual(r.returncode, 0, r.stderr)
        page = read(os.path.join(self.out, "requirements", "DEMO-001.md"))
        self.assertIn("is collapsed into one node, leaving 6.", page)
        self.assertIn("📁 Libpetri/Sample/Lemmas.lean (", page)
        self.assertIn("📁 Libpetri/Sample/Core.lean (", page)
        # below the threshold nothing is collapsed
        r = run(self.out)
        page = read(os.path.join(self.out, "requirements", "DEMO-001.md"))
        self.assertNotIn("📁", page)

    def test_b_split_when_still_too_big(self):
        r = run(self.out, "--threshold", "2")
        self.assertEqual(r.returncode, 0, r.stderr)
        page = read(os.path.join(self.out, "requirements", "DEMO-001.md"))
        self.assertIn("so it is split by direct dependency", page)
        self.assertEqual(page.count("```mermaid"), 3)
        self.assertEqual(page.count("> Rule: "), 3)
        for block in mermaid_blocks(page):
            self.assertGreaterEqual(node_count(block), pg.MIN_SPLIT_NODES)

    def test_b_split_by_root_first(self):
        # two theorems carrying X, each with its own 4-node chain in its own file: 10 nodes over
        # the limit 6, but each root's tree (5 nodes) fits, so one diagram per root
        nodes, edges = [], []

        def node(name, file, specs=()):
            nodes.append({"name": name, "kind": "theorem", "module": file[:-5].replace("/", "."),
                          "file": file, "line": 1, "specs": list(specs), "locked": False,
                          "axioms": [], "external": []})
        for r in ("A", "B"):
            f = f"Libpetri/T/{r}.lean"
            node(f"Libpetri.T.{r}.root", f, ["X-001"])
            for i in range(4):
                node(f"Libpetri.T.{r}.l{i}", f)
            edges.append([f"Libpetri.T.{r}.root", f"Libpetri.T.{r}.l0"])
            for i in range(3):
                edges.append([f"Libpetri.T.{r}.l{i}", f"Libpetri.T.{r}.l{i + 1}"])
        # a trivial second root: a leaf of its own, must not become a 1-2 node diagram
        node("Libpetri.T.C.tiny", "Libpetri/T/C.lean", ["X-001"])
        node("Libpetri.T.C.leaf", "Libpetri/T/C.lean")
        edges.append(["Libpetri.T.C.tiny", "Libpetri.T.C.leaf"])
        data = {"schema": pg.SCHEMA, "nodes": sorted(nodes, key=lambda n: n["name"]),
                "edges": sorted(edges)}
        pg.render(data, self.out, threshold=6)
        page = read(os.path.join(self.out, "requirements", "X-001.md"))
        self.assertIn("one diagram per theorem (3 theorems)", page)
        self.assertEqual(page.count("```mermaid"), 2)
        self.assertEqual(page.count("> Rule: this theorem's whole tree, 5 nodes."), 2)
        for block in mermaid_blocks(page):
            self.assertGreaterEqual(node_count(block), pg.MIN_SPLIT_NODES)
        self.assertIn("Shared leaves of `Libpetri.T.C.tiny`", page)
        self.assertIn("- `Libpetri.T.C.leaf` (`Libpetri/T/C.lean`)", page)

    def test_c_deterministic(self):
        a = os.path.join(self.out, "a")
        b = os.path.join(self.out, "b")
        self.assertEqual(run(a).returncode, 0)
        self.assertEqual(run(b).returncode, 0)
        fa, fb = all_files(a), all_files(b)
        self.assertEqual(fa, fb)
        self.assertEqual(fa, ["index.html", "modules.md", "requirements/DEMO-001.md",
                              "requirements/DEMO-002.md"])
        _, mismatch, errors = filecmp.cmpfiles(a, b, fa, shallow=False)
        self.assertEqual((mismatch, errors), ([], []))

    def test_d_bad_schema_rejected(self):
        bad = dict(self.data, schema="libpetri-proofgraph/2")
        path = os.path.join(self.out, "bad.json")
        with open(path, "w", encoding="utf-8") as f:
            json.dump(bad, f)
        r = run(os.path.join(self.out, "o"), inp=path)
        self.assertNotEqual(r.returncode, 0)
        self.assertIn("unsupported schema 'libpetri-proofgraph/2'", r.stderr)
        self.assertFalse(os.path.exists(os.path.join(self.out, "o")))

    def test_ids_and_labels_are_safe(self):
        r = run(self.out)
        page = read(os.path.join(self.out, "requirements", "DEMO-002.md"))
        # unicode, apostrophes and ✝ only ever appear inside quoted labels
        for name in ("Libpetri.Sample.σ_step", "Libpetri.Sample.aux'", "Libpetri.Sample.helper✝"):
            if name in page:
                self.assertIn(f'["{name}"]', page)
        self.assertIn("Axioms used:", page)
        self.assertIn("- `Libpetri.Sample.safety`: `propext`", page)

    def _coverage(self, entries):
        path = os.path.join(self.out, "coverage.json")
        with open(path, "w", encoding="utf-8") as f:
            json.dump({"theorems": entries}, f)
        return path

    def test_coverage_ok_counts_pages(self):
        cov = self._coverage([
            {"name": "diamondTop", "module": "Libpetri/Sample/Main.lean",
             "specIds": [{"id": "DEMO-001", "fragment": "x"}]},
            {"name": "safety", "module": "Libpetri/Sample/Main.lean",
             "specIds": [{"id": "DEMO-002", "fragment": "y"}]},
        ])
        r = run(os.path.join(self.out, "o"), "--coverage", cov)
        self.assertEqual(r.returncode, 0, r.stderr)
        self.assertIn("2 spec IDs in", r.stdout)
        self.assertIn("2 requirement pages", r.stdout)

    def test_coverage_missing_theorem_fails_loudly(self):
        cov = self._coverage([
            {"name": "diamondTop", "module": "Libpetri/Sample/Main.lean",
             "specIds": [{"id": "DEMO-001", "fragment": "x"}]},
            # renamed or moved: no node `renamedAway` in that file
            {"name": "renamedAway", "module": "Libpetri/Sample/Main.lean",
             "specIds": [{"id": "DEMO-003", "fragment": "z"}]},
            # right name, wrong file
            {"name": "safety", "module": "Libpetri/Sample/Lemmas.lean",
             "specIds": [{"id": "DEMO-002", "fragment": "y"}]},
        ])
        out = os.path.join(self.out, "o")
        r = run(out, "--coverage", cov)
        self.assertEqual(r.returncode, 3)
        self.assertIn("DEMO-003: theorem 'renamedAway'", r.stderr)
        self.assertIn("DEMO-002: theorem 'safety' in 'Libpetri/Sample/Lemmas.lean'", r.stderr)
        self.assertFalse(os.path.exists(out))

    def test_stale_pages_removed(self):
        stale = os.path.join(self.out, "requirements", "GONE-001.md")
        os.makedirs(os.path.dirname(stale))
        with open(stale, "w", encoding="utf-8") as f:
            f.write("old\n")
        self.assertEqual(run(self.out).returncode, 0)
        self.assertFalse(os.path.exists(stale))
        self.assertEqual(all_files(self.out),
                         ["index.html", "modules.md", "requirements/DEMO-001.md",
                          "requirements/DEMO-002.md"])

    def _html(self):
        self.assertEqual(run(self.out).returncode, 0)
        return read(os.path.join(self.out, "index.html"))

    def test_html_data_round_trips(self):
        page = self._html()
        start = page.index('<script id="graph-data" type="application/json">') + \
            len('<script id="graph-data" type="application/json">')
        end = page.index("</script>", start)
        data = json.loads(page[start:end])
        self.assertEqual(len(data["nodes"]), len(self.data["nodes"]))
        self.assertEqual(len(data["edges"]), len(self.data["edges"]))
        names = [n[0] for n in data["nodes"]]
        self.assertEqual(names, sorted(n["name"] for n in self.data["nodes"]))
        # every edge maps back to the same pair of names
        back = sorted([names[a], names[b]] for a, b in data["edges"])
        self.assertEqual(back, sorted(self.data["edges"]))
        top = data["nodes"][names.index("Libpetri.Sample.diamondTop")]
        self.assertEqual(top[4], 1)  # locked
        self.assertEqual(top[6], ["Quot.sound", "propext"])  # axioms

    def test_html_deterministic(self):
        a, b = os.path.join(self.out, "a"), os.path.join(self.out, "b")
        run(a)
        run(b)
        with open(os.path.join(a, "index.html"), "rb") as fa, \
                open(os.path.join(b, "index.html"), "rb") as fb:
            self.assertEqual(fa.read(), fb.read())

    def test_html_fetches_nothing_remote(self):
        import re
        page = self._html()
        # no src=/href=/url() pointing at a host, no fetch/XHR/dynamic import at all
        self.assertIsNone(re.search(r'(src|href)\s*=\s*["\']?\s*(https?:)?//', page, re.I))
        self.assertIsNone(re.search(r'url\(\s*["\']?\s*(https?:)?//', page, re.I))
        for api in ("fetch(", "XMLHttpRequest", "import(", "<link", "<iframe", "@import"):
            self.assertNotIn(api, page)
        # the only URL-shaped strings are the SVG namespace identifier (never dereferenced)
        urls = set(re.findall(r"https?://[^\s\"'<>)]+", page))
        self.assertEqual(urls, {"http://www.w3.org/2000/svg"})

    def test_html_script_not_closed_by_data(self):
        data = dict(self.data)
        data["nodes"] = [dict(n) for n in self.data["nodes"]]
        data["nodes"][0] = dict(data["nodes"][0], external=["</script><b>x", "<!-- y"])
        text = pg.html_data(data)
        self.assertNotIn("</", text)
        self.assertNotIn("<!--", text)
        self.assertEqual(json.loads(text)["nodes"][0][7], sorted(["</script><b>x", "<!-- y"]))

    def test_modules_page(self):
        run(self.out)
        page = read(os.path.join(self.out, "modules.md"))
        self.assertIn('f0["Libpetri/Sample/Core.lean (5)"]', page)
        self.assertIn("f2 --> f1", page)   # Main -> Lemmas
        self.assertIn("f1 --> f0", page)   # Lemmas -> Core
        # Main -> Core exists (diamondRight -> Marking) but is implied by Main -> Lemmas -> Core
        self.assertNotIn("f2 --> f0", page)


if __name__ == "__main__":
    unittest.main(verbosity=2)
