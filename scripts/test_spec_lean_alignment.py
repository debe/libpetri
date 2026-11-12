#!/usr/bin/env python3
"""Tests for scripts/spec-lean-alignment.py (the escape-hatch scanner has its own tests in
scripts/test_lean_escape_hatch_check.py).

Run: python3 -m unittest scripts/test_spec_lean_alignment.py
Every case builds a synthetic spec and registry in a temp directory.
"""

from __future__ import annotations

import contextlib
import importlib.util
import io
import json
import tempfile
import textwrap
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parent


def _load(name: str, file: str):
    spec = importlib.util.spec_from_file_location(name, HERE / file)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


align = _load("spec_lean_alignment", "spec-lean-alignment.py")

INDEX = textwrap.dedent("""\
    # Index

    ## Alphabetical Cross-Reference Index

    ### CORE — Core Model
    | ID | Title | Priority | Depends On |
    |----|-------|----------|------------|
    | CORE-031 | Inhibitor Arc | MUST | — |
    | CORE-032 | Read Arc | MUST | — |

    ### IO — Input & Output
    | ID | Title | Priority | Depends On |
    |----|-------|----------|------------|
    | IO-001 | Input One | MUST | — |
    | ~~IO-006~~ | ~~Input Guard~~ | ~~MUST~~ | — |

    ## Appendix

    | NOPE-001 | Not in the index section | MUST | — |
    """)

CORE = textwrap.dedent("""\
    # 01 — Core

    #### CORE-031: Inhibitor Arc

    **Priority:** MUST

    *While* the inhibitor place holds a token,
    the transition *shall not* fire. The arc does not consume.

    <!-- The hidden comment shall be ignored. -->

    ```python
    # not a heading
    code_inside = "fenced text shall be ignored"
    ```

        indented_code = "shall be ignored"

    A ~~struck sentence shall vanish~~ visible tail.

    **Acceptance Criteria:**
    1. Inhibitor place marked → transition disabled.
    2. Inhibitor place empty → transition
       enabled.

    **Test derivation:** Toggle the inhibitor.

    #### CORE-032: Read Arc

    A read arc tests for a token without consuming it. It shall not consume.
    """)

IO = textwrap.dedent("""\
    # 02 — IO

    #### IO-001: Input One

    `One(place)` consumes exactly 1 token from the place.
    """)

SHALL_1 = "While the inhibitor place holds a token, the transition shall not fire."

# lean/report/requirements.json exactly as `#write_requirements_report` wrote it (2026-11-06,
# after the CORE-031 rewording). Refresh it when the report's shape changes.
REAL_REPORT_JSON = r"""{"title": "libpetri requirements",
 "requirements":
 [{"title": "Inhibitor arc",
   "statement":
   "fun {N} [DecidableEq N] F ↦\n  ∀ (t : Reference.Trans N) (p : N),\n    InhibitorArc t p →\n      (while fun m ↦ Marked m p, never Fire F t) ∧\n        ∀ (m : CountMarking N) (m' : N → ℕ),\n          ¬Marked m p → (Fire F t m m' ↔ Fire F (withoutInhibitor t p) m m')",
   "sourceRef": "spec/01-core-model.md",
   "source": "verbatim",
   "signoff": "pending",
   "scope": "all executors",
   "reading":
   ["For every transition t and every inhibitor place p of t:",
    "t does not fire from a marking in which p is marked;",
    "from a marking m in which p is unmarked, t fires to m' exactly when t without its inhibitor arcs on p fires from m to m'."],
   "quotes":
   ["*While* an inhibitor place of a transition is marked, the transition *shall not* fire.",
    "*While* an inhibitor place of a transition is unmarked, the inhibitor arc *shall not* affect whether the transition can fire."],
   "module": "Libpetri.Spec.Core",
   "kind": "B",
   "id": "CORE-031",
   "hash": "4f884470bf67c07e",
   "evidence":
   [{"theorem": "Libpetri.Spec.CORE_031_reference",
     "role": "holds",
     "module": "Libpetri.Spec.Core"},
    {"theorem": "Libpetri.Spec.CORE_031_forbids_ignoresInhibitor",
     "role": "forbids",
     "module": "Libpetri.Spec.Core"},
    {"theorem": "Libpetri.Spec.CORE_031_forbids_inhibitorAlwaysBlocks",
     "role": "forbids",
     "module": "Libpetri.Spec.Core"},
    {"theorem": "Libpetri.Spec.CORE_031_mutant_dropMarked_killed",
     "role": "mutant",
     "module": "Libpetri.Spec.Core"},
    {"theorem": "Libpetri.Spec.CORE_031_mutant_dropUnmarked_killed",
     "role": "mutant",
     "module": "Libpetri.Spec.Core"},
    {"theorem": "Libpetri.Spec.CORE_031_nonvacuous",
     "role": "nonvacuous",
     "module": "Libpetri.Spec.Core"}],
   "decl": "Libpetri.Spec.CORE_031",
   "assumes":
   ["A firing is read as one step from a marking to a marking (glossary: Fire); timing and priority play no part. 'Can fire' and 'enabled' are both read as 'some firing exists'.",
    "AC1 (inhibitor place empty, enablement unaffected) is the second line: with p unmarked, removing the inhibitor arcs on p changes neither whether t fires nor where it leads.",
    "AC2 (inhibitor place marked, transition disabled) is the first line.",
    "AC3, first half (a firing consumes nothing through its inhibitor arcs): by the second line a firing of t from a marking with p unmarked is a firing of t without its arcs on p, so those arcs add nothing to what it consumes or produces; by the first line t does not fire when p is marked. AC3, second half: what a firing of another transition consumes through an input arc on p is CORE-030's subject, not this block's."]}],
 "citations": []}
"""

# The CORE-031 section of spec/01-core-model.md, verbatim (2026-11-06, after the rewording).
REAL_CORE_031 = textwrap.dedent("""\
    # 01 — Core Model

    #### CORE-031: Inhibitor Arc

    **Priority:** MUST
    **Kind:** B

    An inhibitor arc connects a place to a transition as a **negative precondition**.

    *While* an inhibitor place of a transition is marked, the transition *shall not* fire.

    *While* an inhibitor place of a transition is unmarked, the inhibitor arc *shall not* affect whether the transition can fire.

    The inhibitor arc does not consume tokens.

    **Acceptance Criteria:**
    1. Inhibitor place empty → transition enablement unaffected by inhibitor.
    2. Inhibitor place has tokens → transition disabled.
    3. Firing a transition consumes nothing through its inhibitor arcs; another transition's input arc on the same place consumes as [CORE-030] says.

    **Test derivation:** Create transition with inhibitor; verify disabled when inhibitor place has tokens, enabled when empty.

    ---
    """)


def block(**over) -> dict:
    b = {
        "decl": "Libpetri.Spec.CORE_031",
        "id": "CORE-031",
        "title": "Inhibitor arc",
        "kind": "B",
        "scope": "ALL",
        "source": "verbatim",
        "sourceRef": "spec/01-core.md",
        "quotes": [SHALL_1],
        "reading": ["x"],
        "assumes": ["AC1 and AC2 are read as the quoted sentence."],
        "signoff": "pending",
        "statement": "fun F => True",
        "evidence": [
            {"role": "holds", "theorem": "Libpetri.Spec.ref_CORE_031"},
            {"role": "nonvacuous", "theorem": "Libpetri.Spec.CORE_031_nonvacuous"},
            {"role": "forbids", "theorem": "Libpetri.Spec.CORE_031_forbids"},
        ],
    }
    b.update(over)
    return b


class AlignmentTest(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.root = Path(self.tmp.name)
        self.spec = self.root / "spec"
        self.spec.mkdir()
        (self.spec / "00-index.md").write_text(INDEX)
        (self.spec / "01-core.md").write_text(CORE)
        (self.spec / "02-io.md").write_text(IO)
        self.report = self.root / "requirements.json"

    def tearDown(self):
        self.tmp.cleanup()

    def run_gate(self, data, raw: str | None = None) -> tuple[int, str]:
        self.report.write_text(raw if raw is not None else json.dumps(data))
        out, err = io.StringIO(), io.StringIO()
        with contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
            rc = align.main(["--report", str(self.report), "--spec", str(self.spec)])
        return rc, out.getvalue() + err.getvalue()

    def assertPasses(self, data):
        rc, out = self.run_gate(data)
        self.assertEqual(rc, 0, out)
        return out

    def assertFails(self, data, *fragments):
        rc, out = self.run_gate(data)
        self.assertEqual(rc, 1, out)
        for f in fragments:
            self.assertIn(f, out)
        return out

    # ---- pass cases ------------------------------------------------------

    def test_pass_list_form(self):
        out = self.assertPasses([block()])
        self.assertIn("1 verbatim quotes", out)

    def test_pass_emphasis_and_whitespace_normalised(self):
        q = "*While* the  inhibitor place holds a token,\n the transition _shall not_ fire."
        self.assertPasses([block(quotes=[q])])

    def test_pass_consecutive_sentence_run(self):
        self.assertPasses([block(quotes=[SHALL_1 + " The arc does not consume."])])

    def test_pass_object_form_with_top_level_evidence_and_cites(self):
        b = block(evidence=[])
        data = {
            "blocks": [b, block(decl="Libpetri.Spec.IO_001", id="IO-001", kind="F",
                                sourceRef="spec/02-io.md", assumes=[],
                                quotes=["`One(place)` consumes exactly 1 token from the place."],
                                evidence=[{"role": "allows", "theorem": "T.io"},
                                          {"role": "mutant", "theorem": "T.m"}])],
            "evidence": [
                {"role": "holds", "theorem": "T.h", "reqs": ["Libpetri.Spec.CORE_031"]},
                {"role": "nonvacuous", "theorem": "T.n", "reqs": ["CORE-031"]},
                {"role": "forbids", "theorem": "T.f", "reqs": ["CORE-031"]},
                {"role": "cites", "theorem": "T.c", "module": "Libpetri.X",
                 "id": "CORE-032", "fragment": "read arcs"},
            ],
        }
        out = self.assertPasses(data)
        self.assertIn("1 citations", out)

    # ---- quotes: whole sentences of the section body only ---------------

    def test_fail_quote_drifted(self):
        self.assertFails([block(quotes=["the transition shall fire"])],
                         "ALIGN quote-missing Libpetri.Spec.CORE_031: not a whole sentence",
                         "'#### CORE-031:' body in 01-core.md")

    def test_fail_quote_fragment_of_sentence(self):
        for q in ("the transition shall not fire.",
                  "While the inhibitor place holds a token,",
                  "Inhibitor place marked",
                  SHALL_1 + " The arc"):
            with self.subTest(q=q):
                self.assertFails([block(quotes=[q])], "ALIGN quote-missing")

    def test_fail_quote_from_heading_line(self):
        for q in ("CORE-031: Inhibitor Arc", "Inhibitor Arc", "#### CORE-031: Inhibitor Arc"):
            with self.subTest(q=q):
                self.assertFails([block(quotes=[SHALL_1, q])], "ALIGN quote-missing")

    def test_fail_quote_from_other_section(self):
        self.assertFails([block(quotes=["A read arc tests for a token without consuming it."])],
                         "ALIGN quote-missing")

    def test_fail_quote_from_stripped_text(self):
        for q in ("The hidden comment shall be ignored.",
                  'code_inside = "fenced text shall be ignored"',
                  '# not a heading',
                  'indented_code = "shall be ignored"',
                  "A struck sentence shall vanish visible tail.",
                  "struck sentence shall vanish"):
            with self.subTest(q=q):
                self.assertFails([block(quotes=[SHALL_1, q])], "ALIGN quote-missing")
        # what survives strikethrough removal is quotable
        self.assertPasses([block(quotes=[SHALL_1, "A visible tail."])])

    def test_pass_whole_bullet(self):
        out = self.assertPasses([block(quotes=[SHALL_1, "Inhibitor place empty → transition enabled."],
                                       assumes=["AC1"])])
        self.assertIn("2 verbatim quotes", out)

    def test_fail_missing_heading(self):
        self.assertFails([block(id="CORE-032", decl="D", quotes=["nope"])],
                         "ALIGN quote-missing D: not a whole sentence")
        (self.spec / "01-core.md").write_text(CORE.replace("#### CORE-032: Read Arc", "Read Arc"))
        self.assertFails([block(id="CORE-032", decl="D")],
                         "ALIGN quote-missing D: no '#### CORE-032:' heading")

    def test_fail_wrong_source_ref(self):
        self.assertFails([block(sourceRef="spec/02-io.md")],
                         "ALIGN quote-missing", "sourceRef 'spec/02-io.md' does not name 01-core.md")

    def test_fail_empty_quotes(self):
        self.assertFails([block(quotes=[])], "ALIGN quote-missing", "verbatim block without quotes")

    def test_fail_unknown_source_and_kind(self):
        self.assertFails([block(source="invented", kind="Z")],
                         "ALIGN schema", "unknown source 'invented'", "unknown kind 'Z'")

    # ---- markdown stripping ---------------------------------------------

    def test_strip_fences_commonmark(self):
        s = align.strip_markdown
        # a closing fence must use the opening character and be at least as long
        self.assertEqual(s(["````", "```", "x", "````", "y"]), ["", "", "", "", "y"])
        self.assertEqual(s(["~~~", "```", "x", "~~~~", "y"]), ["", "", "", "", "y"])
        # indented four spaces: not a fence; three: a fence
        self.assertEqual(s(["    ```", "x"]), ["    ```", "x"])
        self.assertEqual(s(["   ```", "x", "   ```", "y"]), ["", "", "", "y"])
        # a closing fence may not carry an info string
        self.assertEqual(s(["```", "``` x", "y"]), ["", "", ""])
        # an unclosed fence runs to the end
        self.assertEqual(s(["```", "x", "#### CORE-031: y"]), ["", "", ""])

    def test_strip_comments_and_strikethrough(self):
        s = align.strip_markdown
        self.assertEqual(s(["a <!-- b --> c", "d <!-- e", "#### X-001: f", "g --> h", "~~i~~ j"]),
                         ["a  c", "d ", "", " h", " j"])

    def test_heading_in_fence_or_comment_is_not_a_heading(self):
        (self.spec / "02-io.md").write_text(
            IO + "\n```\n#### CORE-031: Fake\n```\n\n<!--\n#### CORE-031: Fake\n-->\n")
        self.assertPasses([block()])

    def test_indented_code_inside_list_is_list_text(self):
        u = align.units(["- item one.", "", "    still the item."])
        self.assertEqual([x.sents for x in u], [["item one."], ["still the item."]])
        u = align.units(["para.", "", "    code()"])
        self.assertEqual([x.sents for x in u], [["para."]])

    # ---- coverage of normative text -------------------------------------

    def test_fail_uncovered_acceptance_criteria(self):
        out = self.assertFails([block(assumes=[])],
                               "ALIGN uncovered CORE-031: Acceptance Criteria bullet AC1",
                               "ALIGN uncovered CORE-031: Acceptance Criteria bullet AC2")
        self.assertIn("2 finding(s)", out)

    def test_ac_mention_must_be_ac_n(self):
        self.assertFails([block(assumes=["Acceptance criterion 1 and 2 follow."])],
                         "bullet AC1", "bullet AC2")
        self.assertFails([block(assumes=["AC12 is irrelevant; AC2 too."])], "bullet AC1")

    def test_ac_mentions_across_blocks_of_one_id(self):
        self.assertPasses([block(assumes=["AC1"]), block(decl="D2", assumes=["AC2"])])

    def test_fail_uncovered_shall_sentence(self):
        b = block(quotes=["Inhibitor place marked → transition disabled."], assumes=["AC2"])
        self.assertFails([b], "ALIGN uncovered CORE-031: 'shall' sentence in 01-core.md",
                         repr(SHALL_1))

    def test_shall_sentence_covered_by_exact_text_in_assumes(self):
        b = block(quotes=["Inhibitor place marked → transition disabled."],
                  assumes=["AC2. Read literally: " + SHALL_1])
        self.assertPasses([b])

    def test_shall_in_stripped_text_needs_no_coverage(self):
        # the comment, fence, indented code and strikethrough all say "shall"
        self.assertPasses([block()])

    def test_ids_without_blocks_are_not_checked(self):
        # CORE-032 has an unquoted 'shall' sentence but no block
        self.assertPasses([block()])

    # ---- proposed --------------------------------------------------------

    def test_fail_proposed_not_allowlisted(self):
        b = block(source="proposed", sourceRef="plan", quotes=["text found nowhere"])
        self.assertFails([b], "ALIGN proposed-not-allowed Libpetri.Spec.CORE_031")

    def test_pass_proposed_allowlisted(self):
        (self.spec / "lean-proposed.txt").write_text("# proposed wording\nCORE-031  # pending\n")
        b = block(source="proposed", sourceRef="plan", quotes=["text found nowhere"])
        self.assertPasses([b])

    # ---- no blocks, headings ---------------------------------------------

    def test_fail_no_blocks(self):
        self.assertFails({"title": "t", "requirements": [], "citations": []}, "ALIGN no-blocks")
        self.assertFails([], "ALIGN no-blocks")

    def test_fail_duplicate_heading(self):
        (self.spec / "02-io.md").write_text(IO + "\n#### CORE-031: Again\n")
        self.assertFails([block()],
                         "ALIGN duplicate-heading CORE-031: '#### CORE-031:' at 01-core.md:3 "
                         "and 02-io.md:7")

    def test_warn_non_canonical_heading(self):
        for h in ("### CORE-032: Again", "#### CORE-032 : Again", "####CORE-032: Again"):
            with self.subTest(h=h):
                (self.spec / "02-io.md").write_text(IO + f"\n{h}\n\nx\n")
                rc, out = self.run_gate([block()])
                self.assertEqual(rc, 0, out)
                self.assertIn("WARNING: 02-io.md:7: non-canonical requirement heading", out)

    # ---- evidence --------------------------------------------------------

    def test_fail_no_evidence(self):
        self.assertFails([block(kind="F", evidence=[])],
                         "ALIGN evidence-missing Libpetri.Spec.CORE_031: no evidence theorem")

    def test_fail_b_without_holds(self):
        b = block(evidence=[{"role": "nonvacuous", "theorem": "T.n"}, {"role": "mutant", "theorem": "T.m"}])
        self.assertFails([b], "ALIGN evidence-missing", "kind-B block without a 'holds' evidence theorem")

    def test_fail_b_without_nonvacuous(self):
        b = block(evidence=[{"role": "holds", "theorem": "T.h"}, {"role": "forbids", "theorem": "T.f"}])
        self.assertFails([b], "ALIGN evidence-missing", "kind-B block without a 'nonvacuous' evidence theorem")

    def test_fail_without_negative_example(self):
        b = block(kind="F", evidence=[{"role": "allows", "theorem": "T.a"}])
        self.assertFails([b], "ALIGN evidence-missing", "no 'forbids' or 'mutant' evidence theorem")
        b = block(kind="F", evidence=[{"role": "mutant", "theorem": "T.m"}])
        self.assertPasses([b])

    def test_cites_in_block_evidence_do_not_count(self):
        b = block(kind="F", evidence=[{"role": "cites", "theorem": "T.c",
                                        "id": "CORE-031", "fragment": "f"}])
        self.assertFails([b], "ALIGN evidence-missing", "no evidence theorem")

    # ---- IDs and citations -----------------------------------------------

    def test_fail_block_id_not_active(self):
        (self.spec / "01-core.md").write_text(CORE + "\n#### CORE-099: Ghost\n\nboo\n")
        self.assertFails([block(id="CORE-099", decl="D", quotes=["boo"])],
                         "ALIGN id-inactive D: CORE-099 is not an active requirement")

    def test_fail_block_id_tombstoned(self):
        (self.spec / "02-io.md").write_text(IO + "\n#### IO-006: Gone\n\nboo\n")
        self.assertFails([block(id="IO-006", decl="D", sourceRef="spec/02-io.md",
                                quotes=["boo"], assumes=[])],
                         "ALIGN id-inactive D: IO-006 is a removed (tombstoned) requirement")

    def test_fail_cites_inactive_tombstoned_malformed_empty(self):
        data = {"blocks": [block()], "cites": [
            {"theorem": "T.a", "module": "M", "id": "NOPE-001", "fragment": "x"},
            {"theorem": "T.b", "module": "M", "id": "IO-006", "fragment": "x"},
            {"theorem": "T.c", "module": "M", "id": "core-1", "fragment": "x"},
            {"theorem": "T.d", "module": "M", "id": "IO-001", "fragment": "  "},
        ]}
        self.assertFails(data,
                         "ALIGN citation-inactive T.a (M): cites NOPE-001, which is not an active requirement",
                         "ALIGN citation-inactive T.b (M): cites IO-006, a removed (tombstoned) requirement",
                         "ALIGN citation-inactive T.c (M): cites malformed ID 'core-1'",
                         "ALIGN citation-empty T.d (M): cites IO-001 with an empty fragment")

    # ---- the report's real JSON shape -------------------------------------

    def _real(self, citations=None, extra_assumes=(), drop_ac=False):
        data = json.loads(REAL_REPORT_JSON)
        if citations is not None:
            data["citations"] = citations
        req = data["requirements"][0]
        if drop_ac:
            req["assumes"] = [a for a in req["assumes"] if not a.startswith("AC")]
        req["assumes"] += list(extra_assumes)
        (self.spec / "01-core.md").write_text(REAL_CORE_031)
        req["sourceRef"] = "spec/01-core.md"
        return data

    def test_real_shape_reads_citations_key(self):
        cites = [
            {"role": "cites", "id": "CORE-999", "fragment": "an inhibitor arc",
             "theorem": "Libpetri.X.t1", "module": "Libpetri.X"},
            {"role": "cites", "id": "IO-006", "fragment": "guard",
             "theorem": "Libpetri.X.t2", "module": "Libpetri.X"},
        ]
        out = self.assertFails(
            self._real(cites, ["AC1, AC2 and AC3 are read as the two quotes."]),
            "ALIGN citation-inactive Libpetri.X.t1 (Libpetri.X): cites CORE-999, "
            "which is not an active requirement",
            "ALIGN citation-inactive Libpetri.X.t2 (Libpetri.X): cites IO-006, "
            "a removed (tombstoned) requirement")
        self.assertIn("2 finding(s)", out)

    def test_real_shape_as_committed_passes(self):
        out = self.assertPasses(self._real())
        self.assertIn("2 verbatim quotes", out)

    def test_real_shape_without_ac_lines_is_uncovered(self):
        out = self.assertFails(self._real(drop_ac=True), "bullet AC1", "bullet AC2", "bullet AC3")
        self.assertIn("3 finding(s)", out)

    def test_real_shape_passes_with_ac_mentions_and_active_citation(self):
        cites = [{"role": "cites", "id": "CORE-032", "fragment": "read arc",
                  "theorem": "Libpetri.X.t", "module": "Libpetri.X"}]
        out = self.assertPasses(self._real(cites, ["AC1, AC2 and AC3 are read as the two quotes."]))
        self.assertIn("2 verbatim quotes", out)
        self.assertIn("1 citations", out)

    # ---- Kind lines (ruling D21) -------------------------------------------

    def _with_kinds(self, k031=None, k032=None, k001=None):
        """Write the fixture spec with `**Kind:**` lines under the given headings."""
        core = CORE
        if k031 is not None:
            core = core.replace("**Priority:** MUST\n", f"**Priority:** MUST\n**Kind:** {k031}\n", 1)
        if k032 is not None:
            core = core.replace("#### CORE-032: Read Arc\n", f"#### CORE-032: Read Arc\n\n**Kind:** {k032}\n", 1)
        (self.spec / "01-core.md").write_text(core)
        io_text = IO
        if k001 is not None:
            io_text = io_text.replace("#### IO-001: Input One\n", f"#### IO-001: Input One\n\n**Kind:** {k001}\n", 1)
        (self.spec / "02-io.md").write_text(io_text)

    def run_gate_args(self, data, *extra) -> tuple[int, str]:
        self.report.write_text(json.dumps(data))
        out, err = io.StringIO(), io.StringIO()
        with contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
            rc = align.main(["--report", str(self.report), "--spec", str(self.spec), *extra])
        return rc, out.getvalue() + err.getvalue()

    def test_kind_line_matching_block_passes(self):
        self._with_kinds(k031="B", k032="Q", k001="N")
        self.assertPasses([block()])

    def test_real_shape_kind_line_is_read(self):
        data = self._real()
        (self.spec / "01-core.md").write_text(REAL_CORE_031.replace("**Kind:** B", "**Kind:** F"))
        self.assertFails(data, "ALIGN kind-mismatch CORE-031: the section in 01-core.md:",
                         "says Kind F, but no block of CORE-031 has kind F (blocks: B)")

    def test_companion_block_of_another_kind_passes(self):
        self._with_kinds(k031="B")
        self.assertPasses([block(), block(decl="Libpetri.Spec.CORE_031_table", kind="F",
                                          evidence=[{"role": "forbids", "theorem": "x"}])])

    def test_fail_kind_line_without_a_block_of_that_kind(self):
        self._with_kinds(k031="T")
        out = self.assertFails([block()], "ALIGN kind-mismatch CORE-031",
                               "says Kind T, but no block of CORE-031 has kind T (blocks: B)")
        self.assertIn("1 finding(s)", out)

    def test_fail_stated_kind_without_any_block(self):
        self._with_kinds(k032="F")
        self.assertFails([block()], "ALIGN kind-mismatch CORE-032",
                         "a stated kind, but CORE-032 has no requirement block")

    def test_q_a_n_kinds_need_no_block(self):
        for k in "QAN":
            self._with_kinds(k032=k)
            self.assertPasses([block()])

    def test_fail_malformed_or_repeated_kind_line(self):
        self._with_kinds(k031="B+Q", k032="Q\n**Kind:** A")
        self.assertFails([block()], "ALIGN kind-mismatch CORE-031: '**Kind:** B+Q'",
                         "ALIGN kind-mismatch CORE-032: the section in 01-core.md:",
                         "has 2 '**Kind:**' lines (Q, A); expected one")

    def test_kind_line_in_code_or_comment_does_not_count(self):
        core = CORE.replace("**Priority:** MUST\n", "**Priority:** MUST\n<!-- **Kind:** T -->\n", 1)
        (self.spec / "01-core.md").write_text(core)
        self.assertPasses([block()])

    def test_kind_missing_only_with_require_kind(self):
        self._with_kinds(k031="B")
        self.assertPasses([block()])
        rc, out = self.run_gate_args([block()], "--require-kind")
        self.assertEqual(rc, 1, out)
        self.assertIn("ALIGN kind-missing CORE-032", out)
        self.assertIn("ALIGN kind-missing IO-001", out)
        self.assertNotIn("kind-missing CORE-031", out)
        self.assertIn("2 finding(s)", out)
        self._with_kinds(k031="B", k032="Q", k001="Q")
        rc, out = self.run_gate_args([block()], "--require-kind")
        self.assertEqual(rc, 0, out)

    # ---- output format and input errors ----------------------------------

    def test_fail_all_findings_reported_together_with_prefix(self):
        rc, out = self.run_gate([block(quotes=["drift"], evidence=[])])
        self.assertEqual(rc, 1)
        self.assertIn("6 finding(s)", out)
        lines = out.splitlines()
        self.assertTrue(lines[0].startswith("spec-lean-alignment FAILED"))
        for line in lines[1:]:
            self.assertTrue(line.startswith("ALIGN "), line)

    def test_fail_missing_report(self):
        out = io.StringIO()
        with contextlib.redirect_stderr(out):
            rc = align.main(["--report", str(self.root / "absent.json"), "--spec", str(self.spec)])
        self.assertEqual(rc, 1)
        self.assertIn("not found", out.getvalue())

    def test_fail_bad_json(self):
        self.report.write_text("{not json")
        out = io.StringIO()
        with contextlib.redirect_stderr(out):
            rc = align.main(["--report", str(self.report), "--spec", str(self.spec)])
        self.assertEqual(rc, 1)
        self.assertIn("not valid JSON", out.getvalue())

    def test_fail_index_without_section(self):
        (self.spec / "00-index.md").write_text("# Index\n")
        rc, out = self.run_gate([block()])
        self.assertEqual(rc, 1)
        self.assertIn("Alphabetical Cross-Reference Index", out)


if __name__ == "__main__":
    unittest.main()
