"""Unit tests for scripts/lean-escape-hatch-check.py.

Run from the repository root: python3 -m unittest scripts/test_lean_escape_hatch_check.py
"""

from __future__ import annotations

import importlib.util
import tempfile
import unittest
from pathlib import Path

_SPEC = importlib.util.spec_from_file_location(
    "lean_escape_hatch_check", Path(__file__).resolve().parent / "lean-escape-hatch-check.py"
)
ehc = importlib.util.module_from_spec(_SPEC)
_SPEC.loader.exec_module(ehc)


def hits(src: str) -> list[tuple[str, int]]:
    """(pattern, line) for every forbidden pattern in the lexed source."""
    out = []
    for ln, line in enumerate(ehc.strip(src).splitlines(), 1):
        for what, pat in ehc.COMPILED:
            if pat.search(line):
                out.append((what, ln))
    return out


class LexerTest(unittest.TestCase):
    def test_length_and_lines_preserved(self):
        src = 'def x := "a\nb" -- c\n/- d\n -/ r#"e\n"# \'f\'\n'
        out = ehc.strip(src)
        self.assertEqual(len(out), len(src))
        self.assertEqual(out.count("\n"), src.count("\n"))

    def test_comments_and_strings_are_prose(self):
        src = (
            "-- sorry\n"
            "/- admit /- nested sorry -/ still comment axiom -/\n"
            'def s := "sorry \\" native_decide"\n'
            "def c := 'x'\n"
        )
        self.assertEqual(hits(src), [])

    def test_code_after_comment_is_seen(self):
        self.assertEqual(hits("/- a /- b -/ c -/ theorem t : False := sorry\n"), [("sorry", 1)])

    def test_raw_string_hides_sorry(self):
        # The quote inside r#"..."# does not close the raw string. A lexer that treats it as a
        # plain string pairs the last quote with the one after `sorry`, and blanks the sorry.
        src = 'def x := r#"a"b"#\ntheorem t : False := sorry\ndef y := "c"\n'
        self.assertEqual(hits(src), [("sorry", 2)])

    def test_raw_string_backslash_does_not_escape(self):
        # In r"..." a backslash is literal, so the string ends at the second quote.
        src = 'def x := r"C:\\" theorem t : False := sorry "\n'
        self.assertIn(("sorry", 1), hits(src))

    def test_raw_string_content_is_prose(self):
        self.assertEqual(hits('def x := r##"sorry "# admit"##\n'), [])

    def test_r_suffix_of_identifier_is_not_raw(self):
        # `fooer"` is an identifier followed by a plain string, not a raw string.
        self.assertEqual(hits('def x := fooer"sorry"\n'), [])

    def test_interpolation_hole_is_code(self):
        self.assertEqual(hits('def x : String := s!"value {sorry}"\n'), [("sorry", 1)])

    def test_interpolation_nested_string(self):
        src = 'def x : String := s!"a {f "}" ++ g sorry} b"\ndef y := "c"\n'
        self.assertEqual(hits(src), [("sorry", 1)])

    def test_interpolation_literal_text_is_prose(self):
        self.assertEqual(hits('def x : String := s!"sorry {n} admit"\n'), [])

    def test_unprefixed_hole_is_code(self):
        self.assertEqual(hits('def f : MetaM Unit := throwError "bad {sorry}"\n'), [("sorry", 1)])

    def test_escaped_brace_is_prose(self):
        self.assertEqual(hits('def x : String := s!"\\{sorry}"\n'), [])

    def test_char_literals(self):
        src = "def a := '\"'\ntheorem t : False := sorry\ndef b := '\\''\ndef c := '\\x41'\n"
        self.assertEqual(hits(src), [("sorry", 2)])

    def test_prime_identifier_is_not_char(self):
        self.assertEqual(hits("theorem t (h' : p) (h'' : q) : False := sorry\n"), [("sorry", 1)])

    def test_guillemet_with_quote_is_code(self):
        self.assertEqual(hits('def «a"b» := 1\ntheorem t : False := sorry\n'), [("sorry", 2)])


class PatternTest(unittest.TestCase):
    def assertHit(self, src: str, what: str):
        self.assertIn(what, [w for w, _ in hits(src)], src)

    def test_new_patterns(self):
        self.assertHit("def x := sorryAx Nat false\n", "sorryAx")
        self.assertHit("run_tac Lean.Elab.admitGoal g\n", "admitGoal")
        self.assertHit("def x := mkSorry t false\n", "mkSorry")
        self.assertHit("example : P := by decide (config := { native := true })\n", "native:=true")
        self.assertHit("example : P := by decide +native\n", "decide+native")
        self.assertHit("set_option debug.skipKernelTC true\n", "skipKernelTC")
        self.assertHit("set_option «debug.skipKernelTC» true\n", "skipKernelTC")
        self.assertHit("set_option debug.«skipKernelTC» true\n", "skipKernelTC")
        self.assertHit("run_cmd addDeclCore env 0 d none\n", "addDeclCore")
        self.assertHit("run_cmd addDeclWithoutChecking env d\n", "addDeclWithoutChecking")
        self.assertHit("run_cmd Lean.addDecl d (doCheck := false)\n", "doCheck")

    def test_old_patterns(self):
        for src, what in [
            ("private axiom cheat : False\n", "axiom"),
            ("example : P := by native_decide\n", "native_decide"),
            ("@[implemented_by g] def f := 1\n", "implemented_by"),
            ("unsafe def f := 1\n", "unsafe"),
            ("example : P := by admit\n", "admit"),
            ("theorem t : False := sorry\n", "sorry"),
            ("@[extern \"c_f\"] def f : Nat := 1\n", "extern"),
            ("@[csimp] theorem t : f = g := rfl\n", "csimp"),
            ("opaque f : Nat\n", "opaque"),
            ("theorem t := Lean.ofReduceBool\n", "ofReduceBool"),
            ("theorem t := Lean.ofReduceNat\n", "ofReduceNat"),
            ("theorem t := Lean.trustCompiler\n", "trustCompiler"),
        ]:
            self.assertHit(src, what)

    def test_word_boundaries(self):
        self.assertEqual(hits("#audit_axioms\ntheorem sorry_free : True := trivial\n"), [])


class ScanTest(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.lean = Path(self.tmp.name) / "lean"
        (self.lean / "Libpetri" / "Sub").mkdir(parents=True)
        (self.lean / "spec-tools").mkdir()
        (self.lean / "ProofGraph").mkdir()
        (self.lean / ".lake" / "pkg").mkdir(parents=True)
        (self.lean / "Libpetri.lean").write_text("import Libpetri.Sub.A\n")
        (self.lean / "Libpetri" / "Sub" / "A.lean").write_text("theorem a : True := trivial\n")
        (self.lean / "spec-tools" / "Audit.lean").write_text("import Libpetri\n")
        (self.lean / "ProofGraph" / "Main.lean").write_text("unsafe def main : IO Unit := pure ()\n")
        (self.lean / ".lake" / "pkg" / "X.lean").write_text("axiom x : False\n")
        (self.lean / "lakefile.toml").write_text('name = "libpetri"\n# moreLeanArgs = ["-DautoImplicit=false"]\n')

    def tearDown(self):
        self.tmp.cleanup()

    def scan(self):
        return ehc.scan(self.lean)[1]

    def test_clean_tree(self):
        self.assertEqual(self.scan(), [])

    def test_message_format(self):
        (self.lean / "spec-tools" / "Report.lean").write_text("\n\ntheorem r : False := sorry\n")
        self.assertEqual(self.scan(), ["ESCAPE sorry lean/spec-tools/Report.lean:3"])

    def test_proofgraph_scanned_and_allowlist_is_narrow(self):
        (self.lean / "ProofGraph" / "Main.lean").write_text(
            "unsafe def main : IO Unit := pure ()\nunsafe def other : Nat := 1\n"
        )
        self.assertEqual(self.scan(), ["ESCAPE unsafe lean/ProofGraph/Main.lean:2"])

    def test_lakefile_options(self):
        (self.lean / "lakefile.toml").write_text(
            'name = "libpetri"\n[[lean_lib]]\nname = "Libpetri"\n'
            'leanOptions = { "debug.skipKernelTC" = true }\nmoreLeanArgs = ["-DautoImplicit=false"]\n'
        )
        self.assertEqual(
            self.scan(),
            [
                "ESCAPE leanOptions lean/lakefile.toml:4",
                "ESCAPE moreLeanArgs lean/lakefile.toml:5",
                "ESCAPE -D lean/lakefile.toml:5",
            ],
        )

    def test_main_exit_codes(self):
        self.assertEqual(ehc.main(["--lean-dir", str(self.lean)]), 0)
        (self.lean / "Libpetri" / "Sub" / "B.lean").write_text('def x := r#"a"b"#\ntheorem t : False := sorry\n')
        self.assertEqual(ehc.main(["--lean-dir", str(self.lean)]), 1)


if __name__ == "__main__":
    unittest.main()
