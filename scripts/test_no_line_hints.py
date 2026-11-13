"""Tests for scripts/no-line-hints.py."""
import importlib.util
import tempfile
import unittest
from pathlib import Path

_spec = importlib.util.spec_from_file_location(
    "no_line_hints", Path(__file__).resolve().parent / "no-line-hints.py")
nlh = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(nlh)


class NoLineHintsTest(unittest.TestCase):
    def scan(self, text: str) -> list[str]:
        with tempfile.TemporaryDirectory() as d:
            p = Path(d) / "x.lean"
            p.write_text(text, encoding="utf-8")
            return nlh.scan(p)

    def test_flags_line_citations(self):
        for text in [
            "see `executor.rs:412`",
            "rust/libpetri-core/src/rewriter.rs:611-698",
            "PetriNet.java:202 binds",
            "transition.ts#L12",
            "`subnet_def.rs`, lines 90-120",
            "line 30 of `Compile.lean`",
            "the second branch (`:118-130`)",
            "BitmapNetExecutor.java 1077-1125",
            "`bitmap-net-executor.ts` 494-518",
            "executor.rs (1084-1090)",
        ]:
            with self.subTest(text=text):
                self.assertEqual(len(self.scan(text)), 1)

    def test_allows_names_and_formula_lines(self):
        for text in [
            "`apply_fusion` in `rewriter.rs`",
            "line 2 of the statement",
            "AC3 and step 5 of [EXEC-001]",
            "`PetriNet.bindActions` (`PetriNet.java`)",
            "ratio 3:1",
        ]:
            with self.subTest(text=text):
                self.assertEqual(self.scan(text), [])


if __name__ == "__main__":
    unittest.main()
