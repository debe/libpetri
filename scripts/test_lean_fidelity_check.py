#!/usr/bin/env python3
"""Tests for scripts/lean-fidelity-check.py.

Run: python3 -m unittest scripts/test_lean_fidelity_check.py
"""

import importlib.util
import os
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
SCRIPT = os.path.join(HERE, "lean-fidelity-check.py")

_spec = importlib.util.spec_from_file_location("lean_fidelity_check", SCRIPT)
lfc = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(lfc)


class MaskRust(unittest.TestCase):
    def test_braces_in_strings_and_comments_are_masked(self):
        src = 'fn f() { let s = "}"; // }\n let c = \'}\'; }\n'
        masked = lfc.mask_rust(src)
        self.assertEqual(len(masked), len(src))
        self.assertEqual(masked.count("{"), 1)
        self.assertEqual(masked.count("}"), 1)

    def test_a_test_module_is_not_part_of_any_pin(self):
        src = (
            "/// doc\nfn remove_matching() { 1 }\n\n"
            "#[cfg(test)]\nmod tests {\n    #[test]\n    fn remove_matching() {}\n}\n"
        )
        spans = lfc.find_spans(src, lfc.mask_rust(src), "remove_matching")
        self.assertEqual(len(spans), 1)
        a, b = spans[0]
        self.assertEqual(src[a:b], "/// doc\nfn remove_matching() { 1 }")


if __name__ == "__main__":
    unittest.main()
