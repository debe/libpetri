#!/usr/bin/env python3
"""Fail when a Lean module escapes the whole-library gates.

The axiom audit (lean/spec-tools/Audit.lean) only sees constants of the modules
it imports. The requirements report (lean/spec-tools/Report.lean) only sees the
@[evidence] tags of the modules it imports, the `cites` tags that become
lean/report/proof-coverage.json included, and the requirement blocks of the
modules lean/Libpetri/Spec/All.lean imports. A module outside an import graph
is never audited, its tags silently never reach the report, and `lake build` of
the default targets does not build it either. Transitive closure would need a
Lean-aware resolver, so the rule is direct imports:

* every module lean/Libpetri.lean and lean/Libpetri/**/*.lean is imported
  directly by lean/spec-tools/Audit.lean and by lean/spec-tools/Report.lean;
* every module lean/Libpetri/Spec/**/*.lean other than All itself is imported
  directly by lean/Libpetri/Spec/All.lean.

An import of a Libpetri module that has no source file is reported too.

Findings print as `MODULES missing <module> in <file>` or
`MODULES unknown <module> in <file>`, <file> relative to the parent of the
Lean directory (lean/...). The prefix is stable; scripts may grep for it.

Usage: lean-module-coverage-check.py [--lean-dir DIR]   (default: <repo>/lean)
Exit 0 when complete, 1 otherwise.

python3 stdlib only.
"""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent

AUDIT = "spec-tools/Audit.lean"
REPORT = "spec-tools/Report.lean"
SPEC_ALL = "Libpetri/Spec/All.lean"

_IMPORT = re.compile(r"^(?:public\s+|private\s+)?(?:meta\s+)?import\s+(?:all\s+)?(.+)$")


def _strip_comments(src: str) -> str:
    """Drop `--` line comments and nested `/- -/` block comments (a header holds no strings)."""
    out, i, n, depth = [], 0, len(src), 0
    while i < n:
        if depth == 0 and src.startswith("--", i):
            j = src.find("\n", i)
            i = n if j < 0 else j
        elif src.startswith("/-", i):
            depth, i = depth + 1, i + 2
        elif depth > 0 and src.startswith("-/", i):
            depth, i = depth - 1, i + 2
        elif depth > 0:
            out.append("\n" if src[i] == "\n" else "")
            i += 1
        else:
            out.append(src[i])
            i += 1
    return "".join(out)


def imports(path: Path) -> set[str]:
    """Module names imported by the header of a Lean file (guillemets removed)."""
    found: set[str] = set()
    for line in _strip_comments(path.read_text(encoding="utf-8")).splitlines():
        line = line.strip()
        if not line or line == "module" or line.startswith("prelude"):
            continue
        m = _IMPORT.match(line)
        if not m:
            break  # the header ends at the first command
        found.update(tok.replace("«", "").replace("»", "") for tok in m.group(1).split())
    return found


def module_name(lean_dir: Path, path: Path) -> str:
    return ".".join(path.relative_to(lean_dir).with_suffix("").parts)


def modules_under(lean_dir: Path, sub: str) -> set[str]:
    d = lean_dir / sub
    if not d.is_dir():
        return set()
    return {module_name(lean_dir, p) for p in d.rglob("*.lean") if ".lake" not in p.parts}


def check(lean_dir: Path) -> tuple[int, list[str]]:
    """Return (modules known, findings)."""
    root = lean_dir.parent
    lib = modules_under(lean_dir, "Libpetri")
    if (lean_dir / "Libpetri.lean").is_file():
        lib.add("Libpetri")
    spec = modules_under(lean_dir, "Libpetri/Spec") - {"Libpetri.Spec.All"}
    bad: list[str] = []
    for rel, want in ((AUDIT, lib), (REPORT, lib), (SPEC_ALL, spec)):
        f = lean_dir / rel
        shown = f.relative_to(root).as_posix()
        if not f.is_file():
            bad.append(f"MODULES missing-file {shown}")
            continue
        have = imports(f)
        bad += [f"MODULES missing {m} in {shown}" for m in sorted(want - have)]
        bad += [
            f"MODULES unknown {m} in {shown}"
            for m in sorted(have)
            if (m == "Libpetri" or m.startswith("Libpetri.")) and m not in lib
        ]
    return len(lib), bad


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--lean-dir", default="lean", help="Lean project directory (repo-relative)")
    a = ap.parse_args(argv)
    lean_dir = Path(a.lean_dir)
    if not lean_dir.is_absolute():
        lean_dir = REPO / lean_dir
    lean_dir = lean_dir.resolve()
    if not (lean_dir / "Libpetri").is_dir():
        sys.stderr.write(f"lean-module-coverage-check: ERROR: no Libpetri/ under {lean_dir}\n")
        return 1
    n, bad = check(lean_dir)
    if bad:
        print(f"lean-module-coverage-check FAILED, {len(bad)} finding(s):")
        for line in bad:
            print(line)
        return 1
    print(f"lean-module-coverage-check ok: {n} Libpetri modules imported by {AUDIT} and {REPORT}, "
          f"Spec modules by {SPEC_ALL}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
