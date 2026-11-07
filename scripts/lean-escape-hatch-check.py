#!/usr/bin/env python3
"""Fail when a Lean source of the project uses an escape hatch.

Scans lean/Libpetri/**/*.lean, lean/*.lean, lean/spec-tools/**/*.lean and
lean/ProofGraph/**/*.lean (never .lake/). Comments and the text of string and
char literals are blanked first, so prose may mention the words; code may not.
Lexing follows Lean: nested /- -/ comments, escapes, raw strings r"..." and
r#"..."# (no escapes, closed by the matching number of #), char literals,
«guillemet» identifiers, and string interpolation: the {...} holes of an
s!/m!/f! string are lexed as code (nested strings included), and a balanced
{...} without quotes inside a plain string is kept as code too, because
throwError and friends interpolate unprefixed strings.

Forbidden: sorry and its elaborator forms, admit, native_decide / decide
+native / native := true, any `axiom` (whatever its visibility), the
attributes and keywords that link proofs to compiled code, and the kernel
bypasses (skipKernelTC, addDeclCore, addDeclWithoutChecking, doCheck).

lean/lakefile.toml (and lakefile.lean, if present) is scanned for options that
reach every module: leanOptions, moreLeanArgs, weakLeanArgs, and -D flags.

Every finding prints as `ESCAPE <pattern> <file>:<line>` with <file> relative
to the parent of the Lean directory (lean/...). The prefix is stable; scripts
may grep for it.

Usage: lean-escape-hatch-check.py [--lean-dir DIR]   (default: <repo>/lean)
Exit 0 when clean, 1 when anything is found.

python3 stdlib only.
"""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent

# pattern name (stable, no spaces) -> regex over lexed code
FORBIDDEN = {
    "sorry": r"\bsorry\b",
    "sorryAx": r"\bsorryAx\b",
    "mkSorry": r"\bmkSorry\b",
    "admit": r"\badmit\b",
    "admitGoal": r"\badmitGoal\b",
    "native_decide": r"\bnative_decide\b",
    "decide+native": r"\+\s*native\b",
    "native:=true": r"\bnative\s*:=\s*true\b",
    "axiom": r"\baxiom\b",
    "implemented_by": r"\bimplemented_by\b",
    "extern": r"\bextern\b",
    "csimp": r"\bcsimp\b",
    "unsafe": r"\bunsafe\b",
    "opaque": r"\bopaque\b",
    "ofReduceBool": r"\bofReduceBool\b",
    "ofReduceNat": r"\bofReduceNat\b",
    "trustCompiler": r"\btrustCompiler\b",
    # Matches debug.skipKernelTC, «debug.skipKernelTC» and debug.«skipKernelTC»:
    # guillemet text stays in the lexed code and « » are not word characters.
    "skipKernelTC": r"\bskipKernelTC\b",
    "addDeclCore": r"\baddDeclCore\b",
    "addDeclWithoutChecking": r"\baddDeclWithoutChecking\b",
    "doCheck": r"\bdoCheck\b",
}
COMPILED = [(what, re.compile(p)) for what, p in FORBIDDEN.items()]

# lakefile options that apply to every module of a library.
LAKEFILE = {
    "leanOptions": r"\bleanOptions\b",
    "moreLeanArgs": r"\bmoreLeanArgs\b",
    "weakLeanArgs": r"\bweakLeanArgs\b",
    "-D": r"(?<![\w-])-D",
}
LAKEFILE_COMPILED = [(what, re.compile(p)) for what, p in LAKEFILE.items()]

# Narrow, reviewed exceptions: (file relative to the Lean dir, pattern, regex the line must match).
# ProofGraph is the graph extractor executable, not a proof; its entry point loads the environment.
ALLOW = [
    ("ProofGraph/Main.lean", "unsafe", re.compile(r"^unsafe def main\b")),
]


def _ident_char(c: str) -> bool:
    return c.isalnum() or c in "_'!?"


class _Lexer:
    """Blanks comments and literal text of Lean source, keeping length and line breaks."""

    def __init__(self, src: str) -> None:
        self.src, self.n, self.i, self.out = src, len(src), 0, []

    def blank(self, j: int) -> None:
        """Blank src[i:j] (newlines kept) and advance to j."""
        self.out.append(re.sub(r"[^\n]", " ", self.src[self.i:j]))
        self.i = j

    def keep(self, j: int) -> None:
        self.out.append(self.src[self.i:j])
        self.i = j

    def prev(self) -> str:
        return self.src[self.i - 1] if self.i > 0 else ""

    def code(self, in_hole: bool = False) -> None:
        """Lex code; inside an interpolation hole, stop before the `}` that closes it."""
        s, depth = self.src, 0
        while self.i < self.n:
            c = s[self.i]
            if s.startswith("--", self.i):
                j = s.find("\n", self.i)
                self.blank(self.n if j < 0 else j)
            elif s.startswith("/-", self.i):
                self.block_comment()
            elif c == "«":
                j = s.find("»", self.i + 1)
                self.keep(self.n if j < 0 else j + 1)
            elif c == "r" and not _ident_char(self.prev()) and re.match(r'r#*"', s[self.i:self.i + 300]):
                self.raw_string()
            elif c == '"':
                interp = self.prev() == "!" and self.i >= 2 and _ident_char(s[self.i - 2])
                self.string(interp)
            elif c == "'" and not _ident_char(self.prev()) and self.char_literal():
                pass
            elif in_hole and c == "}" and depth == 0:
                return
            else:
                if c == "{":
                    depth += 1
                elif c == "}" and depth > 0:
                    depth -= 1
                self.keep(self.i + 1)

    def block_comment(self) -> None:
        s, j, depth = self.src, self.i, 0
        while j < self.n:
            if s.startswith("/-", j):
                depth, j = depth + 1, j + 2
            elif s.startswith("-/", j):
                depth, j = depth - 1, j + 2
                if depth == 0:
                    break
            else:
                j += 1
        self.blank(j)

    def raw_string(self) -> None:
        m = re.match(r'r(#*)"', self.src[self.i:])
        close = '"' + m.group(1)
        j = self.src.find(close, self.i + len(m.group(0)))
        self.blank(self.n if j < 0 else j + len(close))

    def string(self, interp: bool) -> None:
        s = self.src
        self.blank(self.i + 1)  # opening quote
        while self.i < self.n:
            c = s[self.i]
            if c == "\\":
                self.blank(min(self.i + 2, self.n))
            elif c == '"':
                self.blank(self.i + 1)
                return
            elif c == "{" and interp:
                self.keep(self.i + 1)
                self.code(in_hole=True)
                if self.i < self.n:
                    self.keep(self.i + 1)  # the closing }
            elif c == "{":
                # Unprefixed string: a balanced hole with no quote or brace inside stays code,
                # so `throwError "{sorry}"` is seen. A hole holding a nested string desyncs the
                # quote parity for that hole only, and the parity is restored right after it.
                m = re.match(r'\{[^"{}\\]*\}', s[self.i:])
                if m:
                    self.keep(self.i + m.end())
                else:
                    self.blank(self.i + 1)
            else:
                self.blank(self.i + 1)

    def char_literal(self) -> bool:
        """Blank a char literal at i ('a', '\\n', '\\x41', '\\u{1F600}'); False if there is none."""
        m = re.match(r"'(?:\\(?:x[0-9a-fA-F]{2}|u\{[0-9a-fA-F]+\}|.)|[^'\\\n])'", self.src[self.i:self.i + 16])
        if not m:
            return False
        self.blank(self.i + m.end())
        return True


def strip(src: str) -> str:
    """Blank out comments and string/char literal text of Lean source, keeping line numbers."""
    lx = _Lexer(src)
    lx.code()
    return "".join(lx.out)


def strip_toml(src: str) -> str:
    """Blank TOML comments (`#` outside a quoted string), keeping line numbers."""
    lines = []
    for line in src.split("\n"):
        quote, k = None, 0
        while k < len(line):
            c = line[k]
            if quote:
                if c == "\\" and quote == '"':
                    k += 1
                elif c == quote:
                    quote = None
            elif c in "\"'":
                quote = c
            elif c == "#":
                line = line[:k]
                break
            k += 1
        lines.append(line)
    return "\n".join(lines)


def lean_files(lean_dir: Path) -> list[Path]:
    """lean/*.lean plus every .lean under Libpetri/, spec-tools/, ProofGraph/, skipping .lake."""
    files = set(lean_dir.glob("*.lean"))
    for sub in ("Libpetri", "spec-tools", "ProofGraph"):
        d = lean_dir / sub
        if d.is_dir():
            files.update(p for p in d.rglob("*.lean") if ".lake" not in p.parts)
    return sorted(files)


def _allowed(rel: str, what: str, line: str) -> bool:
    return any(rel == f and what == w and rx.search(line) for f, w, rx in ALLOW)


def scan(lean_dir: Path) -> tuple[list[Path], list[str]]:
    """Return (files scanned, findings as 'ESCAPE <pattern> <file>:<line>')."""
    files = lean_files(lean_dir)
    root = lean_dir.parent
    bad: list[str] = []

    def report(f: Path, code: str, pats) -> None:
        rel = f.relative_to(lean_dir).as_posix()
        for ln, line in enumerate(code.splitlines(), 1):
            for what, pat in pats:
                if pat.search(line) and not _allowed(rel, what, line):
                    bad.append(f"ESCAPE {what} {f.relative_to(root).as_posix()}:{ln}")

    for f in files:
        code = strip(f.read_text(encoding="utf-8"))
        report(f, code, COMPILED)
        if f.name == "lakefile.lean" and f.parent == lean_dir:
            report(f, code, LAKEFILE_COMPILED)
    toml = lean_dir / "lakefile.toml"
    if toml.is_file():
        files.append(toml)
        report(toml, strip_toml(toml.read_text(encoding="utf-8")), LAKEFILE_COMPILED)
    return files, bad


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--lean-dir", default="lean", help="Lean project directory (repo-relative)")
    a = ap.parse_args(argv)
    lean_dir = Path(a.lean_dir)
    if not lean_dir.is_absolute():
        lean_dir = REPO / lean_dir
    lean_dir = lean_dir.resolve()
    if not lean_dir.is_dir():
        sys.stderr.write(f"lean-escape-hatch-check: ERROR: {lean_dir} is not a directory\n")
        return 1
    files, bad = scan(lean_dir)
    if not any(f.suffix == ".lean" for f in files):
        sys.stderr.write(f"lean-escape-hatch-check: ERROR: no Lean files under {lean_dir}\n")
        return 1
    if bad:
        print(f"lean-escape-hatch-check FAILED, {len(bad)} escape hatch(es) found:")
        for line in bad:
            print(line)
        return 1
    print(f"lean-escape-hatch-check ok: {len(files)} files, no escape hatches")
    return 0


if __name__ == "__main__":
    sys.exit(main())
