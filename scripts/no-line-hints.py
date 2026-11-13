#!/usr/bin/env python3
"""Fail if the Lean development or the spec cites code by line number.

A line number goes stale as soon as the code above it moves, and nothing checks it. Lean prose and
the spec name the item instead: the function, method, type, field or test. The Rust items the Lean
models describe are pinned by name and content hash in `lean/fidelity.toml`.

Scanned: every `.lean` file under `lean/`, `lean/README.md` and `spec/**/*.md`.
Usage: no-line-hints.py [paths...]   (no arguments: the default set)
"""
import re
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
EXT = r"(?:rs|java|ts|tsx|js|mjs|py|lean|kt)"
PATTERNS = [
    # file.rs:123, path/File.java:120-134, file.ts#L12
    re.compile(r"[\w./-]+\." + EXT + r"(?::|#L)\d+"),
    # file.rs line 12, file.rs, lines 10-20
    re.compile(r"[\w./-]+\." + EXT + r"`?,?\s+lines?\s+\d+", re.I),
    # line 12 of file.rs, lines 10-20 in File.java
    re.compile(r"\blines?\s+\d+(?:\s*[-–]\s*\d+)?\s+(?:of|in)\s+`?[\w./-]+\." + EXT + r"\b", re.I),
    # File.java 1077-1125, `executor.rs` 412, executor.rs (1084-1090)
    re.compile(r"[\w./-]+\." + EXT + r"`?,?\s+\(?\d+(?:\s*[-–]\s*\d+)?\b"),
    # a bare continuation hint after a file was named: `:123` or `:120-134`
    re.compile(r"`:\d+(?:[-–]\d+)?`"),
]


def default_paths() -> list[Path]:
    paths = sorted((REPO_ROOT / "lean").rglob("*.lean"))
    paths = [p for p in paths if ".lake" not in p.parts]
    paths.append(REPO_ROOT / "lean" / "README.md")
    paths += sorted((REPO_ROOT / "spec").rglob("*.md"))
    return paths


def scan(path: Path) -> list[str]:
    problems = []
    for n, line in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
        for rx in PATTERNS:
            m = rx.search(line)
            if m:
                rel = path.relative_to(REPO_ROOT) if path.is_relative_to(REPO_ROOT) else path
                problems.append(f"{rel}:{n}: line-number citation {m.group(0)!r}; name the item instead")
                break
    return problems


def main(argv: list[str]) -> int:
    paths = [Path(a).resolve() for a in argv] if argv else default_paths()
    problems = [p for path in paths for p in scan(path)]
    for p in problems:
        print(p)
    if problems:
        print(f"no-line-hints: {len(problems)} line-number citation(s)", file=sys.stderr)
        return 1
    print(f"no-line-hints: {len(paths)} file(s), no line-number citations")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
