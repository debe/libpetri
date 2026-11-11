#!/usr/bin/env python3
"""Situation replays (spec/situations/README.md), written by the verified Lean reference.

A situation is a corpus-schema net plus a list of steps. The Lean reference
(``lake exe reference situations``, lean/Libpetri/Reference/Situation.lean)
replays the steps on the reference firing rule and writes, per situation, the
marking after each fired step and the reason the first blocked step cannot
fire. The expected files are written by the Lean binary, never by hand.

    scripts/situations.py --update   replay every situation into spec/situations/expected/
    scripts/situations.py --check    fail if spec/situations/expected/ is stale
                                     (re-derived by the Lean binary into a temp dir)

Options: ``--reference CMD`` (the reference command, default ``lake exe reference``
run inside lean/).

A situation with ``"replay": false`` gets no expected file. The ``reference``
field of an expected file (the hash of the reference's sources) is ignored by
--check, as conformance-corpus.py ignores it, so editing any reference module
does not make the replays stale while their content is unchanged.
"""

from __future__ import annotations

import argparse
import json
import shlex
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
SITUATIONS = REPO / "spec" / "situations"
EXPECTED = SITUATIONS / "expected"
LEAN = REPO / "lean"


def replayable() -> list[str]:
    """Slugs of the situations the reference replays (``replay`` absent or true)."""
    slugs = []
    for path in sorted(SITUATIONS.glob("*.json")):
        try:
            doc = json.loads(path.read_text())
        except json.JSONDecodeError as e:
            sys.exit(f"situations: {path.relative_to(REPO)}: {e}")
        if not isinstance(doc, dict):
            sys.exit(f"situations: {path.relative_to(REPO)}: a situation must be an object")
        if doc.get("replay", True) is not False:
            slugs.append(path.stem)
    return slugs


def run_reference(reference: list[str], out_dir: Path) -> None:
    cmd = reference + ["situations", str(SITUATIONS), str(out_dir)]
    print("situations: " + " ".join(shlex.quote(c) for c in cmd), file=sys.stderr)
    proc = subprocess.run(cmd, cwd=LEAN)
    if proc.returncode != 0:
        sys.exit(f"situations: the reference failed (exit {proc.returncode})")


def without_reference(text: str):
    doc = json.loads(text)
    doc.pop("reference", None)
    return doc


def main(argv: list[str]) -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    mode = ap.add_mutually_exclusive_group(required=True)
    mode.add_argument("--update", action="store_true", help="rewrite spec/situations/expected/ with the Lean reference")
    mode.add_argument("--check", action="store_true", help="fail when spec/situations/expected/ is stale")
    ap.add_argument("--reference", default="lake exe reference",
                    help="reference command, run inside lean/ (default: %(default)s)")
    args = ap.parse_args(argv)
    reference = shlex.split(args.reference)
    slugs = replayable()

    with tempfile.TemporaryDirectory() as tmp:
        fresh = Path(tmp) / "expected"
        fresh.mkdir()
        run_reference(reference, fresh)
        want = {p.name: p.read_text() for p in fresh.glob("*.json")}
        missing = sorted(f"{s}.json" for s in slugs if f"{s}.json" not in want)
        if missing:
            sys.exit(f"situations: the reference wrote no replay for {missing}")

        if args.update:
            if EXPECTED.exists():
                shutil.rmtree(EXPECTED)
            shutil.copytree(fresh, EXPECTED)
            print(f"situations: wrote {len(want)} replays to {EXPECTED.relative_to(REPO)}")
            return 0

        have = {p.name: p.read_text() for p in EXPECTED.glob("*.json")} if EXPECTED.exists() else {}
        problems = []
        for name in sorted(set(want) | set(have)):
            if name not in have:
                problems.append(f"expected/{name} missing")
            elif name not in want:
                problems.append(f"expected/{name} is not produced by the reference")
            elif without_reference(have[name]) != without_reference(want[name]):
                problems.append(f"expected/{name} differs from the reference's output")
        for p in problems:
            print("  " + p, file=sys.stderr)
        if problems:
            print(f"situations: STALE ({len(problems)} problem(s)); run scripts/situations.py --update",
                  file=sys.stderr)
            return 1
        print(f"situations: {len(want)} replays are current")
        return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
