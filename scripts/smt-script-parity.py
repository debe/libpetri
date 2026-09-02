#!/usr/bin/env python3
"""Cross-language SMT script parity (VER-013 AC1).

The scripts every implementation sends to z3 for the shared verdict-parity
fixtures are pinned under ``spec/verification-fixtures/scripts/<id>/``. The Rust
verifier writes them; every language's script-parity test diffs its own output
against them byte for byte.

    scripts/smt-script-parity.py --update   regenerate the goldens from Rust
    scripts/smt-script-parity.py --check    (default) fail when Rust's output drifts

``--check`` is what ``cargo test --workspace --all-features`` already runs in CI
(``rust/libpetri-verification/tests/smt_script_parity.rs``); the Java, TypeScript
and Python suites carry the same comparison. A diff is a parity finding in
whichever emitter drifted, never a reason to edit a golden by hand.
"""

import os
import subprocess
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
RUST = REPO / "rust"


def main(argv: list[str]) -> int:
    update = "--update" in argv
    if any(a not in ("--update", "--check") for a in argv):
        print(__doc__)
        return 2
    env = dict(os.environ)
    if update:
        env["LIBPETRI_SMT_SCRIPT_UPDATE"] = "1"
    cmd = [
        "cargo", "test", "-p", "libpetri-verification", "--all-features",
        "--test", "smt_script_parity", "--", "--nocapture",
    ]
    proc = subprocess.run(cmd, cwd=RUST, env=env)
    if proc.returncode != 0:
        print("smt-script-parity: FAILED", file=sys.stderr)
        return proc.returncode
    print("smt-script-parity: " + ("goldens regenerated" if update else "goldens are current"))
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
