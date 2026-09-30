#!/usr/bin/env python3
"""Replay every Violated trace a language's verifier reports on the Lean reference.

Rule 3 of spec/verification-fixtures/conformance/README.md: every `violated`
trace a language reports must replay under the reference firing rule. This
script runs a language's conformance suite with ``LIBPETRI_CONFORMANCE_DUMP`` set
(the suite writes ``<dump>/<id>.traces.json`` = ``[{"property": id, "trace":
[names]}]`` for every net with a Violated trace), then runs

    lake exe reference --replay nets/<id>.json <dump>/<id>.traces.json

on each dump and fails on any failed replay (the reference exits 1).

    scripts/conformance-replay.py --lang rust
    scripts/conformance-replay.py --lang ts --dump-dir /tmp/ts-dump --skip-tests   # replay an existing dump

Options:
  --lang rust|java|ts|py   which suite to run (required unless --skip-tests)
  --dump-dir DIR           where the suite dumps (default: a temporary directory)
  --skip-tests             do not run the suite; replay what is already in --dump-dir
  --test-cmd CMD           override the language's test command (run in its directory)
  --reference CMD          the reference command, run inside lean/ (default: the built
                           `reference` binary, else `lake exe reference`)
  --allow-empty            do not fail when the suite dumped no trace at all
  --jobs N                 parallel replays (default: CPU count)

The suite runs with ``LIBPETRI_CONFORMANCE_REQUIRE=1``, so a missing expected/
fails it instead of silently skipping, and an empty dump fails here: a green run
that replayed nothing is the failure this gate exists to stop.
"""

from __future__ import annotations

import argparse
import os
import shlex
import subprocess
import sys
import tempfile
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
NETS = REPO / "spec" / "verification-fixtures" / "conformance" / "nets"
LEAN = REPO / "lean"

# (working directory, command). Each suite reads LIBPETRI_CONFORMANCE_DUMP and
# LIBPETRI_CONFORMANCE_REQUIRE from the environment.
SUITES = {
    "rust": ("rust", "cargo test -p libpetri-verification --features z3 --test conformance -- --nocapture"),
    "java": ("java", "./mvnw -q test -Dtest=*Conformance*"),
    "ts": ("typescript", "npx vitest run conformance"),
    "py": ("python", "pytest -k conformance"),
}


def reference_command(given: str | None) -> list[str]:
    if given:
        return shlex.split(given)
    # `lake exe` re-checks the build on every call; build once, then call the binary.
    subprocess.run(["lake", "build", "reference"], cwd=LEAN, check=True)
    binary = LEAN / ".lake" / "build" / "bin" / "reference"
    return [str(binary)] if binary.exists() else ["lake", "exe", "reference"]


def replay(reference: list[str], dump: Path) -> tuple[str, bool, str]:
    net_id = dump.name[: -len(".traces.json")]
    net = NETS / f"{net_id}.json"
    if not net.exists():
        return net_id, False, f"no corpus net {net.relative_to(REPO)}"
    proc = subprocess.run(
        reference + ["--replay", str(net), str(dump)], cwd=LEAN, capture_output=True, text=True
    )
    return net_id, proc.returncode == 0, (proc.stdout + proc.stderr).strip()


def main(argv: list[str]) -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--lang", choices=sorted(SUITES))
    ap.add_argument("--dump-dir", type=Path)
    ap.add_argument("--skip-tests", action="store_true")
    ap.add_argument("--test-cmd")
    ap.add_argument("--reference")
    ap.add_argument("--allow-empty", action="store_true")
    ap.add_argument("--jobs", type=int, default=os.cpu_count() or 4)
    args = ap.parse_args(argv)
    if not args.skip_tests and not args.lang:
        ap.error("--lang is required unless --skip-tests")
    if args.skip_tests and not args.dump_dir:
        ap.error("--skip-tests needs --dump-dir")

    with tempfile.TemporaryDirectory(prefix="conformance-dump-") as tmp:
        dump_dir = (args.dump_dir or Path(tmp)).resolve()
        dump_dir.mkdir(parents=True, exist_ok=True)
        label = args.lang or "dump"
        if not args.skip_tests:
            for stale in dump_dir.glob("*.traces.json"):
                stale.unlink()
            workdir, cmd = SUITES[args.lang]
            cmd = args.test_cmd or cmd
            env = dict(os.environ, LIBPETRI_CONFORMANCE_DUMP=str(dump_dir), LIBPETRI_CONFORMANCE_REQUIRE="1")
            print(f"conformance-replay[{label}]: {cmd}  (in {workdir}/)", file=sys.stderr)
            proc = subprocess.run(cmd, shell=True, cwd=REPO / workdir, env=env)
            if proc.returncode != 0:
                print(f"conformance-replay[{label}]: the {args.lang} suite FAILED", file=sys.stderr)
                return proc.returncode or 1

        dumps = sorted(dump_dir.glob("*.traces.json"))
        if not dumps:
            msg = f"conformance-replay[{label}]: no *.traces.json under {dump_dir} — did the suite run?"
            print(msg, file=sys.stderr)
            return 0 if args.allow_empty else 1

        reference = reference_command(args.reference)
        with ThreadPoolExecutor(max_workers=max(1, args.jobs)) as pool:
            results = list(pool.map(lambda d: replay(reference, d), dumps))
        failed = [(i, out) for i, ok, out in results if not ok]
        for net_id, out in failed:
            print(f"--- {net_id}: REPLAY FAILED\n{out}", file=sys.stderr)
        if failed:
            print(f"conformance-replay[{label}]: {len(failed)} of {len(dumps)} net(s) have a trace "
                  "the reference does not replay (rule 3)", file=sys.stderr)
            return 1
        print(f"conformance-replay[{label}]: every Violated trace of {len(dumps)} net(s) replays on the reference")
        return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
