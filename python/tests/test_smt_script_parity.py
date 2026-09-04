"""Cross-language SMT script parity (VER-013 AC1).

For every fixture in ``spec/verification-fixtures/fixtures.json`` the scripts the
binding would send to z3 (``libpetri.encode_smt_scripts``) must equal the committed
goldens under ``spec/verification-fixtures/scripts/<id>/``, byte for byte. The
goldens are written by the Rust verifier (``scripts/smt-script-parity.py
--update``); the Java and TypeScript suites diff them too. A diff is a parity
FINDING in whichever emitter drifted, never a reason to edit a golden by hand.

No solver is needed: the encoders are pure text (the wheel must carry the SMT
surface, ``lp.HAS_Z3``).
"""

import json

import libpetri as lp
import pytest

from test_verdict_parity import FIXTURES, _net, _property

pytestmark = pytest.mark.skipif(not lp.HAS_Z3, reason="z3 feature not enabled")

SCRIPTS = FIXTURES.parent / "scripts"


def _first_difference(expected: str, actual: str) -> str:
    e = expected.split("\n")
    a = actual.split("\n")
    for i, (x, y) in enumerate(zip(e, a)):
        if x != y:
            return f"line {i + 1}:\n  golden: {x}\n  actual: {y}"
    return f"one text is a prefix of the other (golden {len(e)} lines, actual {len(a)} lines)"


def test_smt_scripts_match_the_committed_goldens():
    fixtures = json.loads(FIXTURES.read_text())["fixtures"]
    assert fixtures, "fixtures.json lists no fixtures"
    findings = []
    for fixture in fixtures:
        fid = fixture["id"]
        net, marking, env = _net(fixture["net"])
        scripts = lp.encode_smt_scripts(
            net,
            _property(fixture["property"]),
            initial_marking=marking,
            sink_places=fixture.get("sinkPlaces") or None,
            budget_places=fixture.get("budgetPlaces") or None,
            semiflow_invariants=bool(fixture.get("semiflowInvariants", False)),
            counterexample_replay=True,
            **env,
        )
        for name, actual in (("horn.smt2", scripts["horn"]), ("certificate.smt2", scripts["certificate"])):
            golden = SCRIPTS / fid / name
            if not golden.is_file():
                if actual is not None:
                    findings.append(
                        f"SCRIPT PARITY FINDING [{fid}]: this encoding emits {name} but no golden "
                        f"exists at {golden} (run scripts/smt-script-parity.py --update)"
                    )
                continue
            if actual is None:
                findings.append(f"SCRIPT PARITY FINDING [{fid}]: {golden} exists but this encoding emits no such script")
                continue
            expected = golden.read_text()
            if expected != actual:
                findings.append(
                    f"SCRIPT PARITY FINDING [{fid}]: {name} differs from the Rust golden at "
                    f"{_first_difference(expected, actual)} - report the divergence, never edit the golden by hand"
                )
    assert not findings, f"\n{len(findings)} script parity finding(s):\n\n" + "\n\n".join(findings)
