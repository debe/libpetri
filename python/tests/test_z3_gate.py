"""CI gate for the z3 back-end (the Python analogue of Rust's ``tests/z3_gate.rs``).

Every SMT-backed test in this suite skips itself when the wheel was built without
the ``z3`` feature or when no usable ``z3`` executable resolves, so the binding
can ship unverified because the checks did not run. Locally that skip is a
legitimate choice; on a CI runner (``CI`` set) it is a red build.
"""

import os

import libpetri as lp
import pytest


def test_z3_backed_suites_must_actually_run_in_ci():
    skipped = []
    if not lp.HAS_Z3:
        skipped.append(
            "the wheel was built without the z3 feature, so test_verdict_parity.py, "
            "test_smt_verification.py and test_nu_verification.py skipped themselves"
        )
    elif not lp.z3_available():
        skipped.append(
            "no usable z3 executable resolves (PATH or LIBPETRI_Z3, >= 4.8.0), so the "
            "verdict-parity runner, the certificate check and the counterexample replay "
            "skipped themselves"
        )
    if not skipped:
        return
    if os.environ.get("CI") is None:
        pytest.skip("z3-backed verification suites did not run: " + "; ".join(skipped))
    pytest.fail(
        "the z3-backed verification suites did not run on a CI runner, so the SMT "
        "verifier is unverified in this build:\n  - "
        + "\n  - ".join(skipped)
        + "\nFix the runner rather than relaxing this assertion."
    )
