"""VER-013: cancelling a running verification with ``libpetri.CancelToken``.

The verification runs with the GIL released, so ``cancel()`` from another thread
-- or from an asyncio task while the call runs in an executor -- reaches it. The
call returns ``unknown`` with ``verification cancelled during <phase>``. The
net here is an unbounded producer whose enumeration never closes, so without a
cancellation the call would run until its class budget; it needs no solver.
"""

import asyncio
import threading
import time

import libpetri as lp
import pytest

pytestmark = pytest.mark.skipif(not lp.HAS_Z3, reason="z3 feature not enabled")

ENUMERATION = "verification cancelled during state-space enumeration"


def _producer():
    """``gen: G -> G, A`` with one token on ``G``: a graph that never closes."""
    g = lp.Place("G")
    a = lp.Place("A")
    return (
        lp.Net("gen")
        .transition(lp.Transition("gen").input(lp.one(g)).output(lp.and_(g, a)).action(lp.fork).build())
        .build()
    )


def _verify(token, cache=None):
    return lp.verify(
        _producer(),
        lp.place_bound("A", 10**12),
        initial_marking={"G": 1},
        enumeration_max_classes=10**15,
        state_space_cache=cache,
        cancel=token,
    )


def test_a_token_cancelled_before_the_call_returns_at_once():
    token = lp.CancelToken()
    token.cancel()
    assert token.is_cancelled()
    result = _verify(token)
    assert result.verdict == "unknown"
    assert result.reason == "verification cancelled during net preparation"
    assert "UNKNOWN: verification cancelled during net preparation" in result.report


def test_cancel_from_another_thread():
    token = lp.CancelToken()
    cache = lp.StateSpaceCache()
    timer = threading.Timer(0.3, token.cancel)
    timer.start()
    started = time.monotonic()
    result = _verify(token, cache)
    timer.join()
    assert result.verdict == "unknown", result.report
    assert result.reason == ENUMERATION
    assert time.monotonic() - started < 30
    assert len(cache) == 0, "a cancelled build is not a truncation"


def test_cancel_from_an_asyncio_task():
    async def main():
        token = lp.CancelToken()
        loop = asyncio.get_running_loop()
        running = loop.run_in_executor(None, _verify, token)

        async def canceller():
            await asyncio.sleep(0.3)
            token.cancel()

        _, result = await asyncio.gather(canceller(), running)
        return result

    result = asyncio.run(main())
    assert result.verdict == "unknown", result.report
    assert result.reason == ENUMERATION


def test_verify_subnet_honours_the_token():
    token = lp.CancelToken()
    token.cancel()
    inp = lp.Place("in")
    out = lp.Place("out")
    subnet = (
        lp.SubnetDef("Forward")
        .transition(lp.Transition("forward").input(lp.one(inp)).output(lp.out(out)).action(lp.fork).build())
        .input_port("in", inp)
        .output_port("out", out)
        .build()
    )
    harness = lp.VerificationHarness().input("in", lambda: "x").property(lp.place_bound("harness_out_out", 1))
    result = lp.verify_subnet(subnet, harness, cancel=token).property_results()[0].result
    assert result.verdict == "unknown"
    assert result.reason == "verification cancelled during net preparation"


def test_verify_open_net_honours_the_token():
    """VER-013 through ``verify_open_net``: a cancelled token leaves every part it
    reaches undecided, so the gadget ``test_open_net`` proves comes back unknown."""
    from test_open_net import _contract, _gadget

    assert lp.verify_open_net(_gadget(), _contract()).verdict == "proven"
    token = lp.CancelToken()
    token.cancel()
    result = lp.verify_open_net(_gadget(), _contract(), cancel=token)
    assert result.verdict == "unknown", result.report
    assert "verification cancelled during" in result.report


def test_the_token_and_the_result_keep_their_own_docstrings():
    """The binding's doc comments attach to the item that follows them: the token
    must not take over ``VerificationResult``'s docstring and leave it without one."""
    assert lp.CancelToken.__doc__.startswith("Cancels a running verification")
    assert lp.VerificationResult.__doc__.startswith("Outcome of an SMT verification run")
