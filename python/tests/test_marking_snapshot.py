"""Marking snapshot / restore round-trips preserving Token.created_at."""

from __future__ import annotations

import asyncio
import re
import subprocess
import sys
import textwrap
import threading
import time

import pytest

import libpetri as lp

requires_tokio = pytest.mark.skipif(
    not lp.HAS_TOKIO, reason="ExecutorHandle.snapshot requires tokio"
)


def _build_forward_net() -> lp.BuiltNet:
    p_in = lp.Place("p_in")
    p_out = lp.Place("p_out")
    return (
        lp.Net("snapshot-net")
        .transition(
            lp.Transition("t")
            .input(lp.one(p_in))
            .output(lp.out(p_out))
            .action(lp.fork)
            .build()
        )
        .build()
    )


def test_run_sync_returns_structured_marking_with_timestamps() -> None:
    net = _build_forward_net()
    marking = lp.run_sync(net, initial={"p_in": ["hello"]})

    assert marking["p_out"] == ("hello",)
    timestamps = marking.timestamps("p_out")
    assert len(timestamps) == 1
    assert isinstance(timestamps[0], int)
    assert timestamps[0] > 0


def test_snapshot_roundtrip_preserves_token_timestamps() -> None:
    net = _build_forward_net()
    marking = lp.run_sync(net, initial={"p_in": ["one", "two"]})

    snapshot = marking.snapshot()
    restored = lp.MarkingView.from_snapshot(snapshot)

    assert restored.to_dict() == marking.to_dict()
    for place in marking.places():
        assert restored.timestamps(place) == marking.timestamps(place)


def test_passing_marking_view_as_initial_preserves_timestamps() -> None:
    net = _build_forward_net()
    marking = lp.run_sync(net, initial={"p_in": ["v"]})

    # Note when token entered the marking.
    [token_ts] = marking.timestamps("p_out")

    # Wait long enough that any reassignment to now() would be detectable.
    time.sleep(0.05)

    # Now restore via the structured form (passing the view itself).
    # In this run there are no inputs and no enabled transitions, so the
    # executor terminates with the same marking it started with.
    restored = lp.run_sync(net, initial=marking)

    [restored_ts] = restored.timestamps("p_out")
    assert restored_ts == token_ts, (
        "ExecutorHandle and Marking save/restore must preserve token "
        "created_at; got "
        f"{restored_ts} != {token_ts}"
    )


def test_legacy_value_only_init_still_works_and_stamps_now() -> None:
    net = _build_forward_net()
    before_ms = int(time.time() * 1000)
    marking = lp.run_sync(net, initial={"p_in": ["legacy"]})
    after_ms = int(time.time() * 1000) + 1

    [ts] = marking.timestamps("p_out")
    assert before_ms <= ts <= after_ms


def test_from_snapshot_accepts_explicit_structured_form() -> None:
    structured = {
        "p_out": [
            {"value": "alpha", "created_at": 1_000_000},
            {"value": "beta", "created_at": 2_000_000},
        ]
    }
    view = lp.MarkingView.from_snapshot(structured)
    assert view["p_out"] == ("alpha", "beta")
    assert view.timestamps("p_out") == (1_000_000, 2_000_000)


def test_constructor_auto_detects_structured_vs_legacy() -> None:
    legacy = lp.MarkingView({"p": [1, 2, 3]})
    assert legacy["p"] == (1, 2, 3)
    # legacy timestamps are filled with a single fallback `now`
    assert len(set(legacy.timestamps("p"))) == 1

    structured = lp.MarkingView(
        {"p": [{"value": 10, "created_at": 100}, {"value": 20, "created_at": 200}]}
    )
    assert structured["p"] == (10, 20)
    assert structured.timestamps("p") == (100, 200)


def test_snapshot_handles_empty_marking() -> None:
    empty = lp.MarkingView()
    assert empty.snapshot() == {}
    assert lp.MarkingView.from_snapshot({}).to_dict() == {}


@requires_tokio
@pytest.mark.asyncio
async def test_executor_handle_snapshot_returns_live_marking() -> None:
    # Net with an environment place — keeps the executor alive while we
    # request a mid-execution snapshot.
    p_env = lp.Place("p_env")
    p_seen = lp.Place("p_seen")
    net = (
        lp.Net("env-net")
        .transition(
            lp.Transition("forward")
            .input(lp.one(p_env))
            .output(lp.out(p_seen))
            .action(lp.fork)
            .build()
        )
        .build()
    )
    options = lp.ExecutorOptions(environment_places=(p_env,))

    handle, awaitable = lp.start_async(net, options=options)
    try:
        handle.inject(p_env, "ping")
        # Give the executor a moment to fire `forward`.
        await asyncio.sleep(0.05)
        mid = await handle.snapshot()
        # [ENV-014] AC5: the reply carries the marking AND whether anything
        # was in flight when it was taken, as one value.
        assert isinstance(mid, lp.SnapshotResult)
        assert mid.marking["p_seen"] == ("ping",)
        assert isinstance(mid.marking.timestamps("p_seen")[0], int)
        # `forward` uses a builtin action that completes inline, so by the
        # time the orchestrator serves the snapshot nothing is in flight.
        assert mid.action_in_flight is False
        assert mid.is_restore_point is True
    finally:
        handle.drain()
        await awaitable


@requires_tokio
@pytest.mark.asyncio
async def test_a_snapshot_taken_mid_action_is_flagged_and_is_not_a_restore_point() -> None:
    """[ENV-014] AC5/AC6 and its test derivation, observed from Python.

    Snapshot while an action is in flight (flag set, consumed input in neither
    place), release it, snapshot at quiescence (flag clear, output present),
    then restore that marking. The sibling test above only ever sees
    ``False``, so a binding that hard-coded the flag would pass it.

    The gate is a ``threading.Event`` behind `action_to_thread`: actions run
    on a Tokio thread with no running asyncio loop, so ``asyncio.Event`` /
    ``asyncio.sleep`` inside one fails. A second event marks *entry*, so the
    snapshot is never raced against a fixed sleep.
    """
    p_in, p_out, p_env = lp.Place("p_in"), lp.Place("p_out"), lp.Place("p_env")
    started, release = threading.Event(), threading.Event()

    def gate() -> None:
        started.set()
        release.wait(30)  # bounded: a failed assertion must not wedge the pool

    async def slow(ctx: lp.TransitionContext) -> None:
        value = ctx.input("p_in")
        await lp.action_to_thread(gate)
        ctx.output("p_out", value)

    net = (
        lp.Net("in-flight")
        .transition(
            lp.Transition("slow")
            .input(lp.one(p_in))
            .output(lp.out(p_out))
            .action(slow)
            .build()
        )
        # Keeps the executor alive after `slow` completes, so the quiescent
        # snapshot below is served by a live run rather than rejected.
        .transition(
            lp.Transition("sink_env").input(lp.one(p_env)).action(lp.passthrough).build()
        )
        .build()
    )
    handle, awaitable = lp.start_async(
        net,
        initial={p_in: [{"value": "work", "created_at": 42}]},
        options=lp.ExecutorOptions(environment_places=(p_env,)),
    )
    try:
        assert await asyncio.to_thread(started.wait, 10), "the action never started"

        mid = await handle.snapshot()
        assert mid.action_in_flight is True
        assert mid.is_restore_point is False
        # AC6: the consumed token is in *neither* place.
        assert mid.marking.to_dict() == {}, mid.marking

        release.set()
        quiet = await handle.snapshot()
        for _ in range(500):
            if not quiet.action_in_flight:
                break
            await asyncio.sleep(0.01)
            quiet = await handle.snapshot()
        assert quiet.action_in_flight is False
        assert quiet.is_restore_point is True
        assert quiet.marking["p_out"] == ("work",)
    finally:
        release.set()
        handle.drain()
        await awaitable

    # A restore point restores: values and order survive, nothing re-fires.
    restored = lp.run_sync(net, initial=quiet.marking)
    assert restored.snapshot() == quiet.marking.snapshot()
    assert list(restored.snapshot()) == ["p_out"]


@requires_tokio
@pytest.mark.asyncio
async def test_events_accepted_before_a_snapshot_are_already_in_its_marking() -> None:
    """[ENV-014] AC#7: a snapshot is not a restore point while an accepted external
    event is still un-injected. Implementations that queue accepted events fold
    "queue not empty" into the flag; here `inject` and `snapshot` share one
    FIFO channel into the Rust executor and an inject is applied on receipt,
    so there is nothing to flag — every event accepted before the request is
    already **in** the marking. No ``await`` between the injects and the
    request, so the executor has had no turn in which to catch up by luck.
    """
    inbox = lp.Place("inbox")
    net = lp.NetBuilder("idle").place(inbox).build()
    handle, awaitable = lp.start_async(
        net, options=lp.ExecutorOptions(environment_places=(inbox,))
    )
    try:
        for i in range(50):
            assert handle.inject(inbox, i)
        # The wrapper sends the request synchronously on its first step, so
        # it queues directly behind the 50 injects.
        result = await handle.snapshot()
        assert result.marking["inbox"] == tuple(range(50))
        assert result.is_restore_point is True
    finally:
        handle.close()
        await awaitable


@requires_tokio
@pytest.mark.asyncio
async def test_executor_handle_snapshot_rejected_after_close() -> None:
    p_env = lp.Place("p_env")
    net = (
        lp.Net("env-noop")
        .transition(
            lp.Transition("noop")
            .input(lp.one(p_env))
            .action(lp.passthrough)
            .build()
        )
        .build()
    )
    options = lp.ExecutorOptions(environment_places=(p_env,))
    handle, awaitable = lp.start_async(net, options=options)
    handle.close()
    await awaitable
    with pytest.raises(RuntimeError):
        await handle.snapshot()


def _handle_reaching_net(action) -> tuple[lp.BuiltNet, lp.Place, lp.Place, lp.Place]:
    """``work`` runs `action`; ``p_in`` is an environment place so the test can
    hand the action its `ExecutorHandle` *before* the firing starts (the handle
    only exists once `start_async` has returned)."""
    p_in, p_out, p_env = lp.Place("p_in"), lp.Place("p_out"), lp.Place("p_env")
    net = (
        lp.Net("snapshot-from-an-action")
        .transition(
            lp.Transition("work")
            .input(lp.one(p_in))
            .output(lp.out(p_out))
            .action(action)
            .build()
        )
        .transition(
            lp.Transition("sink_env").input(lp.one(p_env)).action(lp.passthrough).build()
        )
        .build()
    )
    return net, p_in, p_out, p_env


@requires_tokio
@pytest.mark.asyncio
async def test_a_snapshot_awaited_from_inside_an_action_returns_and_is_flagged() -> None:
    """[ENV-014] AC#8: `snapshot()` requested by a running action — from its
    first statement as well as after it has suspended — returns, and its
    result says it is not a restore point.

    Bounded by the call *returning* (`wait_for`), not by patience: the failure
    mode the AC names is a self-deadlock. An ``async def`` action is driven
    from a Tokio worker, not from the orchestrator, so it may await the reply;
    the firing that is running it has consumed ``p_in`` and deposited nothing,
    which is exactly what the flag reports.
    """
    box: dict[str, object] = {}
    done = threading.Event()

    async def work(ctx: lp.TransitionContext) -> None:
        try:
            # First statement: the synchronous prefix of the action.
            box["prefix"] = await box["handle"].snapshot()  # type: ignore[union-attr]
            value = ctx.input("p_in")
            await lp.action_to_thread(lambda: None)  # a real suspension
            box["suspended"] = await box["handle"].snapshot()  # type: ignore[union-attr]
            ctx.output("p_out", value)
        except BaseException as err:  # surfaced below, not swallowed by the net
            box["error"] = err
            raise
        finally:
            done.set()

    net, p_in, _p_out, p_env = _handle_reaching_net(work)
    handle, awaitable = lp.start_async(
        net, options=lp.ExecutorOptions(environment_places=(p_in, p_env))
    )
    try:
        box["handle"] = handle
        assert handle.inject(p_in, "work")
        assert await asyncio.wait_for(asyncio.to_thread(done.wait, 10), 15), (
            "AC#8: the action never came back from snapshot() — self-deadlock"
        )
        assert "error" not in box, f"AC#8: snapshot() from an action raised: {box['error']!r}"
        for when in ("prefix", "suspended"):
            result = box[when]
            assert isinstance(result, lp.SnapshotResult), when
            assert result.action_in_flight is True, f"AC#8 ({when}): the requesting firing is itself in flight"
            assert result.is_restore_point is False, when
            # Reason (1): consumed, not yet deposited — in neither place.
            assert result.marking.to_dict() == {}, (when, result.marking)

        # The run was not disturbed: the firing completes and deposits.
        quiet = await handle.snapshot()
        for _ in range(500):
            if not quiet.action_in_flight:
                break
            await asyncio.sleep(0.01)
            quiet = await handle.snapshot()
        assert quiet.is_restore_point is True
        assert quiet.marking["p_out"] == ("work",)
    finally:
        handle.drain()
        await asyncio.wait_for(awaitable, 10)


@requires_tokio
@pytest.mark.asyncio
async def test_a_snapshot_requested_by_an_inline_sync_action_is_served_only_after_it_returns() -> None:
    """[ENV-014] AC#8, the half that is a rule rather than a feature.

    A **sync** action under `start_async` runs inline in the orchestrator
    loop. Sending the request from it is safe; *blocking on the reply* from it
    is the self-deadlock the spec describes — the orchestrator is the caller.
    Pinned in bounded form: the action blocks for 200 ms and must time out,
    and the reply that arrives once it has returned describes the instant
    after the firing — output deposited, nothing in flight, no token missing
    from a result that calls itself a restore point.
    """
    import concurrent.futures

    box: dict[str, object] = {}

    def work(ctx: lp.TransitionContext) -> None:
        pending = asyncio.run_coroutine_threadsafe(
            box["handle"].snapshot(),  # type: ignore[union-attr]
            lp._libpetri.captured_event_loop(),
        )
        box["pending"] = pending
        try:
            pending.result(timeout=0.2)
            box["served_while_running"] = True
        except concurrent.futures.TimeoutError:
            box["served_while_running"] = False
        ctx.output("p_out", ctx.input("p_in"))

    net, p_in, _p_out, p_env = _handle_reaching_net(work)
    handle, awaitable = lp.start_async(
        net, options=lp.ExecutorOptions(environment_places=(p_in, p_env))
    )
    try:
        box["handle"] = handle
        assert handle.inject(p_in, "work")
        for _ in range(500):
            if "served_while_running" in box:
                break
            await asyncio.sleep(0.01)
        assert box.get("served_while_running") is False, (
            "a reply arrived while the inline action still held the orchestrator"
        )
        result = await asyncio.wait_for(
            asyncio.wrap_future(box["pending"]), 10  # type: ignore[arg-type]
        )
        assert result.is_restore_point is True
        assert result.marking.to_dict() == {"p_out": ["work"]}, result.marking
    finally:
        handle.drain()
        await asyncio.wait_for(awaitable, 10)


@pytest.mark.parametrize("in_flight", [False, True], ids=["restore-point", "mid-flight"])
def test_a_snapshot_result_is_not_an_initial_marking(in_flight: bool) -> None:
    """[CORE-073] / [ENV-014] AC#5: ``initial=`` takes a *marking*. Handing it
    the whole `SnapshotResult` skips the one check the result exists to force,
    so it is refused with an error that names both the fix and the check —
    never unwrapped silently, not even when the flag happens to be clear.
    """
    net = _build_forward_net()
    result = lp.SnapshotResult(
        marking=lp.MarkingView({"p_in": [{"value": 1, "created_at": 5}]}),
        action_in_flight=in_flight,
    )
    compiled = lp.compile(net)
    entry_points = {
        "run_sync": lambda: lp.run_sync(net, initial=result),
        "CompiledNet.run_sync": lambda: compiled.run_sync(initial=result),
        "MarkingView": lambda: lp.MarkingView(result),
        "MarkingView.from_snapshot": lambda: lp.MarkingView.from_snapshot(result),
    }
    if lp.HAS_TOKIO:
        entry_points["start_async"] = lambda: lp.start_async(net, initial=result)
        entry_points["CompiledNet.start_async"] = lambda: compiled.start_async(initial=result)
        entry_points["run_async"] = lambda: asyncio.run(lp.run_async(net, initial=result))
        entry_points["CompiledNet.run_async"] = lambda: asyncio.run(
            compiled.run_async(initial=result)
        )
    for name, call in entry_points.items():
        with pytest.raises(TypeError) as caught:
            call()
        message = str(caught.value)
        assert "SnapshotResult" in message, f"{name}: {message}"
        assert ".marking" in message, f"{name}: {message}"
        assert "is_restore_point" in message, f"{name}: {message}"

    # The pointed-to fix works.
    assert lp.run_sync(net, initial=result.marking)["p_out"] == (1,)


# ============================================================
#  CORE-073 AC#11 / AC#12 and NU-011 AC#3 on the binding
# ============================================================


def test_restore_is_unaffected_by_the_order_places_are_presented_in() -> None:
    """CORE-073 AC#12, **second half** — and this is where the real coverage is.

    Rust's snapshot type is a `BTreeMap`, so on that side a caller *cannot*
    present the places in another order and the property holds by
    construction. Python is different: `marking_from_python` accepts an
    arbitrary dict, and Python dicts are insertion-ordered, so an order
    dependency could genuinely live here and nowhere else.

    The first half (deterministic emission) is asserted too, in the
    discriminating form: the places are *inserted* in an order that is not
    sorted, so an implementation preserving insertion order would fail.
    """
    p_a, p_m, p_z = lp.Place("alpha"), lp.Place("mid"), lp.Place("zeta")
    net = lp.NetBuilder("N").place(p_a).place(p_m).place(p_z).build()

    # Deliberately unsorted insertion order.
    seeded = {
        p_z: [{"value": "z", "created_at": 30}],
        p_a: [{"value": "a", "created_at": 10}],
        p_m: [{"value": "m", "created_at": 20}],
    }
    snapshot = lp.run_sync(net, initial=seeded).snapshot()

    assert list(snapshot) == ["alpha", "mid", "zeta"], (
        f"AC#12 first half: emission is sorted, not insertion-ordered: {list(snapshot)}"
    )

    # Second half: the same snapshot presented in reverse must restore identically.
    reversed_snapshot = dict(reversed(list(snapshot.items())))
    assert list(reversed_snapshot) != list(snapshot), "the test must actually reorder"

    forward = lp.run_sync(net, initial=snapshot).snapshot()
    backward = lp.run_sync(net, initial=reversed_snapshot).snapshot()

    assert forward == backward, (
        "AC#12 second half: a restore must not depend on the order places are "
        f"presented in.\nforward:  {forward}\nbackward: {backward}"
    )
    # And the values/timestamps genuinely survived, so this is not two empties.
    assert forward["alpha"] == [{"value": "a", "created_at": 10}]
    assert forward["zeta"] == [{"value": "z", "created_at": 30}]


def test_there_is_exactly_one_marking_input() -> None:
    """CORE-073 AC#11: restore *plus* an explicit initial marking must not be
    merged or silently resolved.

    Python satisfies this structurally — `run_sync`/`run_async`/`start_async`
    each take a single `initial=`, and a restore is simply a snapshot passed
    as that argument. There is no second marking input to conflict with, so
    no combination can be constructed. This pins that property; if a
    restore-specific parameter is ever added, AC#11 stops being free.
    """
    import inspect

    for fn in (lp.run_sync, lp.start_async):
        params = inspect.signature(fn).parameters
        marking_params = [
            name
            for name in params
            if name in {"initial", "restore", "restored", "marking", "snapshot"}
        ]
        assert marking_params == ["initial"], (
            f"{fn.__name__} must take exactly one marking input, got {marking_params}"
        )


def test_pinned_execution_scope_reproduces_minted_names() -> None:
    """NU-011 AC#3 through the binding.

    Reachable from Python only because `ExecutorOptions` now carries
    `execution_scope`. Without it a Python host gets AC#1/#2/#4 (disjoint by
    default) but *not* AC#3 — and NU-011 is a MUST for any implementation
    supporting CORE-073 restore, which Python does.
    """
    src, sink = lp.Place("src"), lp.Place("sink")

    def run(scope: str | None) -> list[str]:
        seen: list[str] = []

        def act(ctx: lp.TransitionContext) -> None:
            seen.append(ctx.fresh_name())
            ctx.output("sink", ctx.input("src"))

        net = (
            lp.NetBuilder("mint")
            .transition(
                lp.Transition("fork")
                .input(lp.one(src))
                .output(lp.out(sink))
                .action(act)
                .build()
            )
            .build()
        )
        lp.run_sync(
            net,
            initial={src: ["a", "b"]},
            options=lp.ExecutorOptions(execution_scope=scope),
        )
        return seen

    pinned_a, pinned_b = run("seg1"), run("seg1")
    assert pinned_a == pinned_b == ["fork#seg1:0", "fork#seg1:1"], (
        f"AC#3: a fixed scope and firing order must reproduce the sequence: "
        f"{pinned_a} vs {pinned_b}"
    )


# `<transition>#<scope>:<n>` with the default scope: 32 lowercase hex chars.
_DEFAULT_SCOPE_NAME = re.compile(r"^(?P<t>.+)#(?P<scope>[0-9a-f]{32}):(?P<n>\d+)$")


def _mint_with(scope: str | None, transition: str = "fork", tokens: int = 2) -> list[str]:
    """Runs a one-transition net that mints one ν-name per firing."""
    src, sink = lp.Place("src"), lp.Place("sink")
    seen: list[str] = []

    def act(ctx: lp.TransitionContext) -> None:
        seen.append(ctx.fresh_name())
        ctx.output("sink", ctx.input("src"))

    net = (
        lp.NetBuilder("mint")
        .transition(
            lp.Transition(transition)
            .input(lp.one(src))
            .output(lp.out(sink))
            .action(act)
            .build()
        )
        .build()
    )
    lp.run_sync(
        net,
        initial={src: [str(i) for i in range(tokens)]},
        options=lp.ExecutorOptions(execution_scope=scope),
    )
    return seen


def test_the_default_scope_is_a_random_token_not_a_run_counter() -> None:
    """[NU-011] AC#5 (and AC#1/#4 by default), compared **structurally**.

    The default scope is 128 random bits rendered as exactly 32 lowercase hex
    characters — not the executor's run identifier, which is a per-process
    counter and therefore repeats in every process. (Python publishes no run
    identifier on any event, so AC#5's "not equal to it" clause has nothing to
    compare against here; the 32-hex shape already rules a counter out.)
    Nothing here depends on how many executors this process built before the
    test ran.
    """
    runs = [_mint_with(None), _mint_with(None)]
    scopes = []
    for names in runs:
        parsed = [m for n in names if (m := _DEFAULT_SCOPE_NAME.match(n))]
        assert len(parsed) == len(names) == 2, (
            f"default-scope names must be <t>#<32 hex>:<n>: {names}"
        )
        assert [m["t"] for m in parsed] == ["fork", "fork"]
        # `<n>` is a per-executor counter from 0; randomness is only in the scope.
        assert [int(m["n"]) for m in parsed] == [0, 1], names
        assert len({m["scope"] for m in parsed}) == 1, "one scope per execution"
        scopes.append(parsed[0]["scope"])
    assert scopes[0] != scopes[1], f"two executions shared a default scope: {scopes}"
    assert not set(runs[0]) & set(runs[1])


def test_the_first_executor_of_two_processes_mints_different_names() -> None:
    """[NU-011] AC#5 — AC#1 across processes, the case a durable snapshot
    actually hits: the resuming executor is the *first* one in its process.

    A per-process counter makes every process's first executor mint
    ``fork#0:0``, so a snapshot persisted by one process and restored as the
    first executor of the next re-mints a name that is live in the restored
    marking. Each child below is a fresh interpreter whose only executor is
    this one.
    """
    child = textwrap.dedent(
        """
        import libpetri as lp
        src, sink = lp.Place("src"), lp.Place("sink")
        seen = []
        def act(ctx):
            seen.append(ctx.fresh_name())
            ctx.output("sink", ctx.input("src"))
        net = (lp.NetBuilder("mint").transition(
            lp.Transition("fork").input(lp.one(src)).output(lp.out(sink)).action(act).build()
        ).build())
        lp.run_sync(net, initial={src: ["a"]})
        print(seen[0])
        """
    )

    def first_name() -> str:
        done = subprocess.run(
            [sys.executable, "-c", child], capture_output=True, text=True, timeout=60
        )
        assert done.returncode == 0, done.stderr
        return done.stdout.strip()

    a, b = first_name(), first_name()
    parsed_a, parsed_b = _DEFAULT_SCOPE_NAME.match(a), _DEFAULT_SCOPE_NAME.match(b)
    assert parsed_a and parsed_b, (a, b)
    assert a != b, f"two processes minted the same default-scope name: {a}"
    # "different for every executor": the difference is in the scope, not luck
    # in the counter — both are each process's first mint, so `<n>` is 0 twice.
    assert parsed_a["scope"] != parsed_b["scope"], (a, b)
    assert parsed_a["n"] == parsed_b["n"] == "0", (a, b)


_NATIVE_OPTIONS = lp._libpetri.ExecutorOptions


@pytest.mark.parametrize(
    "make", [lp.ExecutorOptions, _NATIVE_OPTIONS], ids=["wrapper", "native"]
)
@pytest.mark.parametrize(
    ("scope", "needle"),
    [
        ("", "must not be empty"),
        ("bad:scope", "must not contain ':'"),
        (":", "must not contain ':'"),
        ("bad#scope", "must not contain '#'"),
        ("#", "must not contain '#'"),
    ],
)
def test_an_invalid_execution_scope_is_a_value_error_in_both_layers(
    make, scope: str, needle: str
) -> None:
    """[NU-011] AC#6, scope validation — the same rule in all four implementations:
    reject a zero-length scope, any ``':'`` and any ``'#'``.

    Validated rather than escaped, so a minted ``<transition>#<scope>:<n>``
    parses uniquely whatever the transition is called: the last ``':'`` splits
    off the counter, then the last ``'#'`` before it splits off the scope.

    Both layers, because a host may build ``_libpetri.ExecutorOptions``
    directly — and an unvalidated scope reaching the engine is a Rust panic
    at run time, not an exception. Raised where the value is written, so the
    error points at the mistake.
    """
    with pytest.raises(ValueError, match=re.escape(needle)):
        make(execution_scope=scope)


def test_a_blank_or_non_ascii_execution_scope_is_accepted() -> None:
    """[NU-011] AC#6. The rule is *empty*, not *blank*: whitespace is a legal scope, and so is
    anything outside ASCII. Only the two separators are special."""
    assert _mint_with(" ", tokens=1) == ["fork# :0"]
    assert _mint_with("läuf-7", tokens=1) == ["fork#läuf-7:0"]
    assert _NATIVE_OPTIONS(execution_scope=" ").execution_scope == " "


def test_a_minted_name_parses_uniquely_under_a_hostile_transition_name() -> None:
    """[NU-011] AC#6, the parse rule. With ``'#'`` and ``':'`` banned from the
    scope, a transition name that contains both still yields a name with
    exactly one parse."""
    [name] = _mint_with("seg", transition="a#b:c", tokens=1)
    assert name == "a#b:c#seg:0"
    head, _, counter = name.rpartition(":")
    transition, _, scope = head.rpartition("#")
    assert (transition, scope, counter) == ("a#b:c", "seg", "0")


def test_a_place_name_is_an_arbitrary_string_and_none_is_reserved() -> None:
    """CORE-073: no place name is reserved.

    An implementation must not drop, rename or mangle an entry because its
    name collides with a construct of the host language or of the
    serialization it uses. TypeScript lost places named ``__proto__``
    entirely — assigning that key on a plain object sets the prototype
    instead of creating a key, so the place vanished and the marking
    serialized as ``{}``. Silent data loss, and reachable input: place names
    compile from user-supplied step identifiers.

    Python's exposure is different. Writing a name into a ``dict`` is safe —
    ``dict`` reserves nothing — so the risk is any path routing a name
    through ``setattr``, a dataclass field, ``__slots__`` or ``**kwargs``
    expansion. A sweep found none, and this pins the behaviour rather than
    the absence of those constructs.

    The names below are chosen to break something in each category: Python
    dunders, a JavaScript prototype key, strings that are not valid
    identifiers, and a Python keyword.
    """
    hostile = [
        "__proto__",      # sinks a plain JS object
        "__class__",      # attribute access
        "__dict__",
        "__slots__",
        "__init__",
        "constructor",
        "prototype",
        "2",              # not an identifier; JS orders integer-like keys first
        "class",          # Python keyword
        "a b",            # whitespace
        "",               # empty
        "has spaces and 'quotes'",
    ]
    places = {name: lp.Place(name) for name in hostile}

    builder = lp.NetBuilder("hostile")
    for place in places.values():
        builder = builder.place(place)
    net = builder.build()

    seeded = {places[n]: [{"value": n, "created_at": 7}] for n in hostile}
    snapshot = lp.run_sync(net, initial=seeded).snapshot()

    assert sorted(snapshot) == sorted(hostile), (
        "every place must survive; missing: "
        f"{sorted(set(hostile) - set(snapshot))}"
    )
    for name in hostile:
        assert snapshot[name] == [{"value": name, "created_at": 7}], (
            f"place {name!r} was mangled: {snapshot[name]}"
        )

    # And a full restore round-trip, since the restore path parses the dict
    # back out and is where a name could be lost on the way in.
    restored = lp.run_sync(net, initial=snapshot).snapshot()
    assert restored == snapshot, "hostile names must survive the round trip too"

    # The value-only projection is a separate code path — check it as well.
    view = lp.MarkingView.from_snapshot(snapshot)
    assert sorted(view.to_dict()) == sorted(hostile)
    for name in hostile:
        assert view.timestamps(name) == (7,)


def test_marking_snapshot_places_are_in_canonical_order() -> None:
    """CORE-073 canonical order, through the binding.

    Ascending code-point order, which is what distinguishes it from a
    case-insensitive or locale-aware collation: ``'A'`` (U+0041) sorts before
    ``'a'`` (U+0061). Seeded unsorted so an implementation preserving
    insertion order fails.
    """
    names = ["zeta", "Alpha", "alpha", "mid", "2", "_under"]
    places = {n: lp.Place(n) for n in names}
    builder = lp.NetBuilder("order")
    for place in places.values():
        builder = builder.place(place)
    net = builder.build()

    snapshot = lp.run_sync(
        net, initial={places[n]: [{"value": n, "created_at": 1}] for n in names}
    ).snapshot()

    assert list(snapshot) == sorted(names), (
        f"places must appear in ascending code-point order: {list(snapshot)}"
    )
    # `sorted()` on str is code-point order, so this pins the distinction
    # rather than assuming it.
    assert list(snapshot)[:3] == ["2", "Alpha", "_under"], list(snapshot)


def test_a_hand_built_view_snapshots_in_canonical_order() -> None:
    """CORE-073 AC#12 on the method the spec names as Python's snapshot form.

    Executor-produced views arrive sorted from Rust, which hid that
    `MarkingView.snapshot()` itself just replayed insertion order. A host that
    assembles, merges or migrates a marking in Python and persists
    ``view.snapshot()`` must get the same key order as every other host.

    ``list(...)`` throughout: dict equality ignores order.
    """
    names = ["zeta", "Alpha", "alpha", "\U00010000", "\uffff", "2", "_under"]
    view = lp.MarkingView({n: [{"value": n, "created_at": 1}] for n in names})

    assert list(view.snapshot()) == sorted(names)
    # Code-point order, not UTF-16 order: U+FFFF sorts before U+10000.
    assert list(view.snapshot())[-2:] == ["\uffff", "\U00010000"]
    assert list(lp.MarkingView.from_snapshot(view.snapshot()).snapshot()) == sorted(names)
    # The value-only projection is an ordered medium too.
    assert list(view.to_dict()) == sorted(names)
    # Copy-construction keeps it.
    assert list(lp.MarkingView(view).snapshot()) == sorted(names)


def test_an_emitted_snapshot_omits_empty_places_and_a_restore_accepts_them() -> None:
    """An emitted snapshot omits empty places; a restore takes both forms
    identically (the four-language ruling on CORE-073)."""
    view = lp.MarkingView({"b": [], "a": [{"value": 1, "created_at": 5}]})
    assert view.snapshot() == {"a": [{"value": 1, "created_at": 5}]}
    assert view.tokens("b") == ()

    net = lp.NetBuilder("N").place(lp.Place("a")).place(lp.Place("b")).build()
    with_empty = lp.run_sync(net, initial={"b": [], "a": [{"value": 1, "created_at": 5}]})
    without = lp.run_sync(net, initial={"a": [{"value": 1, "created_at": 5}]})
    assert with_empty.snapshot() == without.snapshot() == view.snapshot()
    assert list(with_empty.snapshot()) == ["a"]


class _IndexLike:
    """An integer type that is not `int` — what numpy scalars look like."""

    def __init__(self, value: int) -> None:
        self._value = value

    def __index__(self) -> int:
        return self._value


def _via_view(created_at: object) -> int:
    view = lp.MarkingView({"p": [{"value": "v", "created_at": created_at}]})
    return view.timestamps("p")[0]


def _via_engine(created_at: object) -> int:
    net = lp.NetBuilder("N").place(lp.Place("p")).build()
    marking = lp.run_sync(net, initial={"p": [{"value": "v", "created_at": created_at}]})
    return marking.timestamps("p")[0]


_CREATED_AT_ROUTES = pytest.mark.parametrize(
    "route", [_via_view, _via_engine], ids=["MarkingView", "engine"]
)


@_CREATED_AT_ROUTES
@pytest.mark.parametrize(
    ("raw", "expected"),
    [
        (0, 0),
        (2**64 - 1, 2**64 - 1),
        (_IndexLike(7), 7),
        # JSON pipelines hand back integral floats; the value is not altered.
        (1_700_000_000_000.0, 1_700_000_000_000),
    ],
    ids=["zero", "u64-max", "index-like", "integral-float"],
)
def test_a_valid_created_at_means_the_same_through_both_layers(route, raw, expected) -> None:
    assert route(raw) == expected


@_CREATED_AT_ROUTES
@pytest.mark.parametrize(
    ("raw", "error"),
    [
        (1.5, ValueError),           # was silently truncated to 1 by the view
        (float("nan"), ValueError),
        (float("inf"), ValueError),
        (-1, ValueError),            # was accepted by the view
        (2**64, ValueError),         # likewise
        ("3", TypeError),            # was parsed to 3 by the view
        (None, TypeError),
        (True, TypeError),
    ],
    ids=["fraction", "nan", "inf", "negative", "overflow", "str", "none", "bool"],
)
def test_an_invalid_created_at_is_rejected_the_same_through_both_layers(
    route, raw, error
) -> None:
    """[CORE-073] AC#9: a snapshot's `created_at` is never altered on the way
    in. `MarkingView` used to run it through ``int()``, so a fractional value
    was truncated, a numeric string parsed, and a negative or oversized int
    accepted — each failing only later, inside the engine, with a message
    saying an int "must be an int". The same dict now means the same thing
    whether or not it passes through a view first."""
    with pytest.raises(error, match="created_at"):
        route(raw)


def test_binding_docstrings_describe_the_members_they_sit_on() -> None:
    """``help()`` is documentation too. A getter inserted between a doc comment
    and its fn once moved the deadline text onto `execution_scope` and left
    `deadline_tolerance_ms` undocumented; `snapshot` described a payload it no
    longer returns."""
    ext = lp._libpetri
    deadline_doc = ext.ExecutorOptions.deadline_tolerance_ms.__doc__ or ""
    scope_doc = ext.ExecutorOptions.execution_scope.__doc__ or ""
    assert deadline_doc.startswith("Deadline-enforcement tolerance"), deadline_doc
    assert "Deadline" not in scope_doc and "NU-011" in scope_doc, scope_doc
    assert "run identifier" not in scope_doc, "the default scope is a random token"

    if lp.HAS_TOKIO:
        native_doc = ext.ExecutorHandle.snapshot.__doc__ or ""
        assert "action_in_flight" in native_doc and '"marking"' in native_doc, native_doc
        first_paragraph = (lp.ExecutorHandle.snapshot.__doc__ or "").split("\n\n")[1]
        assert "SnapshotResult" in first_paragraph, first_paragraph
