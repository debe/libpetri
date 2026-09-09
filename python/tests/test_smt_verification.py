"""VER-006: SMT verification environment-injection soundness.

Regression for the bug where ``verify`` vacuously reported safety bounds as
``proven`` on nets with environment places (env columns could only be consumed,
never produced, so the reachable set froze at the initial marking). The core fix
lives in the Rust verifier; here we exercise it through the Python binding and the
newly exposed ``environment_mode`` selector.

Gated on ``lp.HAS_Z3`` — the SMT path requires the wheel built with the ``z3``
feature (pyproject's maturin config enables ``full`` which includes it).
"""

import libpetri as lp
import pytest

pytestmark = pytest.mark.skipif(not lp.HAS_Z3, reason="z3 feature not enabled")


def _env_source_net():
    """env IN -> T -> OUT."""
    in_p = lp.Place("IN")
    out = lp.Place("OUT")
    net = (
        lp.Net("env-source")
        .transition(
            lp.Transition("T").input(lp.one(in_p)).output(lp.out(out)).action(lp.fork).build()
        )
        .build()
    )
    return in_p, out, net


@pytest.mark.parametrize("k", [0, 1, 5])
def test_always_available_injects_place_bound_violated(k):
    # AlwaysAvailable lets IN be injected without bound, so OUT grows without
    # bound: place_bound(OUT, k) is violated for every finite k.
    _in, out, net = _env_source_net()
    result = lp.verify(
        net,
        lp.place_bound(out, k),
        environment_places=["IN"],
        environment_mode=lp.always_available(),
        timeout_ms=15_000,
    )
    assert result.verdict == "violated", result.report


def test_bounded_gates_by_multiplicity():
    # T2 needs EXACTLY 2 tokens from env IN per firing. bounded(1) starves it
    # (OUT stays 0 -> proven); always_available feeds it (OUT unbounded -> violated).
    # Also exercises the env-aware P-invariant: the closed-net law IN + 2*OUT = 0
    # must be discarded so OUT is not vacuously pinned.
    def build():
        in_p = lp.Place("IN")
        out = lp.Place("OUT")
        return out, (
            lp.Net("env-mult")
            .transition(
                lp.Transition("T2")
                .input(lp.exactly(2, in_p))
                .output(lp.out(out))
                .action(lp.fork)
                .build()
            )
            .build()
        )

    out, net = build()
    bounded1 = lp.verify(
        net,
        lp.place_bound(out, 0),
        environment_places=["IN"],
        environment_mode=lp.bounded(1),
        timeout_ms=15_000,
    )
    assert bounded1.verdict == "proven", bounded1.report

    out, net = build()
    always = lp.verify(
        net,
        lp.place_bound(out, 0),
        environment_places=["IN"],
        environment_mode=lp.always_available(),
        timeout_ms=15_000,
    )
    assert always.verdict == "violated", always.report


def test_ignore_mode_with_env_places_downgrades_to_unknown():
    # Ignore mode does not model injection; a "proven" here would be vacuous,
    # so VER-006 refuses to certify it. The default models injection instead,
    # and answers the question: an inexhaustible IN drives OUT past the bound.
    _in, out, net = _env_source_net()

    explicit = lp.verify(
        net,
        lp.place_bound(out, 1),
        environment_places=["IN"],
        environment_mode=lp.ignore(),
        timeout_ms=15_000,
    )
    assert explicit.verdict == "unknown", explicit.report

    default = lp.verify(
        net,
        lp.place_bound(out, 1),
        environment_places=["IN"],
        timeout_ms=15_000,
    )
    assert default.verdict == "violated", default.report


def test_control_closed_net_place_bound_stays_sound():
    # The defect is env-specific: closed-net place_bound must stay sound.
    a = lp.Place("A")
    b = lp.Place("B")
    net = (
        lp.Net("closed-cycle")
        .transition(lp.Transition("AtoB").input(lp.one(a)).output(lp.out(b)).action(lp.fork).build())
        .transition(lp.Transition("BtoA").input(lp.one(b)).output(lp.out(a)).action(lp.fork).build())
        .build()
    )

    # Note: verify() defaults the initial marking to empty; place_bound on an
    # all-empty closed net is trivially proven, which is still a sound result.
    # Explicit VER-017 opt-out: the enumeration route would close this two-class
    # graph first and the env-specific encoder path this control guards would
    # never run.
    safe = lp.verify(
        net, lp.place_bound(b, 1), enumeration_max_classes=0, timeout_ms=15_000
    )
    assert safe.verdict == "proven", safe.report


def _conserved_pair():
    """p0(3) -> p1: conservation p0 + p1 = 3, so place_bound(p1, 3) is proven."""
    p0 = lp.Place("p0")
    p1 = lp.Place("p1")
    net = (
        lp.Net("conservedPair")
        .transition(lp.Transition("t").input(lp.one(p0)).output(lp.out(p1)).action(lp.fork).build())
        .build()
    )
    return p0, p1, net


def test_certificate_check_kwarg_toggles_the_second_solver_run():
    # Default on: the proof is re-verified against the unstrengthened step
    # relation and the report says so. Off: the check is skipped, and says why.
    # Two explicit opt-outs keep the query on the IC3 path this test is about,
    # neither of which weakens it: `linear_bound=False` because a conservation
    # bound is exactly what the VER-015 phase proves structurally before any
    # fixpoint query, and `enumeration_max_classes=0` because the VER-017 route
    # would close this four-class graph first — a structural or enumerated proof
    # has no certificate to check.
    _p0, p1, net = _conserved_pair()
    on = lp.verify(
        net,
        lp.place_bound(p1, 3),
        initial_marking={"p0": 3},
        linear_bound=False,
        enumeration_max_classes=0,
        timeout_ms=15_000,
    )
    assert on.verdict == "proven", on.report
    assert "  Certificate check: PASSED (init, consecution, safety)" in on.report

    off = lp.verify(
        net,
        lp.place_bound(p1, 3),
        initial_marking={"p0": 3},
        linear_bound=False,
        enumeration_max_classes=0,
        certificate_check=False,
        timeout_ms=15_000,
    )
    assert off.verdict == "proven", off.report
    assert "  Certificate check: not applicable (disabled)" in off.report


def test_ver006_ignore_mode_on_route_b_does_not_silently_prove():
    """VER-006 binds Route B too. An unbudgeted nu-net takes the name-partition
    state-class graph, which returns its verdict without passing the solver path's
    vacuity guard; under ignore() the graph treats the environment place as an ordinary
    empty one, so ``accepted`` is unreachable and the bound holds for a reason that says
    nothing about the real system."""
    in_p = lp.Place("IN")
    a, b, accepted = lp.Place("branchA"), lp.Place("branchB"), lp.Place("accepted")

    net = (
        lp.Net("nu_env_route_b")
        .transition(
            lp.Transition("fork")
            .input(lp.one(in_p))
            .output(lp.and_(a, b))
            .action(lp.fork)
            .build()
        )
        .transition(
            # A match transition with no declared budget place: has_match and not
            # nu_bounded, which is exactly Route B's trigger.
            lp.Transition("join")
            .input(lp.one(a))
            .input(lp.one(b))
            .match_spec(lp.match_spec([(a, lambda m: m), (b, lambda m: m)]))
            .output(lp.out(accepted))
            .action(lp.fork)
            .build()
        )
        .build()
    )

    result = lp.verify(
        net,
        lp.place_bound(accepted, 0),
        environment_places=["IN"],
        environment_mode=lp.ignore(),
        timeout_ms=15_000,
    )
    assert result.verdict == "unknown", result.report


def _semiflow_loop():
    """VER-007 test derivation: a budgeted work loop with one reset arc on a side
    place. Open: one(Budget), reset(Stamp) -> and(Work, Stamp); Step: one(Work) ->
    Done; Close: one(Done) -> and(Budget, Sink). The semiflow enumeration finds
    Budget + Work + Done = 1 with zero weight on the reset place."""
    budget, work, done = lp.Place("Budget"), lp.Place("Work"), lp.Place("Done")
    stamp, sink = lp.Place("Stamp"), lp.Place("Sink")
    net = (
        lp.Net("loop")
        .transition(
            lp.Transition("Open")
            .input(lp.one(budget))
            .reset(lp.reset(stamp))
            .output(lp.and_(lp.out(work), lp.out(stamp)))
            .action(lp.fork)
            .build()
        )
        .transition(
            lp.Transition("Step").input(lp.one(work)).output(lp.out(done)).action(lp.fork).build()
        )
        .transition(
            lp.Transition("Close")
            .input(lp.one(done))
            .output(lp.and_(lp.out(budget), lp.out(sink)))
            .action(lp.fork)
            .build()
        )
        .build()
    )
    return work, sink, net


def _coloured_loop():
    """The scatter-gather ν-net (which puts the verifier on the name-coloured encoder)
    alongside the reset-bearing loop above (which is what makes the null-space basis
    deficient). The two halves share no places; the loop is there purely so the
    semiflow enumeration has a law to contribute.

    The reset arc has to sit on the uncoloured half: the coloured encoder rejects any
    transition whose reset or consume-all set touches a coloured place, and the plan is
    then refused and the verifier falls back silently to the flat encoding — which would
    make the test pass for the wrong reason. That is what the ``coloured`` assertions
    guard.
    """
    source, budget, pending = lp.Place("source"), lp.Place("budget"), lp.Place("pending")
    a, b, merged = lp.Place("branchA"), lp.Place("branchB"), lp.Place("merged")
    loop_budget, work, done = lp.Place("loopBudget"), lp.Place("Work"), lp.Place("Done")
    stamp, sink = lp.Place("Stamp"), lp.Place("Sink")

    net = (
        lp.Net("coloured_loop")
        .transition(
            lp.Transition("fork")
            .input(lp.one(source))
            .input(lp.one(budget))
            .output(lp.and_(a, b, pending))
            .action(lp.fork)
            .build()
        )
        .transition(
            lp.Transition("join")
            .input(lp.one(a))
            .input(lp.one(b))
            .input(lp.one(pending))
            .match_spec(lp.match_spec([(a, lambda m: m), (b, lambda m: m)]))
            .output(lp.and_(merged, budget))
            .action(lp.fork)
            .build()
        )
        .transition(
            lp.Transition("Open")
            .input(lp.one(loop_budget))
            .reset(lp.reset(stamp))
            .output(lp.and_(lp.out(work), lp.out(stamp)))
            .action(lp.fork)
            .build()
        )
        .transition(
            lp.Transition("Step").input(lp.one(work)).output(lp.out(done)).action(lp.fork).build()
        )
        .transition(
            lp.Transition("Close")
            .input(lp.one(done))
            .output(lp.and_(lp.out(loop_budget), lp.out(sink)))
            .action(lp.fork)
            .build()
        )
        .build()
    )
    return pending, net


def _coloured_scripts(net, pending, semiflows):
    return lp.encode_smt_scripts(
        net,
        lp.branch_place_bound(pending, 2),
        initial_marking={"source": 3, "budget": 2, "loopBudget": 1},
        budget_places=["budget"],
        semiflow_invariants=semiflows,
    )


def test_semiflows_reach_the_coloured_encoder():
    """VER-007: the strengthened list reaches the *name-coloured* encoder, not only the
    flat one. Solver-free — ``encode_smt_scripts`` returns the script a verification
    would send.

    This is the case that catches the coloured encoder being handed the semiflows where
    it wants the strengthened invariants: they are separate lists, and every other test
    is blind to the swap.
    """
    pending, net = _coloured_loop()
    off = _coloured_scripts(net, pending, False)
    on = _coloured_scripts(net, pending, True)

    assert off["coloured"], "fixture must take the name-coloured path, not fall back to flat"
    assert on["coloured"], "fixture must take the name-coloured path, not fall back to flat"
    assert off["horn"] != on["horn"], (
        "the semiflows must change the coloured HORN script when the option is on"
    )


def test_semiflow_invariants_kwarg_adds_the_report_line():
    # VER-007 AC2/AC3: off by default (no report line); on, the minimal laws reach
    # the encoder, the report says how many, and the loop's bound is proven.
    work, _sink, net = _semiflow_loop()
    # Explicit VER-017 opt-out on both calls: the report lines under test are
    # Phase-3 lines of the SMT pipeline. `Sink` grows without bound so the graph
    # never closes and the route would truncate to the same pipeline anyway —
    # after enumerating 50 000 classes for nothing.
    off = lp.verify(
        net,
        lp.place_bound(work, 1),
        initial_marking={"Budget": 1},
        enumeration_max_classes=0,
        timeout_ms=30_000,
    )
    assert "Semiflows encoded as invariants" not in off.report, off.report

    on = lp.verify(
        net,
        lp.place_bound(work, 1),
        initial_marking={"Budget": 1},
        semiflow_invariants=True,
        enumeration_max_classes=0,
        timeout_ms=30_000,
    )
    assert on.verdict == "proven", on.report
    assert "  Semiflows encoded as invariants: " in on.report, on.report
    assert any(
        line.startswith("  I") and "Budget" in line and "Work" in line and "Done" in line
        and line.endswith("= 1")
        for line in on.report.splitlines()
    ), on.report


def test_semiflow_invariants_never_hide_a_counterexample():
    # VER-007 AC5: Sink gains one token per loop iteration, so bound 1 is violated.
    _work, sink, net = _semiflow_loop()
    result = lp.verify(
        net,
        lp.place_bound(sink, 1),
        initial_marking={"Budget": 1},
        semiflow_invariants=True,
        # Explicit VER-017 opt-out, as above: the encoders are what must not hide
        # the counterexample, and this graph does not close.
        enumeration_max_classes=0,
        timeout_ms=30_000,
    )
    assert result.verdict == "violated", result.report


def test_counterexample_confirmed_is_a_tri_state():
    # Explicit VER-017 opt-out throughout: this is about the abstract REPLAY, and
    # the enumeration route decides this four-class net before any encoding is
    # built — it reports `confirmed=True` by construction (its trace is a firing
    # sequence) and ignores `counterexample_replay`, so the tri-state would never
    # be exercised. The route's own confirmed-by-construction contract is pinned
    # by test_enumeration_route_decides_without_a_solver below.
    _p0, p1, net = _conserved_pair()
    solver = dict(enumeration_max_classes=0, timeout_ms=15_000)

    # Violated with a replayed chain -> True.
    violated = lp.verify(net, lp.place_bound(p1, 2), initial_marking={"p0": 3}, **solver)
    assert violated.verdict == "violated", violated.report
    assert violated.counterexample_confirmed is True
    assert violated.counterexample_trace, "a confirmed replay carries the trace"

    # Proven -> the replay never applied.
    proven = lp.verify(net, lp.place_bound(p1, 3), initial_marking={"p0": 3}, **solver)
    assert proven.verdict == "proven", proven.report
    assert proven.counterexample_confirmed is None

    # Replay disabled -> also "did not apply", and no trace is produced.
    off = lp.verify(
        net,
        lp.place_bound(p1, 2),
        initial_marking={"p0": 3},
        counterexample_replay=False,
        **solver,
    )
    assert off.verdict == "violated", off.report
    assert off.counterexample_confirmed is None
    assert off.counterexample_trace == []


def _wide_fanout_net(width):
    """One source place drained by `width` competing transitions, one sink each.

    The abstract counterexample replay searches breadth-first, so with S=4 it
    must admit every 3-token distribution over the `width` sinks before it can
    reach the 4-firing violation of ``place_bound(P00, 3)``. At width 48 that
    is C(50, 3) = 19_600 states, comfortably past the replay's 10_000-node
    budget.
    """
    source = lp.Place("S")
    sinks = [lp.Place(f"P{i:02d}") for i in range(width)]
    net = lp.Net("fanout")
    for i, sink in enumerate(sinks):
        net = net.transition(
            lp.Transition(f"t{i:02d}")
            .input(lp.one(source))
            .output(lp.out(sink))
            .action(lp.fork)
            .build()
        )
    return sinks[0], net.build()


def test_counterexample_confirmed_is_false_when_the_replay_exhausts_its_budget():
    # The False arm of the tri-state, mirroring the Rust budget-exhaustion
    # tests through the bindings. False means the replay APPLIED and did not
    # confirm -- here because its search budget ran out, which is an absence
    # of evidence, so the violated verdict stands. That is exactly what
    # separates False from None: None means the replay never ran at all.
    first_sink, net = _wide_fanout_net(48)
    # Explicit VER-017 opt-out: the replay is what is under test, and this net's
    # state-class graph does not close — the enumeration route would spend the
    # whole 50 000-class budget (minutes) only to truncate and hand the query to
    # the very pipeline the test wants, unchanged.
    result = lp.verify(
        net,
        lp.place_bound(first_sink, 3),
        initial_marking={"S": 4},
        enumeration_max_classes=0,
        timeout_ms=30_000,
    )
    assert result.verdict == "violated", result.report
    assert result.counterexample_confirmed is False, result.report
    assert "search node budget" in result.report, result.report


def test_unresolved_property_place_is_refused():
    # A property over a place the net never declares would encode to `false`,
    # which proves anything. Every implementation refuses with the same reason.
    if not lp.z3_available():
        pytest.skip("no usable z3 executable")
    p0 = lp.Place("p0")
    p1 = lp.Place("p1")
    net = (
        lp.Net("tiny")
        .transition(lp.Transition("t").input(lp.one(p0)).output(lp.out(p1)).action(lp.fork).build())
        .build()
    )
    # Explicit VER-017 opt-out (TypeScript's test carries the same one): the
    # refusal is a property of the ENCODERS, and the enumeration route would
    # decide this two-class net first — over the real state space, where a place
    # the net never declares is simply never marked, so it answers `proven`
    # without ever asking whether the name resolves.
    result = lp.verify(
        net,
        lp.unreachable([lp.Place("Ghost")]),
        initial_marking={p0: 1},
        enumeration_max_classes=0,
    )
    assert result.verdict == "unknown", result.report
    assert "does not resolve in the net ('Ghost')" in result.report
    # VER-003 AC4: no route could decide it.
    assert result.route == "unavailable", result.report


# ---------- VER-014 conditional sinks -------------------------------------


def _halt_net():
    """p0(1) -> t -> AND(a, b); a -> ta -> XOR(done | halt); b -> tb -> done, tb
    inhibited by halt. The quiescent markings are {done:2}, {halt:1, done:1} and
    {halt:1, b:1} — the last is the designed terminal a plain sink cannot excuse.
    """
    p0 = lp.Place("p0")
    a = lp.Place("a")
    b = lp.Place("b")
    done = lp.Place("done")
    halt = lp.Place("halt")
    net = (
        lp.Net("haltNet")
        .transition(
            lp.Transition("t").input(lp.one(p0)).output(lp.and_(lp.out(a), lp.out(b))).action(lp.fork).build()
        )
        .transition(
            lp.Transition("ta")
            .input(lp.one(a))
            .output(lp.xor(lp.out(done), lp.out(halt)))
            .action(lp.fork)
            .build()
        )
        .transition(
            lp.Transition("tb")
            .input(lp.one(b))
            .inhibitor(lp.inhibitor(halt))
            .output(lp.out(done))
            .action(lp.fork)
            .build()
        )
        .build()
    )
    return p0, a, b, done, halt, net


def test_sink_places_when_excuses_work_the_halt_interrupted():
    """VER-014: a halt that strands pending work is a violation until the work is
    declared to rest under the halt marker."""
    _p0, _a, b, done, halt, net = _halt_net()
    common = dict(initial_marking={"p0": 1}, sink_places=[done], timeout_ms=30_000)
    # Explicit VER-017 opt-out for the four calls below: this net's graph closes,
    # so the enumeration route would answer first and the ENCODERS' conditional
    # conjuncts — what VER-014 changed here — would never be built. The route's
    # own agreement is asserted separately at the end.
    encoders = dict(common, enumeration_max_classes=0)

    plain = lp.verify(net, lp.deadlock_free(), **encoders)
    assert plain.verdict == "violated", plain.report

    # The marker alone: `halt` is at rest, `b` is still stranded under it.
    marker_only = lp.verify(net, lp.deadlock_free(), sink_places_when={halt: []}, **encoders)
    assert marker_only.verdict == "violated", marker_only.report

    # `b` may rest while halted: no quiescent marking strands anything.
    excused = lp.verify(net, lp.deadlock_free(), sink_places_when={halt: [b]}, **encoders)
    assert excused.verdict == "proven", excused.report
    assert "Property: Deadlock freedom (sinks: done; when halt: b)" in excused.report

    # TerminatesAtSink reads the unconditional sinks only: {halt:1, b:1} marks none.
    reaches = lp.verify(net, lp.terminates_at_sink(), sink_places_when={halt: [b]}, **encoders)
    assert reaches.verdict == "violated", reaches.report

    # VER-002 AC7 / VER-017 AC6: every route decides the same predicate, so the
    # enumeration route reads the same rest set and renders the same Property line.
    enumerated = lp.verify(net, lp.deadlock_free(), sink_places_when={halt: [b]}, **common)
    assert enumerated.route == "enumeration", enumerated.report
    assert enumerated.verdict == excused.verdict, enumerated.report
    assert "Property: Deadlock freedom (sinks: done; when halt: b)" in enumerated.report


# ---------- VER-015 linear state-equation bound ---------------------------


def _fork_or_halt():
    """p0(1) -> f -> XOR(AND(a, b) | halt); a -> ga -> ra; b -> gb -> rb;
    ra + rb -> join -> done. `{ra, rb, halt}` is unreachable, and no EQUALITY law
    says so — the halt branch turns two units into one."""
    places = {n: lp.Place(n) for n in ("p0", "a", "b", "ra", "rb", "halt", "done")}
    net = (
        lp.Net("forkOrHalt")
        .transition(
            lp.Transition("f")
            .input(lp.one(places["p0"]))
            .output(lp.xor(lp.and_(lp.out(places["a"]), lp.out(places["b"])), lp.out(places["halt"])))
            .action(lp.fork)
            .build()
        )
        .transition(
            lp.Transition("ga").input(lp.one(places["a"])).output(lp.out(places["ra"])).action(lp.fork).build()
        )
        .transition(
            lp.Transition("gb").input(lp.one(places["b"])).output(lp.out(places["rb"])).action(lp.fork).build()
        )
        .transition(
            lp.Transition("join")
            .input(lp.one(places["ra"]))
            .input(lp.one(places["rb"]))
            .output(lp.out(places["done"]))
            .action(lp.fork)
            .build()
        )
        .build()
    )
    return places, net


def test_linear_bound_proves_structurally_and_hands_over_otherwise():
    """VER-015: the bound proves an unreachable marking no equality law excludes,
    and says so when none separates the violation."""
    places, net = _fork_or_halt()
    # Explicit VER-017 opt-out on every call: this net closes at seven classes, so
    # the enumeration route would decide each query before the VER-015 phase ran
    # and the report would carry no bound lines at all. The bound is what is
    # under test, so the route is turned off rather than the assertions weakened.
    solver = dict(enumeration_max_classes=0, timeout_ms=30_000)
    proven = lp.verify(
        net,
        lp.unreachable([places["ra"], places["rb"], places["halt"]]),
        initial_marking={"p0": 1},
        **solver,
    )
    assert proven.verdict == "proven", proven.report
    assert proven.route == "structural", proven.report
    assert "Result: property proven structurally (linear state-equation bound)" in proven.report
    assert "  Linear state-equation bound: " in proven.report
    assert "violation needs " in proven.report

    # A reachable target: no bound separates it, so the fixpoint query decides.
    reachable = lp.verify(
        net,
        lp.mutual_exclusion([places["ra"], places["rb"]]),
        initial_marking={"p0": 1},
        **solver,
    )
    assert reachable.verdict == "violated", reachable.report
    assert reachable.route == "smt", reachable.report
    assert "  Linear state-equation bound: none separates the violation" in reachable.report

    # linear_bound=False forces the fixpoint path for the same proven query.
    ic3 = lp.verify(
        net,
        lp.unreachable([places["ra"], places["rb"], places["halt"]]),
        initial_marking={"p0": 1},
        linear_bound=False,
        **solver,
    )
    assert ic3.verdict == "proven", ic3.report
    assert ic3.route == "smt", ic3.report
    assert "Linear state-equation bound" not in ic3.report


def test_encode_smt_scripts_reports_the_bound_query():
    """VER-015 AC4: the bound script is reported for a linear demand, and is None
    for a quiescence property, which has none."""
    places, net = _fork_or_halt()
    with_bound = lp.encode_smt_scripts(
        net,
        lp.unreachable([places["ra"], places["rb"], places["halt"]]),
        initial_marking={"p0": 1},
    )
    assert with_bound["bound"] is not None
    assert "(set-logic QF_LIA)" in with_bound["bound"]

    without = lp.encode_smt_scripts(net, lp.deadlock_free(), initial_marking={"p0": 1})
    assert without["bound"] is None

    # `linear_bound=False` gates the emitted script exactly as it gates the phase
    # in verify(): no bound query, and the other two scripts byte-identical.
    disabled = lp.encode_smt_scripts(
        net,
        lp.unreachable([places["ra"], places["rb"], places["halt"]]),
        initial_marking={"p0": 1},
        linear_bound=False,
    )
    assert disabled["bound"] is None
    assert disabled["horn"] == with_bound["horn"]
    assert disabled["certificate"] == with_bound["certificate"]


# ---------- VER-016 state equation ----------------------------------------


def test_state_equation_keeps_verdicts_and_passes_the_certificate_check():
    """VER-016: a proven verdict carries the counter count and a passing
    certificate; a genuine violation stays violated."""
    places, net = _fork_or_halt()
    # Explicit VER-017 opt-out: the state equation is part of the flat ENCODING,
    # which the enumeration route never builds — it would close this seven-class
    # graph and report neither the counter count nor a certificate check.
    proven = lp.verify(
        net,
        lp.deadlock_free(),
        initial_marking={"p0": 1},
        sink_places=[places["done"], places["halt"]],
        state_equation=True,
        enumeration_max_classes=0,
        timeout_ms=30_000,
    )
    assert proven.verdict == "proven", proven.report
    assert "  State equation: encoded over 5 firing counters (VER-016)" in proven.report
    assert "  Certificate check: PASSED (init, consecution, safety)" in proven.report

    violated = lp.verify(
        net,
        lp.deadlock_free(),
        initial_marking={"p0": 1},
        sink_places=[places["done"]],
        state_equation=True,
        enumeration_max_classes=0,
        timeout_ms=30_000,
    )
    assert violated.verdict == "violated", violated.report


def test_state_equation_is_off_by_default_and_visible_in_the_scripts():
    """VER-016 AC1/AC2: the option changes the encoding, and only when asked."""
    places, net = _fork_or_halt()
    args = dict(initial_marking={"p0": 1}, sink_places=[places["done"]])
    off = lp.encode_smt_scripts(net, lp.deadlock_free(), **args)
    on = lp.encode_smt_scripts(net, lp.deadlock_free(), state_equation=True, **args)

    assert "n0p" not in off["horn"]
    assert "n0p" in on["horn"]
    # Seven places plus five flat transitions: the certificate ranges over 12 args.
    assert "(x!11 Int)" in on["certificate"]
    assert "(x!11 Int)" not in off["certificate"]


# ---------- VER-017 bounded state-space enumeration + VER-003 route -------


def _linear_pipeline(n, *, timed=False):
    """``p0 -> t0 -> p1 -> ... -> pn``: the narrow, deep shape the fixpoint engine
    handles worst and enumeration handles trivially. ``n + 1`` markings, one class
    each. With ``timed`` the first transition is ``delayed``, which takes the net
    out of the route's untimed gate."""
    places = [lp.Place(f"p{i}") for i in range(n + 1)]
    net = lp.Net("pipeline")
    for i in range(n):
        t = (
            lp.Transition(f"t{i}")
            .input(lp.one(places[i]))
            .output(lp.out(places[i + 1]))
            .action(lp.fork)
        )
        if timed and i == 0:
            t = t.timing(lp.delayed(10))
        net = net.transition(t.build())
    return places, net.build()


def test_enumeration_route_decides_without_a_solver():
    """VER-017 AC1/AC3: the state-class graph closes inside the budget, so the
    property is decided exactly with no solver phase at all, and the result says
    which route answered and that no invariants were computed."""
    places, net = _linear_pipeline(6)
    result = lp.verify(
        net,
        lp.deadlock_free(),
        initial_marking={"p0": 1},
        sink_places=[places[6]],
        timeout_ms=30_000,
    )
    assert result.verdict == "proven", result.report
    assert result.route == "enumeration", result.report
    assert "=== Bounded state-space enumeration (VER-017) ===" in result.report
    assert "State classes: 7" in result.report
    assert "P-invariants: not computed (no encoding is built on this route)" in result.report
    # No solver phase ran: none of the SMT pipeline's headings appear.
    assert "=== Phase 1: Net Flattening ===" not in result.report
    assert "=== Phase 4: SMT Verification ===" not in result.report
    # AC3: an empty invariant list here means "not computed", which is exactly
    # what `route` is for -- the statistics say so too.
    assert result.invariants_found == 0
    assert result.structural_result == "n/a (state-space enumeration)"


def test_enumeration_violation_is_a_real_firing_sequence():
    """VER-017 AC2: without the sink the pipeline strands its token, and the
    witness is the ordered firing sequence from the initial marking -- reported
    as confirmed, because a graph path IS a firing sequence."""
    _places, net = _linear_pipeline(6)
    result = lp.verify(net, lp.deadlock_free(), initial_marking={"p0": 1}, timeout_ms=30_000)
    assert result.verdict == "violated", result.report
    assert result.route == "enumeration", result.report
    assert result.counterexample_transitions == ["t0", "t1", "t2", "t3", "t4", "t5"]
    assert result.counterexample_confirmed is True, result.report


def test_enumeration_truncation_hands_over_to_the_smt_pipeline():
    """VER-017 AC4: over budget the route declines, names the budget, and the SMT
    pipeline runs unchanged -- same verdict, by the other means."""
    places, net = _linear_pipeline(6)
    truncated = lp.verify(
        net,
        lp.deadlock_free(),
        initial_marking={"p0": 1},
        sink_places=[places[6]],
        enumeration_max_classes=3,
        timeout_ms=30_000,
    )
    assert truncated.verdict == "proven", truncated.report
    assert truncated.route == "smt", truncated.report
    assert (
        "Bounded state-space enumeration truncated at 3 classes (VER-017); "
        "verifying via the SMT pipeline." in truncated.report
    )
    assert "=== Phase 4: SMT Verification ===" in truncated.report

    # AC5/AC6: budget 0 never runs the route at all, and both routes agree.
    disabled = lp.verify(
        net,
        lp.deadlock_free(),
        initial_marking={"p0": 1},
        sink_places=[places[6]],
        enumeration_max_classes=0,
        timeout_ms=30_000,
    )
    assert disabled.verdict == "proven", disabled.report
    assert disabled.route == "smt", disabled.report
    assert "Bounded state-space enumeration" not in disabled.report


def test_enumeration_route_is_skipped_for_a_timed_net():
    """VER-017 AC5: the graph carries firing domains, so on a timed net its
    `proven` would be the weaker TIMED claim; the route stands aside and the
    encoders make the untimed one (VER-004)."""
    places, net = _linear_pipeline(6, timed=True)
    result = lp.verify(
        net,
        lp.deadlock_free(),
        initial_marking={"p0": 1},
        sink_places=[places[6]],
        timeout_ms=30_000,
    )
    assert result.verdict == "proven", result.report
    assert result.route == "smt", result.report
    assert "Bounded state-space enumeration" not in result.report
    assert "=== Phase 1: Net Flattening ===" in result.report


def test_enumeration_route_is_skipped_for_a_net_with_environment_places():
    """VER-017 AC5: the graph does not model injection (VER-006), so an open net
    is left to the encoders."""
    _in, out, net = _env_source_net()
    result = lp.verify(
        net,
        lp.place_bound(out, 0),
        environment_places=["IN"],
        environment_mode=lp.always_available(),
        timeout_ms=15_000,
    )
    assert result.route != "enumeration", result.report
    assert "Bounded state-space enumeration" not in result.report


def test_enumeration_route_is_skipped_for_a_nu_net():
    """VER-017 AC5, fourth skip case: a net with a match (ν-join) transition has
    its own exact route (VER-012, Route B), which subsumes this one, so the
    enumeration route stands aside."""
    source = lp.Place("source")
    a = lp.Place("branchA")
    b = lp.Place("branchB")
    merged = lp.Place("merged")
    net = (
        lp.Net("nu_join")
        .transition(
            lp.Transition("fork")
            .input(lp.one(source))
            .output(lp.and_(a, b))
            .action(lp.fork)
            .build()
        )
        .transition(
            lp.Transition("join")
            .input(lp.one(a))
            .input(lp.one(b))
            .match_spec(lp.match_spec([(a, lambda m: m), (b, lambda m: m)]))
            .output(lp.out(merged))
            .action(lp.fork)
            .build()
        )
        .build()
    )
    # Untimed and closed, so the ν gate is the only one that can skip the route.
    result = lp.verify(
        net,
        lp.place_bound(merged, 1),
        initial_marking={"source": 1},
        timeout_ms=30_000,
    )
    assert result.route != "enumeration", result.report
    assert "Bounded state-space enumeration" not in result.report


# ---------- VER-007 semiflow union: the `auto` setting --------------------


def test_semiflow_invariants_auto_unions_only_when_the_basis_lost_a_law():
    """VER-007 AC3: `auto` decides in one pass from the drops the pipeline already
    has, says which way it went, and never differs in verdict from the explicit
    setting it chose.

    Explicit VER-017 opt-out throughout: these are Phase-3 report lines, and the
    enumeration route builds no encoding to strengthen.
    """
    work, _sink, loop = _semiflow_loop()
    args = dict(initial_marking={"Budget": 1}, enumeration_max_classes=0, timeout_ms=30_000)

    # The reset arc on `Stamp` drops every basis row whose support touches it --
    # the case the option exists for, so `auto` unions.
    auto_on = lp.verify(loop, lp.place_bound(work, 1), semiflow_invariants="auto", **args)
    assert auto_on.verdict == "proven", auto_on.report
    assert "  Semiflow union: ON (auto — the basis lost a law to the H1 guard)" in auto_on.report
    assert "  Semiflows encoded as invariants: " in auto_on.report
    explicit_on = lp.verify(loop, lp.place_bound(work, 1), semiflow_invariants=True, **args)
    assert auto_on.verdict == explicit_on.verdict, auto_on.report

    # A clean net keeps a complete basis, so the (worst-case exponential)
    # enumeration is skipped -- and the wording says the skipped semiflows add no
    # CONSTRAINT, not that they would add nothing (AC3, last sentence).
    _p0, p1, clean = _conserved_pair()
    clean_args = dict(initial_marking={"p0": 3}, enumeration_max_classes=0, timeout_ms=30_000)
    auto_off = lp.verify(clean, lp.place_bound(p1, 3), semiflow_invariants="auto", **clean_args)
    assert auto_off.verdict == "proven", auto_off.report
    assert (
        "  Semiflow union: off (auto — the basis is complete, so the semiflows would add no "
        "constraint the encoding does not already have; they may still differ in FORM)"
    ) in auto_off.report
    assert "Semiflows encoded as invariants" not in auto_off.report
    explicit_off = lp.verify(clean, lp.place_bound(p1, 3), **clean_args)
    assert auto_off.verdict == explicit_off.verdict, auto_off.report

    # Off (the default) says nothing either way: the line is emitted only under
    # `auto`, so default reports stay byte-identical (AC2).
    assert "Semiflow union:" not in explicit_off.report


def test_semiflow_invariants_rejects_a_mode_it_does_not_know():
    """Only ``True`` / ``False`` / ``"auto"``: a typo is an error, never a silent
    fall-back to off."""
    _p0, p1, net = _conserved_pair()
    with pytest.raises(ValueError, match="auto"):
        lp.verify(net, lp.place_bound(p1, 3), semiflow_invariants="Auto")
    with pytest.raises(TypeError):
        lp.verify(net, lp.place_bound(p1, 3), semiflow_invariants=1)


# ---------- VER-006 vacuous quiescence --------------------------------------


def test_quiescence_on_a_never_quiescent_net_says_the_proof_is_vacuous():
    """VER-006: under modelled injection the transition is enabled in every
    marking, so no marking can be quiescent and every quiescence property is
    vacuously true. The report says so -- an empty claim must not read as a
    guarantee about the workflow."""
    _in, out, net = _env_source_net()
    result = lp.verify(
        net,
        lp.deadlock_free(),
        environment_places=["IN"],
        environment_mode=lp.always_available(),
        sink_places=[out],
        timeout_ms=15_000,
    )
    assert result.verdict == "proven", result.report
    assert "NOTE: no marking of this net can be quiescent" in result.report
    assert "vacuously true here, and a `proven` says nothing about the net" in result.report

    # A closed net whose quiescence is real carries no such note.
    places, closed = _linear_pipeline(3)
    honest = lp.verify(
        closed,
        lp.deadlock_free(),
        initial_marking={"p0": 1},
        sink_places=[places[3]],
        enumeration_max_classes=0,
        timeout_ms=15_000,
    )
    assert "no marking of this net can be quiescent" not in honest.report


# ---------- VER-001 the structural shortcut governs ORDINARY nets only -----


def _deadlock_free_verdict(net, marking):
    """Explicit VER-017 opt-out: the enumeration route decides each of the nets
    below exactly, and the subject here is the structural shortcut above it."""
    return lp.verify(
        net,
        lp.deadlock_free(),
        initial_marking=marking,
        enumeration_max_classes=0,
        timeout_ms=30_000,
    )


def _proven_structurally(result):
    return result.verdict == "proven" and result.method == "structural"


def test_structural_shortcut_refuses_a_net_with_a_read_arc():
    """Commoner's theorem -- every siphon holds an initially marked trap implies
    deadlock freedom -- is about an ORDINARY net. The siphon/trap fixpoints are
    computed from the pre/post vectors alone and never read the read, inhibitor or
    reset sets, the consume-all set or the arc weights, so on a net carrying any of
    them they answer about a strictly MORE PERMISSIVE net -- the wrong direction
    for a deadlock proof.

    ``t1: one(a) read(g) -> g`` with ``t2: one(g) -> a`` from ``{a:1}``: t1 needs a
    token in ``g`` to fire and only t2 can put one there, but t2 needs ``g`` too, so
    nothing is enabled. The executor confirms the net is dead at its initial
    marking; the shortcut used to certify it deadlock-free.
    """
    a, g = lp.Place("a"), lp.Place("g")
    net = (
        lp.Net("read-gate")
        .transition(
            lp.Transition("t1")
            .input(lp.one(a))
            .read(lp.read(g))
            .output(lp.out(g))
            .action(lp.fork)
            .build()
        )
        .transition(
            lp.Transition("t2").input(lp.one(g)).output(lp.out(a)).action(lp.fork).build()
        )
        .build()
    )
    # The net really is dead: nothing fires, so the run quiesces on its input.
    final = lp.run_sync(net, initial={a: [{"v": 1}]})
    assert (final.count(a), final.count(g)) == (1, 0)

    result = _deadlock_free_verdict(net, {"a": 1})
    assert not _proven_structurally(result), (
        f"a dead net was proven deadlock-free structurally:\n{result.report}"
    )


def test_structural_shortcut_refuses_an_arc_weight_above_one():
    """``t: exactly(2, a) -> a`` from ``{a:1}``. One token satisfies ``m >= 1`` but
    not the weight-2 demand, so the net is dead; the fixpoints read the SUPPORT of
    the pre-vector, not its weights."""
    a = lp.Place("a")
    net = (
        lp.Net("weighted")
        .transition(
            lp.Transition("t").input(lp.exactly(2, a)).output(lp.out(a)).action(lp.fork).build()
        )
        .build()
    )
    final = lp.run_sync(net, initial={a: [{"v": 1}]})
    assert final.count(a) == 1

    result = _deadlock_free_verdict(net, {"a": 1})
    assert not _proven_structurally(result), result.report


def test_structural_shortcut_refuses_an_inhibitor_arc():
    """``t: one(a) inhibitor(b) -> a`` from ``{a:1, b:1}``. The marked inhibitor
    place blocks the only transition; the fixpoints never read the inhibitor set."""
    a, b = lp.Place("a"), lp.Place("b")
    net = (
        lp.Net("inhibited")
        .transition(
            lp.Transition("t")
            .input(lp.one(a))
            .inhibitor(lp.inhibitor(b))
            .output(lp.out(a))
            .action(lp.fork)
            .build()
        )
        .build()
    )
    final = lp.run_sync(net, initial={a: [{"v": 1}], b: [{"v": 1}]})
    assert (final.count(a), final.count(b)) == (1, 1)

    result = _deadlock_free_verdict(net, {"a": 1, "b": 1})
    assert not _proven_structurally(result), result.report


def test_structural_shortcut_still_fires_on_an_ordinary_net():
    """Without this the guard could pass by refusing everything. A token
    circulating a ring: every siphon holds a marked trap, and nothing about the net
    is outside what the fixpoints model, so the shortcut still applies."""
    a, b = lp.Place("a"), lp.Place("b")
    net = (
        lp.Net("ring")
        .transition(lp.Transition("t1").input(lp.one(a)).output(lp.out(b)).action(lp.fork).build())
        .transition(lp.Transition("t2").input(lp.one(b)).output(lp.out(a)).action(lp.fork).build())
        .build()
    )
    result = _deadlock_free_verdict(net, {"a": 1})
    assert _proven_structurally(result), result.report
    assert result.route == "structural", result.report


# ---------- VER-017 reset arcs in the enumeration route --------------------


@pytest.mark.parametrize("spec_name", ["one", "all_tokens"])
def test_enumeration_route_decides_a_net_that_consumes_and_resets_one_place(spec_name):
    """A reset arc on a place the SAME transition consumes. The executor runs this
    net, so the state-class graph the enumeration route walks must too.

    The graph's fire step used to apply the reset by removing the PRE-firing count
    read off the original marking, after the input loop had already drawn from the
    builder -- an overdraw, which the marking builder rejects, so the whole route
    died on a net that runs fine. Stating the reset directly (clear the place)
    cannot overdraw and matches what the flat encoder emits (``m'_p = post[p]``).
    """
    p, q = lp.Place("p"), lp.Place("q")
    spec = lp.one(p) if spec_name == "one" else lp.all_tokens(p)
    net = (
        lp.Net("reset-input")
        .transition(
            lp.Transition("t")
            .input(spec)
            .reset(lp.reset(p))
            .output(lp.out(q))
            .action(lp.fork)
            .build()
        )
        .build()
    )
    result = lp.verify(
        net, lp.place_bound(q, 5), initial_marking={"p": 3}, timeout_ms=30_000
    )
    assert result.verdict == "proven", result.report
    assert result.route == "enumeration", result.report

    # And the route agrees with the executor: the input takes its share, the reset
    # clears the rest, outputs are produced afterwards (EXEC-013 AC4), and `t`
    # cannot re-enable on a residue.
    final = lp.run_sync(net, initial={p: [{"i": 0}, {"i": 1}, {"i": 2}]})
    assert (final.count(p), final.count(q)) == (0, 1)


# ---------- VER-002 an absent property place is refused before every route -


def test_absent_property_place_is_refused_before_every_route():
    """A property naming a place the NET does not declare must be refused BEFORE
    any route runs, not inside the flat encoding branch.

    The enumeration route (VER-017), the linear bound (VER-015) and the ν route
    (NU-050) each return before that branch, and each answers such a property
    vacuously in the `proven` direction -- no reachable class marks a place the net
    has not got, and the bound's demand for it drops out of the conjunction -- so a
    mistyped place name used to certify. Contrast
    ``test_unresolved_property_place_is_refused`` above, which opts out of the
    enumeration route to exercise the encoders' own refusal.
    """
    p0, p1 = lp.Place("p0"), lp.Place("p1")
    net = (
        lp.Net("tiny")
        .transition(
            lp.Transition("t1").input(lp.one(p0)).output(lp.out(p1)).action(lp.fork).build()
        )
        .build()
    )
    reason = (
        "property names a place that does not resolve in the net ('Ghost'); refusing to "
        "certify (the encoding would be vacuously proven)"
    )

    # Every route is ON (the defaults), so the enumeration route is the one that
    # would have answered -- and it needs no solver.
    unreachable = lp.verify(net, lp.unreachable([lp.Place("Ghost")]), initial_marking={"p0": 1})
    assert unreachable.verdict == "unknown", unreachable.report
    assert unreachable.reason == reason, unreachable.report
    assert unreachable.route == "unavailable", unreachable.report

    # The same refusal on the linear-bound route, which also returns early.
    bound = lp.verify(net, lp.place_bound("Ghost", 0), initial_marking={"p0": 1})
    assert bound.verdict == "unknown", bound.report
    assert bound.reason == reason, bound.report

    # One absent name among declared ones is still a refusal.
    mixed = lp.verify(
        net, lp.mutual_exclusion([p1, lp.Place("Ghost")]), initial_marking={"p0": 1}
    )
    assert mixed.verdict == "unknown", mixed.report
    assert mixed.reason == reason, mixed.report

    # ... and a property naming only declared places still runs.
    ok = lp.verify(net, lp.place_bound(p1, 1), initial_marking={"p0": 1})
    assert ok.verdict != "unknown", ok.report


# ---------- VER-013 encode_smt_scripts honours the `auto` semiflow mode ----


def test_encode_smt_scripts_honours_the_auto_semiflow_mode():
    """VER-013 AC1: the script this reports must be the script the pipeline would
    send. ``encode_smt_scripts`` used to apply the union only for an explicit
    ``True``, so on a net where ``auto`` unions it under-reported the query --
    which would let the parity goldens pin something no verification ever emits.

    ``_coloured_loop`` makes the difference observable: its reset arc costs the
    basis a law to the H1 guard (so ``auto`` under :func:`verify` DOES union, see
    ``test_semiflow_invariants_auto_unions_only_when_the_basis_lost_a_law``) and the
    union changes the emitted script (``test_semiflows_reach_the_coloured_encoder``).
    """
    pending, net = _coloured_loop()
    off = _coloured_scripts(net, pending, False)
    auto = _coloured_scripts(net, pending, "auto")
    on = _coloured_scripts(net, pending, True)
    # A deficient basis: auto unions, so the script must be the strengthened one.
    assert auto["horn"] == on["horn"], "auto must emit what the setting it CHOSE (True) emits"
    assert auto["certificate"] == on["certificate"]
    assert auto["bound"] == on["bound"]
    # ... on a net where the option genuinely bites, so the equality above is a
    # decision rather than a coincidence.
    assert on["horn"] != off["horn"], (
        "the fixture must be a net whose semiflow union changes the script"
    )

    # A complete basis: auto declines, so the script matches the off case.
    _p0, p1, clean = _conserved_pair()

    def scripts(mode):
        return lp.encode_smt_scripts(
            clean, lp.place_bound(p1, 3), initial_marking={"p0": 3}, semiflow_invariants=mode
        )

    clean_auto, clean_off = scripts("auto"), scripts(False)
    assert clean_auto["horn"] == clean_off["horn"]
    assert clean_auto["certificate"] == clean_off["certificate"]
    assert clean_auto["bound"] == clean_off["bound"]
