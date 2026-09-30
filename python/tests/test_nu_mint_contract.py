"""The ν mint contract (NU-010) through the Python API.

A transition that writes a match key without consuming one is read as a fresh-name
mint only when it is declared, by ``mint_transitions`` or by consuming a declared
budget place. The built-in fork copies its input, so two copies of one correlation
id join at run time, and a route that read them as two fresh names proved the join
unreachable. Mirrors Rust ``rust/libpetri/tests/nu_mint_contract.rs``.
"""

from __future__ import annotations

import libpetri as lp
import pytest

# The verification tests need the SMT surface and, for the flat routes, a z3 binary; the
# executor test below needs neither.
needs_z3 = pytest.mark.skipif(
    not (lp.HAS_Z3 and lp.z3_available()), reason="z3 feature not enabled or no usable z3 executable"
)


def _copying_mints():
    """``mA: S1 -> A`` and ``mB: S2 -> B`` copy their input; ``J: A, B -> DONE`` joins by value."""
    s1, s2, a, b, done = (lp.Place(n) for n in ("S1", "S2", "A", "B", "DONE"))

    def join_action(ctx: lp.TransitionContext) -> None:
        ctx.output("DONE", ctx.input("A"))

    return (
        lp.Net("copying_mints")
        .transition(lp.Transition("mA").input(lp.one(s1)).output(lp.out(a)).action(lp.fork).build())
        .transition(lp.Transition("mB").input(lp.one(s2)).output(lp.out(b)).action(lp.fork).build())
        .transition(
            lp.Transition("J")
            .input(lp.one(a))
            .input(lp.one(b))
            .match_spec(lp.match_spec([(a, lambda v: v), (b, lambda v: v)]))
            .output(lp.out(done))
            .action(join_action)
            .build()
        )
        .build()
    )


def test_the_executor_joins_two_copies_of_one_id() -> None:
    net = _copying_mints()
    result = lp.run_sync(net, initial={lp.Place("S1"): ["order-7"], lp.Place("S2"): ["order-7"]})
    assert list(result.tokens(lp.Place("DONE"))) == ["order-7"]


@needs_z3
def test_an_undeclared_copying_producer_is_not_read_as_a_mint() -> None:
    result = lp.verify(
        _copying_mints(),
        lp.place_bound("DONE", 0),
        initial_marking={"S1": 1, "S2": 1},
    )
    assert result.verdict != "proven", result.report
    assert result.route != "nu-scg", result.report


@needs_z3
def test_a_declared_mint_is_read_as_one_and_the_report_says_so() -> None:
    net = _copying_mints()
    result = lp.verify(
        net,
        lp.place_bound("DONE", 0),
        initial_marking={"S1": 1, "S2": 1},
        mint_transitions=[t for t in net.transitions if t.name in ("mA", "mB")],
    )
    assert result.verdict == "proven", result.report
    assert result.route == "nu-scg"
    assert (
        "Mint contract (NU-010) assumed for mA, mB: each writes a freshly minted name into every "
        "coloured place it writes."
    ) in result.report


@needs_z3
def test_a_declared_mint_that_is_not_in_the_net_is_unknown() -> None:
    result = lp.verify(
        _copying_mints(),
        lp.place_bound("DONE", 0),
        initial_marking={"S1": 1, "S2": 1},
        mint_transitions=["mA", "mC"],
    )
    assert result.verdict == "unknown", result.report
    assert result.reason == "declared mint transition 'mC' not in the net (NU-010)"


@needs_z3
def test_a_timeout_forward_into_a_match_key_is_never_a_mint() -> None:
    """``t1: budget, reqA -> xor(okA, timeout(20, forward(reqA, a)))``, its twin into ``b``,
    and a join on ``a, b``: the timeout forwards the request token, so even declared, ``t1``
    and ``t2`` are no mints."""
    budget, a, b, done = lp.Place("budget"), lp.Place("a"), lp.Place("b"), lp.Place("done")

    def twin(name: str, req: str, ok: str, key: lp.Place) -> lp.Transition:
        r = lp.Place(req)
        return (
            lp.Transition(name)
            .input(lp.one(budget))
            .input(lp.one(r))
            .output(lp.xor(lp.out(lp.Place(ok)), lp.timeout(20, lp.forward_input(r, key))))
            .action(lp.fork)
            .build()
        )

    net = (
        lp.Net("forward_mints")
        .transition(twin("t1", "reqA", "okA", a))
        .transition(twin("t2", "reqB", "okB", b))
        .transition(
            lp.Transition("join")
            .input(lp.one(a))
            .input(lp.one(b))
            .match_spec(lp.match_spec([(a, lambda v: v), (b, lambda v: v)]))
            .output(lp.out(done))
            .action(lp.fork)
            .build()
        )
        .build()
    )
    result = lp.verify(
        net,
        lp.place_bound("done", 0),
        initial_marking={"budget": 2, "reqA": 1, "reqB": 1},
        mint_transitions=["t1", "t2"],
    )
    assert result.verdict != "proven", result.report
    assert result.route != "nu-scg", result.report


# ==================== one rejection at every entry point ====================


def _fork_join():
    """``fork: source -> branchA, branchB`` and ``join`` joining the two by name into
    ``merged``. Mirrors Rust ``mint_declarations.rs``."""
    source, a, b, merged = (lp.Place(n) for n in ("source", "branchA", "branchB", "merged"))
    return (
        lp.Net("fork-join")
        .transition(lp.Transition("fork").input(lp.one(source)).output(lp.and_(a, b)).action(lp.fork).build())
        .transition(
            lp.Transition("join")
            .input(lp.one(a))
            .input(lp.one(b))
            .match_spec(lp.match_spec([(a, lambda v: v), (b, lambda v: v)]))
            .output(lp.out(merged))
            .action(lp.fork)
            .build()
        )
        .build()
    )


_TYPO = "declared mint transition 'frok' not in the net (NU-010)"


def _fork_join_verify(**kw):
    return lp.verify(
        _fork_join(), lp.deadlock_free(), initial_marking={"source": 1}, sink_places=["merged"], **kw
    )


@needs_z3
def test_verify_answers_unknown_for_a_mint_name_not_in_the_net() -> None:
    result = _fork_join_verify(mint_transitions=["frok"])
    assert result.verdict == "unknown", result.report
    assert result.reason == _TYPO


@pytest.mark.skipif(not lp.HAS_Z3, reason="z3 feature not enabled")
def test_encode_smt_scripts_rejects_a_mint_name_not_in_the_net() -> None:
    """The Rust ``encode_scripts`` panics on it; the binding raises ``ValueError`` with
    the reason ``verify`` gives. Before, the scripts came back as if nothing were declared.
    A bad argument is no ``StructureError`` (the net is fine), so the type is exact."""
    with pytest.raises(ValueError, match=r"^declared mint transition 'frok' not in the net \(NU-010\)$") as err:
        lp.encode_smt_scripts(
            _fork_join(), lp.deadlock_free(), initial_marking={"source": 1}, mint_transitions=["frok"]
        )
    assert type(err.value) is ValueError


@pytest.mark.skipif(not lp.HAS_Z3, reason="z3 feature not enabled")
def test_encode_smt_scripts_reads_a_declared_mint() -> None:
    """With ``S1`` a budget place, ``mA`` mints by consuming it; declaring ``mB`` too puts
    the net on Route A's name-coloured encoding. Undeclared, it stays flat."""

    def scripts(mints):
        return lp.encode_smt_scripts(
            _copying_mints(),
            lp.place_bound("DONE", 0),
            initial_marking={"S1": 1, "S2": 1},
            budget_places=["S1"],
            mint_transitions=mints,
        )

    assert scripts([])["coloured"] is False
    assert scripts(["mB"])["coloured"] is True


@pytest.mark.skipif(not lp.HAS_Z3, reason="z3 feature not enabled")
@pytest.mark.parametrize("max_classes", [50_000, 0])
def test_verify_open_net_answers_unknown_for_a_mint_name_not_in_the_net(max_classes) -> None:
    """Before, the answer depended on the route: the graph route never looked at the name."""
    contract = lp.OpenNetContract.builder().initial_tokens("source", 1).rest("merged").build()
    result = lp.verify_open_net(_fork_join(), contract, mint_transitions=["frok"], max_classes=max_classes)
    assert result.verdict == "unknown", result.report
    assert result.reason == _TYPO
    assert result.class_count == 0, result.report
    assert (
        "State-class graph: skipped (a declared mint transition is not in the net (NU-010))"
        in result.report
    )


@needs_z3
def test_a_route_b_decline_for_an_undeclared_mint_points_at_mint_transitions() -> None:
    pointer = (
        "'fork' writes a coloured place without consuming one and is not declared to mint "
        "(NU-010); if the action writes a name minted with fresh_name, declare it with "
        "mint_transitions"
    )
    result = _fork_join_verify()
    assert f"ν-net Route B declined: {pointer}." in result.report, result.report
    assert result.verdict == "unknown", result.report
    assert result.reason.endswith(f"; {pointer}"), result.reason
    declared = _fork_join_verify(mint_transitions=["fork"])
    assert declared.verdict == "proven", declared.report
    assert "Route B declined" not in declared.report, declared.report


@pytest.mark.skipif(not lp.HAS_Z3, reason="z3 feature not enabled")
def test_a_single_string_is_not_a_list_of_mints() -> None:
    """Iterated, ``"fork"`` would declare the mints ``f``, ``o``, ``r`` and ``k``."""
    net = _fork_join()
    contract = lp.OpenNetContract.builder().initial_tokens("source", 1).rest("merged").build()
    calls = [
        lambda: lp.verify(net, lp.deadlock_free(), initial_marking={"source": 1}, mint_transitions="fork"),
        lambda: lp.encode_smt_scripts(net, lp.deadlock_free(), initial_marking={"source": 1}, mint_transitions="fork"),
        lambda: lp.verify_open_net(net, contract, mint_transitions="fork"),
    ]
    for call in calls:
        with pytest.raises(TypeError, match=r"not a single string: pass \['fork'\]"):
            call()
