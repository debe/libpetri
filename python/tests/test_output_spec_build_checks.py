"""Output specs rejected when the transition is built, through the Python binding.

The checks run in the Rust ``TransitionBuilder.build`` and surface as
``StructureError`` with the message every implementation uses, the first failing
check winning: IO-011, IO-013 (Timeout count), IO-013 (Xor in the Timeout child),
IO-014 (ForwardInput placement), IO-014 AC3 (forward from a non-input), IO-012
(ambiguous branches).
"""

from __future__ import annotations

import re

import pytest

import libpetri as lp

P = {n: lp.Place(n) for n in ("a", "b", "c", "d", "e", "A", "B", "C", "P", "Q", "X")}


def _build(spec):
    return lp.Transition("t").input(lp.one(P["a"])).output(spec).build()


def _ambiguous(i: int, j: int, places: str) -> str:
    return (
        f"output spec of transition 't' is ambiguous: output branches {i} and {j} both claim "
        f"{{{places}}}; no write can tell them apart (IO-012)"
    )


def _fwd(src: str, dst: str):
    return lp.forward_input(P[src], P[dst])


A, B, C, PP, Q = P["A"], P["B"], P["C"], P["P"], P["Q"]


@pytest.mark.parametrize(
    ("spec", "message"),
    [
        (lambda: lp.xor(PP, PP), _ambiguous(0, 1, "P")),
        (lambda: lp.xor(lp.and_(A, B), lp.and_(B, A)), _ambiguous(0, 1, "A, B")),
        (lambda: lp.xor(A, lp.xor(A, B)), _ambiguous(0, 1, "A")),
        (lambda: lp.and_(Q, lp.xor(PP, PP)), _ambiguous(0, 1, "Q, P")),
        (lambda: lp.xor(lp.and_(A, lp.xor(B, C)), lp.and_(A, B)), _ambiguous(0, 2, "A, B")),
        (lambda: lp.xor(PP, lp.timeout(10, PP)), _ambiguous(0, 1, "P")),
        (lambda: lp.xor(B, lp.timeout(10, _fwd("a", "B"))), _ambiguous(0, 1, "B")),
    ],
)
def test_io_012_ac5_ambiguous_specs_are_rejected(spec, message) -> None:
    with pytest.raises(lp.StructureError, match=f"^{re.escape(message)}$"):
        _build(spec())


@pytest.mark.parametrize(
    ("spec", "message"),
    [
        # Branches [X,A] [X,B] [X,A'] [Y,A] [Y,B] [Y,A'] with A' = A: (0, 2).
        (lambda: lp.and_(lp.xor(P["X"], lp.Place("Y")), lp.xor(A, B, A)), _ambiguous(0, 2, "X, A")),
        # A repeat in the first child shows at stride 3: (0, 3).
        (lambda: lp.and_(lp.xor(P["X"], P["X"]), lp.xor(A, B, C)), _ambiguous(0, 3, "X, A")),
        # A later alternative that repeats a deep branch of an earlier one: (3, 5).
        (
            lambda: lp.xor(
                lp.and_(lp.xor(A, B), lp.xor(C, lp.Place("D"))), lp.Place("E"), lp.and_(lp.Place("D"), B)
            ),
            _ambiguous(3, 5, "B, D"),
        ),
    ],
)
def test_io_012_reports_the_pair_the_other_implementations_report(spec, message) -> None:
    with pytest.raises(lp.StructureError, match=f"^{re.escape(message)}$"):
        _build(spec())


@pytest.mark.parametrize(
    "spec",
    [
        lambda: lp.xor(lp.and_(A, B, C), lp.and_(A, B)),
        lambda: lp.xor(lp.and_(PP, A), lp.and_(PP, B)),
        lambda: lp.xor(A, lp.timeout(10, B)),
    ],
)
def test_io_012_ac5_distinct_alternatives_build(spec) -> None:
    _build(spec())


def test_io_012_composition_into_one_host_place_is_rejected_as_ambiguous() -> None:
    a, o1, o2 = lp.Place("a"), lp.Place("o1"), lp.Place("o2")
    split = (
        lp.SubnetDef("Split")
        .transition(lp.Transition("t").input(lp.one(a)).output(lp.xor(o1, o2)).action(lp.fork).build())
        .input_port("a", a)
        .output_port("o1", o1)
        .output_port("o2", o2)
        .build()
    )
    x = lp.Place("X")
    message = (
        "output spec of transition 's/t' is ambiguous: output branches 0 and 1 both claim {X}; "
        "no write can tell them apart (IO-012)"
    )
    with pytest.raises(lp.StructureError, match=f"^{re.escape(message)}$"):
        lp.NetBuilder("Host").compose("s", split, {"a": lp.Place("A"), "o1": x, "o2": x})


IO013 = (
    "output spec of transition 't' has 2 Timeout nodes; an output spec has at most one, "
    "nested or not (IO-013)"
)


@pytest.mark.parametrize(
    "spec",
    [
        lambda: lp.timeout(10, lp.timeout(20, PP)),
        lambda: lp.xor(lp.timeout(10, A), lp.timeout(20, B)),
        lambda: lp.and_(lp.timeout(10, A), lp.xor(B, lp.timeout(20, C))),
    ],
    ids=["nested", "xor-siblings", "and-xor"],
)
def test_io_013_ac7_more_than_one_timeout_is_rejected(spec) -> None:
    with pytest.raises(lp.StructureError, match=f"^{re.escape(IO013)}$"):
        _build(spec())


@pytest.mark.parametrize(
    "spec",
    [lambda: lp.xor(A, lp.timeout(10, B)), lambda: lp.timeout(10, lp.and_(A, B))],
)
def test_io_013_ac7_one_timeout_builds(spec) -> None:
    _build(spec())


IO013_XOR = (
    "output spec of transition 't' has a Xor node inside the child of its Timeout node; "
    "the timeout outcome deposits one fixed set of places (IO-013)"
)


@pytest.mark.parametrize(
    "spec",
    [
        lambda: lp.timeout(10, lp.xor(A, B)),
        lambda: lp.xor(C, lp.timeout(10, lp.and_(A, lp.xor(B, P["d"])))),
    ],
    ids=["direct", "nested-under-and"],
)
def test_io_013_ac8_a_xor_inside_the_timeout_child_is_rejected(spec) -> None:
    with pytest.raises(lp.StructureError, match=f"^{re.escape(IO013_XOR)}$"):
        _build(spec())


@pytest.mark.parametrize(
    "spec",
    [
        lambda: lp.xor(A, lp.timeout(10, B)),
        lambda: lp.timeout(10, lp.and_(A, _fwd("a", "B"))),
    ],
)
def test_io_013_ac8_a_xor_outside_the_timeout_child_builds(spec) -> None:
    _build(spec())


def test_io_011_ac5_and_of_two_xors_names_b() -> None:
    message = (
        "output spec of transition 't' names place 'B' twice in one AND branch; outputs are "
        "sets (IO-015) \u2014 a weighted output is not supported, add a second place or a "
        "follow-up transition"
    )
    with pytest.raises(lp.StructureError, match=f"^{re.escape(message)}$"):
        _build(lp.and_(lp.xor(A, B), lp.xor(B, A)))


IO014 = (
    "output spec of transition 't' uses ForwardInput('a', 'b') outside the child of a "
    "Timeout node; a forward deposits only on the timeout outcome (IO-014)"
)


@pytest.mark.parametrize(
    "spec",
    [
        lambda: _fwd("a", "b"),
        lambda: lp.xor(P["c"], _fwd("a", "b")),
        lambda: lp.and_(P["c"], lp.xor(P["e"], _fwd("a", "b"))),
    ],
    ids=["bare", "under-xor", "under-and-xor"],
)
def test_io_014_ac7_a_forward_outside_a_timeout_child_is_rejected(spec) -> None:
    with pytest.raises(lp.StructureError, match=f"^{re.escape(IO014)}$"):
        _build(spec())


@pytest.mark.parametrize(
    "spec",
    [
        lambda: lp.timeout(10, _fwd("a", "b")),
        lambda: lp.xor(P["c"], lp.timeout(10, lp.and_(P["e"], _fwd("a", "b")))),
    ],
)
def test_io_014_ac7_a_forward_inside_a_timeout_child_builds(spec) -> None:
    _build(spec())


def test_the_first_failing_check_reports() -> None:
    # IO-013 before IO-014 placement.
    with pytest.raises(lp.StructureError, match="has 2 Timeout nodes"):
        _build(lp.and_(_fwd("a", "b"), lp.timeout(10, P["c"]), lp.timeout(20, P["d"])))
    # IO-013 Timeout count before IO-013 Xor in the Timeout child.
    with pytest.raises(lp.StructureError, match="has 2 Timeout nodes"):
        _build(lp.and_(lp.timeout(10, lp.xor(P["c"], P["d"])), lp.timeout(20, P["e"])))
    # IO-013 Xor in the Timeout child before IO-014 placement.
    with pytest.raises(lp.StructureError, match=f"^{re.escape(IO013_XOR)}$"):
        _build(lp.and_(_fwd("X", "b"), lp.timeout(10, lp.xor(P["c"], P["d"]))))
    # IO-014 placement before the non-input check.
    with pytest.raises(lp.StructureError, match=r"uses ForwardInput\('X', 'b'\) outside"):
        _build(_fwd("X", "b"))
    # The non-input check before IO-012.
    with pytest.raises(
        lp.StructureError, match=r"^Transition 't': ForwardInput references non-input place 'X'$"
    ):
        _build(lp.xor(P["b"], lp.timeout(10, _fwd("X", "b"))))
