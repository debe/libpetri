"""ν-net name alignment (spec NU-055) through the Python binding: the fixtures of
``spec/verification-fixtures/nu-aligned-fixtures.json`` (AC1, AC2, AC3, AC6, AC7, AC8),
the property descriptions, the list ``S`` (AC7), the re-exports, and the script
encoder's refusal (AC4).

The analysis lives in the Rust verifier (Route B, the name-partition state-class
graph); here we exercise it through Python. Mirrors Rust
``libpetri-verification/tests/nu_name_alignment.rs`` and TypeScript
``tests/verification/nu-name-alignment.test.ts``.
"""

from __future__ import annotations

import json
import pathlib
import re

import libpetri as lp
import libpetri.verification as lpv
import pytest

pytestmark = pytest.mark.skipif(not lp.HAS_Z3, reason="z3 feature not enabled")

FIXTURES = (
    pathlib.Path(__file__).resolve().parents[2]
    / "spec"
    / "verification-fixtures"
    / "nu-aligned-fixtures.json"
)

# The line Route B prints when it decided, or declined, the query.
ROUTE_B_MARKER = "ν-net Route B: name-aware state-class graph (NU-050)"
ONLY_B = "decided only by the name-partition state-class graph (NU-055, Route B)"


def _fixtures() -> list[dict]:
    return json.loads(FIXTURES.read_text(encoding="utf-8"))["fixtures"]


def _fixture(fixture_id: str) -> dict:
    return next(f for f in _fixtures() if f["id"] == fixture_id)


def _key(value):
    """The name projection of every key and relay: each token is its own name."""
    return value


def _net(fixture: dict) -> lp.BuiltNet:
    """The fixture's net from its rows: every input consumed once, every output
    produced once, every token its own name."""
    places: dict[str, lp.Place] = {}

    def p(name: str) -> lp.Place:
        return places.setdefault(name, lp.Place(name))

    net = lp.Net(fixture["net"])
    for name, ins, outs, keys, relays in fixture["rows"]:
        t = lp.Transition(name)
        for i in ins:
            t = t.input(lp.one(p(i)))
        t = t.output(lp.out(p(outs[0])) if len(outs) == 1 else lp.and_(*[p(o) for o in outs]))
        if keys:
            t = t.match_spec(
                lp.match_spec([(p(k), _key) for k in keys], relay_to=[(p(r), _key) for r in relays])
            )
        net = net.transition(t.action(lp.fork).build())
    return net.build()


def _property(fixture: dict) -> lp.SmtProperty:
    prop = fixture["property"]
    places = prop["places"]
    if prop["type"] == "name-aligned":
        return lp.name_aligned(places)
    if prop["type"] == "quiescent-name-aligned":
        return lp.quiescent_name_aligned(places)
    assert prop["type"] == "quiescent-count", prop
    return lp.quiescent_count(places, prop["min"], prop["max"])


def _verify(fixture: dict, **overrides) -> lp.VerificationResult:
    options = dict(
        initial_marking=fixture["marking"],
        mint_transitions=fixture["mintTransitions"],
        carrier_places=fixture["carrierPlaces"],
        budget_places=fixture.get("budgetPlaces"),
        fragment_mode=fixture["fragmentMode"],
        timeout_ms=30_000,
    )
    if fixture.get("environmentPlaces"):
        assert fixture["environmentMode"] == "always-available"
        options.update(
            environment_places=fixture["environmentPlaces"],
            environment_mode=lp.always_available(),
        )
    options.update(overrides)
    return lp.verify(_net(fixture), _property(fixture), **options)


def test_nu055_runs_every_fixture_and_every_unknown_names_its_reason() -> None:
    """One test per fixture below: the ids are distinct, so none shadows another, and
    every ``unknown`` fixture says what its reason must contain."""
    fixtures = _fixtures()
    assert fixtures
    assert len({f["id"] for f in fixtures}) == len(fixtures)
    for fixture in fixtures:
        if fixture["expected"] == "unknown":
            assert fixture.get("reasonContains"), fixture["id"]


@pytest.mark.parametrize("fixture", _fixtures(), ids=lambda f: f["id"])
def test_nu055_fixture(fixture: dict) -> None:
    """Every fixture: Route B, its verdict and witness length, no confirmation claimed
    for the graph's trace (VER-003), and an ``unknown`` reason containing the fixture's
    ``reasonContains``, which the refusal order picks when several refusals apply."""
    assert fixture["route"] == "B"
    result = _verify(fixture)
    assert result.route == "nu-scg", result.report
    assert ROUTE_B_MARKER in result.report, result.report
    assert result.verdict == fixture["expected"], result.report
    if "witnessLength" in fixture:
        assert len(result.counterexample_transitions) == fixture["witnessLength"]
    assert result.counterexample_confirmed is None
    if fixture["expected"] == "unknown":
        assert fixture["reasonContains"] in result.reason, result.reason
        assert "verified via" not in result.reason


def test_nu055_describes_both_properties_byte_for_byte() -> None:
    """For one, two and three places, as every other implementation does."""
    box, items = lp.Place("box"), lp.Place("list")
    assert lp.name_aligned([box]).description() == "Name alignment of box"
    assert lp.name_aligned([box, items]).description() == "Name alignment of box and list"
    assert (
        lp.name_aligned([box, "staged", items]).description()
        == "Name alignment of box, staged and list"
    )
    assert lp.quiescent_name_aligned(["box"]).description() == "Quiescent name alignment of box"
    assert (
        lp.quiescent_name_aligned(["box", "list"]).description()
        == "Quiescent name alignment of box and list"
    )
    assert (
        lp.quiescent_name_aligned(("box", "staged", "list")).description()
        == "Quiescent name alignment of box, staged and list"
    )
    # Re-exported from the package, as joined_or_dead_lettered and quiescent_count are.
    assert lp.name_aligned is lpv.name_aligned
    assert lp.quiescent_name_aligned is lpv.quiescent_name_aligned


def test_nu055_ac2_an_absent_place_is_unknown_naming_it() -> None:
    fixture = _fixture("nu-aligned-search-quiescent-proven")
    result = lp.verify(
        _net(fixture),
        lp.quiescent_name_aligned(["box", "nowhere", "elsewhere"]),
        initial_marking=fixture["marking"],
        mint_transitions=fixture["mintTransitions"],
        carrier_places=fixture["carrierPlaces"],
        fragment_mode="extended",
    )
    assert result.verdict == "unknown"
    assert "'nowhere'" in result.reason
    assert "'elsewhere'" not in result.reason, "the first absent place of S"


@pytest.mark.parametrize("make", [lp.name_aligned, lp.quiescent_name_aligned])
def test_nu055_ac7_a_repeated_place_counts_once_at_its_first_occurrence(make) -> None:
    box = lp.Place("box")
    # A Place and a bare name compare by name.
    assert make([box, "list", "box", lp.Place("list")]).description().endswith("of box and list")
    assert make(["list", box, "list"]).description().endswith("of list and box")
    assert make([box, box]).description().endswith("of box")


@pytest.mark.parametrize("make", [lp.name_aligned, lp.quiescent_name_aligned])
def test_nu055_ac7_an_empty_list_is_rejected_at_construction(make) -> None:
    with pytest.raises(ValueError, match=f"^{make.__name__} needs at least one place$"):
        make([])
    with pytest.raises(ValueError, match="needs at least one place"):
        make(p for p in ())


@pytest.mark.parametrize("make", [lp.name_aligned, lp.quiescent_name_aligned])
def test_nu055_a_bare_name_is_refused_not_split_into_letters(make) -> None:
    with pytest.raises(TypeError, match=re.escape(f"{make.__name__}(['box'])")):
        make("box")


def test_nu055_ac7_the_fixture_that_separates_the_list_reading_from_the_pairwise_one() -> None:
    """Three keystrokes: the net rests with two stale replies in ``reply`` and
    ``staged`` empty, which comparing ``reply`` with ``staged`` pairwise accepts."""
    result = _verify(_fixture("nu-aligned-search-three-keystrokes-quiescent-violated"))
    assert result.route == "nu-scg"
    assert result.verdict == "violated", result.report
    assert len(result.counterexample_transitions) == 12
    rest = result.counterexample_trace[-1]
    assert rest.get("staged", 0) == 0, rest
    assert rest.get("reply", 0) >= 2, rest


def test_nu055_ac7_reordering_s_changes_no_verdict_and_no_witness_length() -> None:
    fixture = _fixture("nu-aligned-search-three-quiescent-violated")
    for order in (["box", "list", "reply"], ["reply", "box", "list"], ["list", "reply", "box"]):
        result = lp.verify(
            _net(fixture),
            lp.quiescent_name_aligned(order),
            initial_marking=fixture["marking"],
            mint_transitions=fixture["mintTransitions"],
            carrier_places=fixture["carrierPlaces"],
            fragment_mode="extended",
        )
        assert result.route == "nu-scg", order
        assert result.verdict == "violated", (order, result.report)
        assert len(result.counterexample_transitions) == fixture["witnessLength"], order


def test_nu055_ac8_an_arrival_into_a_coloured_place_is_refused_before_a_marked_one() -> None:
    """``e`` is a carrier fed by arrivals(1) and ``box`` starts marked: step 3 of the
    refusal order names ``e``, ahead of step 7, which would name ``box``."""
    e, box = lp.Place("e"), lp.Place("box")
    net = (
        lp.Net("arrivalBeforeMarked")
        .transition(lp.Transition("fwd").input(lp.one(e)).output(lp.out(box)).action(lp.fork).build())
        .build()
    )
    result = lp.verify(
        net,
        lp.quiescent_name_aligned([box]),
        initial_marking={"box": 1},
        environment_places=["e"],
        environment_mode=lp.arrivals(1, 1),
        carrier_places=["e", "box"],
        fragment_mode="extended",
    )
    assert result.route == "nu-scg", result.report
    assert result.verdict == "unknown", result.report
    assert "environment place 'e'" in result.reason, result.reason
    assert "arrivals(k)" in result.reason, result.reason


@pytest.mark.parametrize("make", [lp.name_aligned, lp.quiescent_name_aligned])
def test_nu055_ac4_encode_smt_scripts_returns_no_script(make) -> None:
    fixture = _fixture("nu-aligned-search-quiescent-proven")
    with pytest.raises(lp.StructureError, match=re.escape(ONLY_B)):
        lp.encode_smt_scripts(
            _net(fixture),
            make(["box", "list"]),
            initial_marking=fixture["marking"],
            mint_transitions=fixture["mintTransitions"],
            carrier_places=fixture["carrierPlaces"],
            fragment_mode="extended",
        )
