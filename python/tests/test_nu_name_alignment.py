"""ν-net name alignment (spec NU-055) through the Python binding: the fixtures of
``spec/verification-fixtures/nu-aligned-fixtures.json`` (AC1, AC2, AC3, AC6), the
property descriptions, the re-exports, and the script encoder's refusal (AC4).

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
        return lp.name_aligned(places[0], places[1])
    if prop["type"] == "quiescent-name-aligned":
        return lp.quiescent_name_aligned(places[0], places[1])
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


def _named_by_reason(fixture: dict) -> str:
    """What an ``unknown`` fixture's reason names: EXTENDED for a BASE run, else the
    environment place, else the coloured place the initial marking marks, else the
    uncoloured property place."""
    if fixture["fragmentMode"] == "base":
        return "EXTENDED"
    if fixture.get("environmentPlaces"):
        return f"'{fixture['environmentPlaces'][0]}'"
    coloured = set(fixture["carrierPlaces"])
    for _, _, _, keys, relays in fixture["rows"]:
        coloured.update(keys, relays)
    marked = [p for p in fixture["marking"] if p in coloured]
    if marked:
        return f"'{marked[0]}'"
    return f"'{next(p for p in fixture['property']['places'] if p not in coloured)}'"


def test_nu055_lists_the_ten_fixtures() -> None:
    assert len(_fixtures()) == 10


@pytest.mark.parametrize("fixture", _fixtures(), ids=lambda f: f["id"])
def test_nu055_fixture(fixture: dict) -> None:
    """Every fixture: Route B, its verdict and witness length, no confirmation claimed
    for the graph's trace (VER-003), and an ``unknown`` reason naming the place or the
    declined fragment."""
    assert fixture["route"] == "B"
    result = _verify(fixture)
    assert result.route == "nu-scg", result.report
    assert ROUTE_B_MARKER in result.report, result.report
    assert result.verdict == fixture["expected"], result.report
    if "witnessLength" in fixture:
        assert len(result.counterexample_transitions) == fixture["witnessLength"]
    assert result.counterexample_confirmed is None
    if fixture["expected"] == "unknown":
        assert _named_by_reason(fixture) in result.reason, result.reason
        assert "verified via" not in result.reason


def test_nu055_describes_both_properties_byte_for_byte() -> None:
    box, items = lp.Place("box"), lp.Place("list")
    assert lp.name_aligned(box, items).description() == "Name alignment of box and list"
    assert (
        lp.quiescent_name_aligned("box", "list").description()
        == "Quiescent name alignment of box and list"
    )
    # Re-exported from the package, as joined_or_dead_lettered and quiescent_count are.
    assert lp.name_aligned is lpv.name_aligned
    assert lp.quiescent_name_aligned is lpv.quiescent_name_aligned


def test_nu055_ac2_an_absent_place_is_unknown_naming_it() -> None:
    fixture = _fixture("nu-aligned-search-quiescent-proven")
    result = lp.verify(
        _net(fixture),
        lp.quiescent_name_aligned("box", "nowhere"),
        initial_marking=fixture["marking"],
        mint_transitions=fixture["mintTransitions"],
        carrier_places=fixture["carrierPlaces"],
        fragment_mode="extended",
    )
    assert result.verdict == "unknown"
    assert "'nowhere'" in result.reason


@pytest.mark.parametrize("make", [lp.name_aligned, lp.quiescent_name_aligned])
def test_nu055_ac4_encode_smt_scripts_returns_no_script(make) -> None:
    fixture = _fixture("nu-aligned-search-quiescent-proven")
    with pytest.raises(lp.StructureError, match=re.escape(ONLY_B)):
        lp.encode_smt_scripts(
            _net(fixture),
            make("box", "list"),
            initial_marking=fixture["marking"],
            mint_transitions=fixture["mintTransitions"],
            carrier_places=fixture["carrierPlaces"],
            fragment_mode="extended",
        )
