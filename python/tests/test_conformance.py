"""Cross-language verifier conformance against the Lean reference
(``spec/verification-fixtures/conformance/README.md``).

For every net with an expected file, every property is verified under the four route
setups of ``rust/libpetri-verification/tests/route_agreement.rs`` and held against the
README conformance rule: never proven where the reference says violated, never violated
where it says proven, every violated trace replays under the reference firing rule. The
setups run twice: atomically (all rules) and with the in-flight split of VER-004 on, as
a caller gets it (rules 1, 3 and 4; ``conformance_support`` says why).
``unknown`` is always allowed and counted, as is a violation without a trace
(clarification 6); ``pytest -s`` prints the counts.

``LIBPETRI_CONFORMANCE_DIR`` points at another corpus; ``LIBPETRI_CONFORMANCE_DUMP=<dir>``
writes the traced violations of each net to ``<dir>/<id>.traces.json`` for the Lean
replay. The corpus test skips while the corpus or its expected verdicts are absent
(fails instead under ``LIBPETRI_CONFORMANCE_REQUIRE=1``); the SMT setups skip without z3.

The unit tests below (inline nets, never skipped) pin the loader, the reference firing
rule and that the checker goes red.
"""

import copy

import libpetri as lp
import pytest

import conformance_support as cs

_CORPUS, _SKIP_REASON = cs.load_corpus(cs.locate_corpus())
_TOTAL = cs.Stats()


@pytest.fixture(scope="module", autouse=True)
def _summary():
    yield
    if _TOTAL.verdicts:
        print("\n" + _TOTAL.render())


def _z3() -> bool:
    return bool(lp.HAS_Z3) and lp.z3_available()


if _CORPUS is None:

    def test_conformance_corpus():
        if cs.require_corpus():
            pytest.fail(f"LIBPETRI_CONFORMANCE_REQUIRE is set: {_SKIP_REASON}")
        pytest.skip(_SKIP_REASON)

else:

    @pytest.mark.parametrize(
        "net_file,expected_file",
        _CORPUS.cases,
        ids=[n.stem for n, _ in _CORPUS.cases],
    )
    def test_conformance(net_file, expected_file):
        z3 = _z3()
        findings, stats = cs.run_net(net_file, expected_file, z3, cs.dump_dir_from_env())
        _TOTAL.merge(stats)
        assert not findings, "\n".join(str(f) for f in findings)
        if not z3:
            pytest.skip(
                f"z3 absent: only 'enum' ran; skipped SMT setups {stats.skipped_routes}"
            )

    def test_every_corpus_net_has_an_expected_file():
        findings = cs.missing_expected_findings(_CORPUS)
        assert not findings, "\n".join(str(f) for f in findings)


# ======================================================================
# Unit tests on inline nets
# ======================================================================

# t1: a -> b, t2: b -> c; q declared with no arc; z marked, undeclared (inert).
SEQ = {
    "id": "unit-seq",
    "places": ["a", "b", "c", "q"],
    "marking": {"a": 1, "z": 1},
    "transitions": [
        {"name": "t1", "inputs": [{"place": "a", "kind": "one"}],
         "inhibitors": [], "reads": [], "resets": [],
         "output": {"type": "place", "place": "b"}, "priority": 0},
        {"name": "t2", "inputs": [{"place": "b", "kind": "one"}],
         "output": {"type": "place", "place": "c"}},
    ],
    "properties": [
        {"id": "p0", "type": "deadlock-free", "sinks": ["c"]},
        {"id": "p1", "type": "deadlock-free", "sinks": ["c", "z"]},
        {"id": "p2", "type": "terminates-at-sink", "sinks": ["c"]},
        {"id": "p4", "type": "place-bound", "place": "b", "bound": 1},
        {"id": "p6", "type": "mutual-exclusion", "places": ["a", "b"]},
        {"id": "p7", "type": "unreachable", "places": ["c", "z"]},
        {"id": "p9", "type": "quiescent-count", "places": ["c"], "min": 1, "max": 1},
        {"id": "p10", "type": "quiescent-count", "places": ["c"], "min": 2},
    ],
}

# Every input kind but `one`, read / inhibitor / reset arcs, xor / and / timeout / forward
# outputs and no output.
KINDS = {
    "id": "unit-kinds",
    "places": ["a", "b", "c", "d", "e", "g", "r"],
    "marking": {"a": 2, "b": 3, "r": 1},
    "transitions": [
        {"name": "t_ex", "inputs": [{"place": "a", "kind": "exactly", "n": 2}],
         "reads": ["r"],
         "output": {"type": "xor", "children": [
             {"type": "place", "place": "c"},
             {"type": "timeout", "afterMs": 50,
              "child": {"type": "forward", "from": "a", "to": "d"}}]},
         "priority": 1},
        {"name": "t_all", "inputs": [{"place": "b", "kind": "all"}], "inhibitors": ["c"],
         "output": {"type": "and", "children": [
             {"type": "place", "place": "e"}, {"type": "place", "place": "g"}]}},
        {"name": "t_al", "inputs": [{"place": "e", "kind": "atLeast", "n": 1}],
         "resets": ["g"], "output": None},
    ],
    "properties": [
        {"id": "k0", "type": "place-bound", "place": "d", "bound": 1},
        {"id": "k1", "type": "place-bound", "place": "d", "bound": 2},
    ],
}


def _prop(net: cs.ConfNet, pid: str) -> dict:
    return next(p for p in net.properties if p["id"] == pid)


def test_an_absent_corpus_is_a_skip_reason(tmp_path):
    corpus, why = cs.load_corpus(tmp_path)
    assert corpus is None and "absent" in why
    (tmp_path / "nets").mkdir()
    (tmp_path / "nets" / "x.json").write_text("{}")
    corpus, why = cs.load_corpus(tmp_path)
    assert corpus is None and "expected" in why


def test_the_loader_reads_every_input_kind_and_arc():
    net = cs.parse_net(KINDS)
    kinds = {i["kind"] for t in net.transitions for i in t.get("inputs", [])}
    assert kinds == {"exactly", "all", "atLeast"}
    built = cs.build_net(net)
    assert {t.name for t in built.transitions} == {"t_ex", "t_all", "t_al"}
    assert {p.name for p in built.places} == set(net.declared)


def test_the_loader_keeps_the_inert_place_out_of_the_net():
    net = cs.parse_net(SEQ)
    assert net.marking == {"a": 1, "z": 1}
    names = {p.name for p in cs.build_net(net).places}
    assert "q" in names  # declared, no arc
    assert "z" not in names  # marking only: inert


def test_the_loader_builds_all_six_property_types():
    props = cs.parse_net(SEQ).properties
    assert {p["type"] for p in props} == set(cs.PROPERTY_TYPES)
    for p in props:
        cs.build_property(p)


def test_a_three_place_mutual_exclusion_is_expressible_and_pairwise():
    # VER-002: violated iff two listed places are marked at once, on the reference side too.
    prop = {"id": "x", "type": "mutual-exclusion", "places": ["a", "b", "c"]}
    cs.build_property(prop)
    net = cs.parse_net(SEQ)
    assert cs.bad(net, prop, {"a": 1, "c": 1})
    assert not cs.bad(net, prop, {"b": 2})


def test_an_unknown_input_kind_is_rejected():
    doc = copy.deepcopy(SEQ)
    doc["transitions"][0]["inputs"][0]["kind"] = "some"
    with pytest.raises(ValueError, match="unknown input kind"):
        cs.parse_net(doc)


@pytest.mark.skipif(not lp.HAS_Z3, reason="z3 feature not enabled")
def test_the_verifier_agrees_on_the_inline_nets():
    # Every verdict of every available route conforms to the hand-derived reference.
    refs = {
        "unit-seq": {"p0": "violated", "p1": "proven", "p2": "proven", "p4": "proven",
                     "p6": "proven", "p7": "violated", "p9": "proven", "p10": "violated"},
        "unit-kinds": {"k0": "violated", "k1": "proven"},
    }
    z3 = lp.z3_available()
    for doc in (SEQ, KINDS):
        net = cs.parse_net(doc)
        built = cs.build_net(net)
        for prop in net.properties:
            for setup in cs.ALL_ROUTES:
                if setup.needs_z3 and not z3:
                    continue
                r = cs.run_route(built, net, prop, setup)
                if setup.atomic:
                    assert r.verdict == refs[net.id][prop["id"]], (net.id, prop["id"], setup.name, r.report)
                trace = list(r.counterexample_transitions)
                ref = {"property": prop["id"], "verdict": refs[net.id][prop["id"]]}
                split_net = not setup.atomic and cs.SPLIT_MARK in r.report
                assert cs.check(
                    net, prop, setup.name, r.verdict, trace, ref,
                    split_pass=not setup.atomic, split_net=split_net,
                ) == [], (net.id, prop["id"], setup.name, r.report)


# ---------------------------------------------------------------- reference rule


def test_a_timeout_forward_deposits_the_consumed_count():
    net = cs.parse_net(KINDS)
    assert cs.replay(net, _prop(net, "k0"), ["t_ex"]) is None  # d = 2 > 1
    assert cs.replay(net, _prop(net, "k1"), ["t_ex"]) is not None  # d = 2 <= 2


def test_a_completed_forward_deposits_one_token_and_a_timeout_the_consumed_count():
    # IO-016: the completing action claims `to` with one token; IO-014 AC6: the timeout
    # outcome deposits one per consumed token (README clarification 5). gen-000062's shape.
    net = cs.parse_net({
        "id": "fwd-completion",
        "places": ["p0", "p1"],
        "marking": {"p1": 3, "s0": 1},
        "transitions": [{
            "name": "t2",
            "inputs": [{"place": "p1", "kind": "exactly", "n": 3}],
            "inhibitors": ["p0"],
            "output": {"type": "timeout", "afterMs": 50,
                       "child": {"type": "forward", "from": "p1", "to": "p1"}},
        }],
        "properties": [{"id": "d", "type": "deadlock-free", "sinks": ["p0", "s0"]}],
    })
    outcomes = sorted(sorted(m.items()) for m in cs.fire(net.transitions[0], {"p1": 3, "s0": 1}))
    assert outcomes == [[("p1", 1), ("s0", 1)], [("p1", 3), ("s0", 1)]]
    # The completion outcome {p1:1, s0:1} is quiescent and strands p1.
    assert cs.replay(net, net.properties[0], ["t2"]) is None


def test_an_empty_trace_replays_only_when_the_initial_marking_violates():
    net = cs.parse_net(SEQ)
    assert cs.replay(net, _prop(net, "p0"), []) is not None  # t1 enabled at M0
    bound = {"id": "b", "type": "place-bound", "place": "a", "bound": 0}
    assert cs.replay(net, bound, []) is None


def test_a_branch_suffix_is_stripped_only_for_a_real_transition():
    net = cs.parse_net(SEQ)
    assert cs.strip_branch(net, "t1_b0") == "t1"
    assert cs.strip_branch(net, "zz_b0") == "zz_b0"


# ---------------------------------------------------------------- the checker goes red

_P0_VIOLATED = {"property": "p0", "verdict": "violated", "trace": ["t1", "t2"]}
_P4_PROVEN = {"property": "p4", "verdict": "proven"}


def _kinds(findings):
    return [f.kind for f in findings]


def test_a_proven_against_a_reference_violation_is_a_finding():
    net = cs.parse_net(SEQ)
    assert _kinds(cs.check(net, _prop(net, "p0"), "enum", "proven", [], _P0_VIOLATED)) == [
        "WRONG PROVEN"
    ]


def test_a_violated_trace_that_does_not_replay_is_a_finding():
    net = cs.parse_net(SEQ)
    p0 = _prop(net, "p0")
    # t2 is not enabled at M0 = {a, z}.
    assert _kinds(cs.check(net, p0, "ic3", "violated", ["t2"], _P0_VIOLATED)) == ["REPLAY FAILS"]
    # Enabled, but the end state {b, z} does not violate DeadlockFree(sinks c).
    assert _kinds(cs.check(net, p0, "ic3", "violated", ["t1"], None)) == ["REPLAY FAILS"]


def test_a_violated_against_a_reference_proof_is_a_finding():
    net = cs.parse_net(SEQ)
    p4 = _prop(net, "p4")
    assert _kinds(cs.check(net, p4, "enum", "violated", ["t1"], _P4_PROVEN)) == ["WRONG VIOLATED"]
    assert _kinds(cs.check(net, p4, "enum", "violated", None, _P4_PROVEN)) == ["WRONG VIOLATED"]
    # A trace that does replay would falsify the reference: reported loudly.
    ref_bad = {"property": "p0", "verdict": "proven"}
    assert _kinds(cs.check(net, _prop(net, "p0"), "enum", "violated", ["t1", "t2"], ref_bad)) == [
        "FALSIFIES THE REFERENCE"
    ]


def test_unknown_and_agreement_are_not_findings():
    net = cs.parse_net(SEQ)
    p0 = _prop(net, "p0")
    assert cs.check(net, p0, "enum", "unknown", [], _P0_VIOLATED) == []
    assert cs.check(net, p0, "enum", "violated", ["t1", "t2"], _P0_VIOLATED) == []
    # Clarification 6: a violation without a trace fails rule 3.
    assert _kinds(cs.check(net, p0, "ic3", "violated", None, _P0_VIOLATED)) == ["UNTRACED VIOLATED"]
    assert cs.check(net, _prop(net, "p1"), "enum", "proven", [], {"verdict": "proven"}) == []


def test_the_default_pass_holds_rules_1_3_and_4_only():
    net = cs.parse_net(SEQ)
    p0, p4 = _prop(net, "p0"), _prop(net, "p4")

    def split(verdict, trace, ref, split_net=False):
        return _kinds(cs.check(net, p4 if ref is _P4_PROVEN else p0, "enum/split", verdict, trace, ref,
                               split_pass=True, split_net=split_net))

    # Rule 2 is off: a violation where the reference proves is a run with an action in
    # flight, which the atomic reference does not have.
    assert split("violated", ["t1", "complete:t1"], _P4_PROVEN, split_net=True) == []
    assert split("violated", None, _P4_PROVEN) == ["UNTRACED VIOLATED"]
    # Rule 1 holds.
    assert split("proven", [], _P0_VIOLATED) == ["WRONG PROVEN"]
    # Rule 3 holds: a trace of a net the split left atomic replays under the reference rule;
    # a split net's trace names complete:<t> steps and is counted instead.
    assert split("violated", ["t2"], _P0_VIOLATED) == ["REPLAY FAILS"]
    assert split("violated", ["t1", "complete:t1"], _P0_VIOLATED, split_net=True) == []
    assert split("unknown", [], _P0_VIOLATED) == []


def test_every_setup_runs_atomically_and_split():
    assert [r.name for r in cs.ALL_ROUTES] == [
        "enum", "smt+lb", "smt-lb", "ic3", "enum/split", "smt+lb/split", "smt-lb/split", "ic3/split",
    ]
    assert all(r.atomic for r in cs.ROUTES) and not any(r.atomic for r in cs.SPLIT_ROUTES)


@pytest.mark.skipif(not lp.HAS_Z3, reason="z3 feature not enabled")
def test_the_split_pass_leaves_the_split_on():
    # u tests b, which t deposits, with an inhibitor: the split pass verifies t in two
    # steps, the atomic pass in one.
    net = cs.parse_net({
        "id": "unit-guard",
        "places": ["a", "b", "q", "r"],
        "marking": {"a": 1, "q": 1},
        "transitions": [
            {"name": "t", "inputs": [{"place": "a", "kind": "one"}],
             "output": {"type": "place", "place": "b"}},
            {"name": "u", "inputs": [{"place": "q", "kind": "one"}], "inhibitors": ["b"],
             "output": {"type": "place", "place": "r"}},
        ],
        "properties": [{"id": "g0", "type": "place-bound", "place": "r", "bound": 1}],
    })
    built = cs.build_net(net)
    prop = _prop(net, "g0")
    split = cs.run_route(built, net, prop, cs.SPLIT_ROUTES[0])
    assert cs.SPLIT_MARK in split.report, split.report
    assert cs.SPLIT_MARK not in cs.run_route(built, net, prop, cs.ROUTES[0]).report


def test_a_property_missing_from_the_expected_file_is_one_stale_finding():
    net = cs.parse_net(SEQ)
    refs = {"p0": _P0_VIOLATED}
    assert cs.stale_findings(net, _prop(net, "p0"), refs) == []
    [finding] = cs.stale_findings(net, _prop(net, "p4"), refs)
    assert finding.kind == "STALE"
    assert "unit-seq/p4: no reference verdict (expected/ is stale)" in finding.detail


def test_a_net_without_an_expected_file_is_a_stale_finding(tmp_path):
    for sub in ("nets", "expected"):
        (tmp_path / sub).mkdir()
    for nid in ("n1", "n2"):
        (tmp_path / "nets" / f"{nid}.json").write_text("{}")
    (tmp_path / "expected" / "n1.json").write_text("{}")
    corpus, _ = cs.load_corpus(tmp_path)
    assert corpus is not None
    assert [f.detail for f in cs.missing_expected_findings(corpus)] == [
        "n2: no expected/n2.json (expected/ is stale)"
    ]
