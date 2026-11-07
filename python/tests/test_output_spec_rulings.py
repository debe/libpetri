"""Executor-level acceptance criteria of the output-spec rulings, through the binding.

- [CORE-034] AC4: a reset arc on an output place neither adds a deposit nor removes one.
- [CORE-036] AC2/AC3: deposits compare per place; two tokens into one claimed place
  conform, and the order of the writes does not matter.
- [CONC-026] AC4-AC6: ``ExecutorOptions(skip_output_validation=True)`` covers a
  single-leaf spec, a partial ``And`` write and the [IO-016] AC4 warning, but not a
  write to an undeclared place ([CORE-063]) and not the build-time [IO-012] check.
"""

from __future__ import annotations

import pytest

import libpetri as lp


@pytest.mark.parametrize("with_reset", [False, True])
@pytest.mark.parametrize("write_b", [True, False])
def test_core_034_ac4_a_reset_arc_changes_no_deposit(with_reset: bool, write_b: bool) -> None:
    a, b, c = lp.Place("a"), lp.Place("b"), lp.Place("c")

    def act(ctx: lp.TransitionContext) -> None:
        ctx.input("a")
        ctx.output("b" if write_b else "c", 7)

    builder = lp.Transition("t").input(lp.one(a)).output(lp.xor(b, c)).action(act)
    if with_reset:
        builder = builder.reset(lp.reset(b))
    net = lp.Net("N").transition(builder.build()).build()
    marking = lp.run_sync(net, initial={a: [1], b: [1, 2]})
    assert marking.count(a) == 0
    assert marking.count(b) == (0 if with_reset else 2) + (1 if write_b else 0)
    assert marking.count(c) == (0 if write_b else 1)


@pytest.mark.parametrize("order", [("b", "b", "c"), ("c", "b", "b")])
def test_core_036_ac2_ac3_deposits_compare_per_place(order: tuple[str, ...]) -> None:
    a, b, c = lp.Place("a"), lp.Place("b"), lp.Place("c")

    def act(ctx: lp.TransitionContext) -> None:
        ctx.input("a")
        for p in order:
            ctx.output(p, 1)

    net = (
        lp.Net("N")
        .transition(lp.Transition("t").input(lp.one(a)).output(lp.and_(b, c)).action(act).build())
        .build()
    )
    marking = lp.run_sync(net, initial={a: [1]})
    assert marking.count(a) == 0
    assert marking.count(b) == 2
    assert marking.count(c) == 1


def test_conc_026_skip_covers_leaf_and_warning_but_not_undeclared_write() -> None:
    go = {n: lp.Place(n) for n in ("GO1", "GO2", "GO3", "GO4")}
    p, a, b, many = lp.Place("P"), lp.Place("A"), lp.Place("B"), lp.Place("MANY")

    def silent(ctx: lp.TransitionContext) -> None:
        ctx.input("GO1")

    def half(ctx: lp.TransitionContext) -> None:
        ctx.input("GO2")
        ctx.output("A", 1)

    def twice(ctx: lp.TransitionContext) -> None:
        ctx.input("GO3")
        ctx.output("MANY", 1)
        ctx.output("MANY", 2)

    def undeclared(ctx: lp.TransitionContext) -> None:
        ctx.input("GO4")
        ctx.output("A", 9)

    net = (
        lp.Net("skip")
        .transition(lp.Transition("silent").input(lp.one(go["GO1"])).output(lp.out(p)).action(silent).build())
        .transition(lp.Transition("half").input(lp.one(go["GO2"])).output(lp.and_(a, b)).action(half).build())
        .transition(lp.Transition("twice").input(lp.one(go["GO3"])).output(lp.out(many)).action(twice).build())
        .transition(
            lp.Transition("undeclared").input(lp.one(go["GO4"])).output(lp.out(p)).action(undeclared).build()
        )
        .build()
    )
    store = lp.InMemoryEventStore()
    marking = lp.run_sync(
        net,
        initial={g: [0] for g in go.values()},
        options=lp.ExecutorOptions(skip_output_validation=True),
        event_store=store,
    )
    events = list(store.events())
    assert marking.count(p) == 0, "the leaf is not checked: nothing written, nothing deposited"
    assert marking.count(a) == 1, "the partial And write is deposited"
    assert marking.count(b) == 0
    assert marking.count(many) == 2
    assert [e for e in events if e.type == "LogMessage"] == [], "no IO-016 warning under the skip"
    failed = [e.payload()["transition_name"] for e in events if e.type == "TransitionFailed"]
    assert failed == ["undeclared"], "only the undeclared write fails (CORE-063)"


def test_conc_026_ac6_the_skip_does_not_reach_the_build_time_check() -> None:
    p = lp.Place("P")
    with pytest.raises(lp.StructureError, match="is ambiguous: output branches 0 and 1"):
        lp.Transition("t").input(lp.one(lp.Place("GO"))).output(lp.xor(p, p)).build()
