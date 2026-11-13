"""DOT export of names whose cluster key holds an empty ``/``-segment.

**EXP-016 / EXP-017** (ruling D46 (a)): a node named ``a//x`` has the cluster
key ``a/``, ``/a/p`` has ``/a`` and ``http://host/x`` has ``http://host``. Each
key opens its key chain (every non-empty ``/``-prefix, then the key itself), so
the export draws ``a > a/``, ``/a`` and ``http: > http:/ > http://host`` instead
of panicking in the Rust exporter the binding calls.
"""

from __future__ import annotations

import pytest

import libpetri as lp


def _empty_segment_net() -> tuple[lp.Place, lp.BuiltNet]:
    lead, web = lp.Place("/a/p"), lp.Place("http://host/x")
    net = (
        lp.Net("EmptySegments")
        .transition(
            lp.Transition("a//x")
            .input(lp.one(lead))
            .output(lp.out(web))
            .action(lp.fork)
            .build()
        )
        .build()
    )
    return lead, net


def test_exp_016_empty_segment_cluster_key_exports_without_panic() -> None:
    _lead, net = _empty_segment_net()

    dot = lp.dot_export(net)

    assert 'compound="true"' in dot
    assert "subgraph cluster_a {" in dot
    assert "subgraph cluster_a_ {" in dot
    assert "subgraph cluster__a {" in dot
    assert "subgraph cluster_http___host {" in dot


@pytest.mark.skipif(not lp.HAS_ARCHIVE, reason="wheel built without `archive` feature")
def test_exp_016_empty_segment_cluster_key_archives_without_panic(tmp_path) -> None:
    """The archive writer embeds the same DOT export (EXP-016)."""
    lead, net = _empty_segment_net()
    store = lp.InMemoryEventStore()
    lp.run_sync(net, initial={lead: ["v"]}, event_store=store)

    path = tmp_path / "empty-segments.lpa"
    lp.SessionArchiveWriter.write_from_store(path, session_id="s", net=net, store=store)

    assert "subgraph cluster_a_ {" in lp.SessionArchiveReader.read(path).dot_diagram
