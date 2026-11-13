"""Session Archive v3 — write, read, cross-implementation round-trip."""

from __future__ import annotations

import pytest

import libpetri as lp

pytestmark = pytest.mark.skipif(
    not lp.HAS_ARCHIVE,
    reason="wheel built without `archive` feature",
)


def _chain_net() -> tuple[lp.Place, lp.Place, lp.BuiltNet]:
    p_in = lp.Place("p_in")
    p_out = lp.Place("p_out")
    net = (
        lp.Net("archive-net")
        .transition(
            lp.Transition("t1")
            .input(lp.one(p_in))
            .output(lp.out(p_out))
            .action(lp.fork)
            .build()
        )
        .build()
    )
    return p_in, p_out, net


def test_write_and_read_v3_archive(tmp_path) -> None:
    p_in, _p_out, net = _chain_net()
    store = lp.InMemoryEventStore()
    lp.run_sync(net, initial={p_in: ["v"]}, event_store=store)

    archive_path = tmp_path / "session.lpa"
    lp.SessionArchiveWriter.write_from_store(
        archive_path,
        session_id="test-1",
        net=net,
        store=store,
        tags={"source": "test"},
    )
    assert archive_path.exists()
    assert archive_path.stat().st_size > 0

    archive = lp.SessionArchiveReader.read(archive_path)
    assert archive.version == 3
    assert archive.session_id == "test-1"
    assert archive.net_name == "archive-net"
    assert archive.event_count == len(store)
    assert archive.tags == {"source": "test"}
    assert "digraph" in archive.dot_diagram


def test_archive_events_roundtrip_preserves_types(tmp_path) -> None:
    p_in, _p_out, net = _chain_net()
    store = lp.InMemoryEventStore()
    lp.run_sync(net, initial={p_in: ["v"]}, event_store=store)

    archive_path = tmp_path / "roundtrip.lpa"
    lp.SessionArchiveWriter.write_from_store(
        archive_path,
        session_id="rt",
        net=net,
        store=store,
    )
    archive = lp.SessionArchiveReader.read(archive_path)

    original_counts = store.counters()
    restored_events = archive.events()
    restored_counts: dict[str, int] = {}
    for ev in restored_events:
        restored_counts[ev.type] = restored_counts.get(ev.type, 0) + 1

    # Each event-type histogram bin must match across the round-trip.
    for type_name, count in original_counts.items():
        assert restored_counts.get(type_name, 0) == count, (
            f"event type {type_name!r} count differs after archive roundtrip: "
            f"{restored_counts.get(type_name, 0)} != {count}"
        )


def test_archive_preserves_event_timestamps(tmp_path) -> None:
    p_in, _p_out, net = _chain_net()
    store = lp.InMemoryEventStore()
    lp.run_sync(net, initial={p_in: ["v"]}, event_store=store)

    original = [ev.timestamp for ev in store.events()]
    archive_path = tmp_path / "ts.lpa"
    lp.SessionArchiveWriter.write_from_store(
        archive_path, session_id="ts", net=net, store=store
    )
    restored = [ev.timestamp for ev in lp.SessionArchiveReader.read(archive_path).events()]
    assert sorted(original) == sorted(restored)


def test_reader_rejects_corrupt_file(tmp_path) -> None:
    bad = tmp_path / "bad.lpa"
    bad.write_bytes(b"not a gzip archive")
    with pytest.raises(ValueError):
        lp.SessionArchiveReader.read(bad)


def test_reader_raises_io_error_for_missing_file(tmp_path) -> None:
    with pytest.raises(OSError):
        lp.SessionArchiveReader.read(tmp_path / "does-not-exist.lpa")


def test_archive_repr_includes_event_count(tmp_path) -> None:
    p_in, _p_out, net = _chain_net()
    store = lp.InMemoryEventStore()
    lp.run_sync(net, initial={p_in: ["v"]}, event_store=store)
    path = tmp_path / "repr.lpa"
    lp.SessionArchiveWriter.write_from_store(
        path, session_id="r", net=net, store=store
    )
    archive = lp.SessionArchiveReader.read(path)
    assert "SessionArchive" in repr(archive)
    assert "version=3" in repr(archive)


def test_archive_from_empty_store(tmp_path) -> None:
    """An archive written from a store with no events round-trips cleanly."""
    _p_in, _p_out, net = _chain_net()
    store = lp.InMemoryEventStore()  # never executed — zero events
    path = tmp_path / "empty.lpa"
    lp.SessionArchiveWriter.write_from_store(
        path, session_id="empty", net=net, store=store
    )
    archive = lp.SessionArchiveReader.read(path)
    assert archive.event_count == 0
    assert archive.events() == []
    assert archive.session_id == "empty"
    assert "digraph" in archive.dot_diagram


def test_archive_time_accessors_typed(tmp_path) -> None:
    """`start_time` is always present; `end_time` maps Option<String> -> str | None."""
    p_in, _p_out, net = _chain_net()
    store = lp.InMemoryEventStore()
    lp.run_sync(net, initial={p_in: ["v"]}, event_store=store)
    path = tmp_path / "times.lpa"
    lp.SessionArchiveWriter.write_from_store(
        path, session_id="t", net=net, store=store
    )
    archive = lp.SessionArchiveReader.read(path)
    assert isinstance(archive.start_time, str)
    assert archive.end_time is None or isinstance(archive.end_time, str)


def test_archive_tags_come_back_in_ascending_key_order(tmp_path) -> None:
    """A Python dict is an ordered medium: tags read out of a per-process
    seeded hash map would differ run to run for one and the same archive.
    Twelve scrambled keys, so a randomised container passes one time in 12!.
    ``list(...)`` because dict equality ignores order."""
    p_in, _p_out, net = _chain_net()
    store = lp.InMemoryEventStore()
    lp.run_sync(net, initial={p_in: ["v"]}, event_store=store)
    tags = {k: f"v-{k}" for k in ["k07", "k11", "k02", "k09", "k00", "k05", "k10", "k03", "k08", "k01", "k06", "k04"]}

    archive_path = tmp_path / "tagged.lpa"
    lp.SessionArchiveWriter.write_from_store(
        archive_path, session_id="tagged", net=net, store=store, tags=tags
    )
    archive = lp.SessionArchiveReader.read(archive_path)
    assert archive.tags == tags
    assert list(archive.tags) == sorted(tags)


# ---------------------------------------------------------------- EVT-025


def _read_header(path) -> dict:
    """The archive's header JSON: gunzip, then one big-endian length-prefixed frame."""
    import gzip
    import json

    raw = gzip.decompress(path.read_bytes())
    length = int.from_bytes(raw[:4], "big")
    return json.loads(raw[4 : 4 + length])


def test_evt_025_archive_keeps_every_event_of_a_store_over_10000(tmp_path) -> None:
    """EVT-025: one record for each event of the store's snapshot, however many."""
    p_in, _p_out, net = _chain_net()
    run = lp.InMemoryEventStore()
    lp.run_sync(net, initial={p_in: ["v"]}, event_store=run)
    run_events = run.events()

    store = lp.InMemoryEventStore()
    while len(store) <= 10_000:
        for ev in run_events:
            store.append(ev)

    path = tmp_path / "big.lpa"
    lp.SessionArchiveWriter.write_from_store(path, session_id="big", net=net, store=store)
    archive = lp.SessionArchiveReader.read(path)
    assert archive.event_count == len(store)
    restored = archive.events()
    assert len(restored) == len(store)
    assert [ev.type for ev in restored[: len(run_events)]] == [ev.type for ev in run_events]


def test_evt_025_ac1_writes_header_versions_1_2_and_3(tmp_path) -> None:
    """EVT-025 AC1: a writer for each header version 1, 2 and 3."""
    p_in, _p_out, net = _chain_net()
    store = lp.InMemoryEventStore()
    lp.run_sync(net, initial={p_in: ["v"]}, event_store=store)
    tags = {"source": "test"}

    writers = {
        1: lambda path: lp.SessionArchiveWriter.write_v1(
            path, session_id="s", net=net, store=store
        ),
        2: lambda path: lp.SessionArchiveWriter.write_v2(
            path, session_id="s", net=net, store=store, tags=tags
        ),
        3: lambda path: lp.SessionArchiveWriter.write_from_store(
            path, session_id="s", net=net, store=store, tags=tags
        ),
    }
    for version, write in writers.items():
        path = tmp_path / f"v{version}.lpa"
        write(path)
        archive = lp.SessionArchiveReader.read(path)
        assert archive.version == version
        assert _read_header(path)["version"] == version
        assert archive.session_id == "s"
        assert archive.event_count == len(store)
        assert len(archive.events()) == len(store)
        assert archive.tags == ({} if version == 1 else tags)


def test_evt_025_two_archives_of_one_empty_session_are_identical(tmp_path) -> None:
    """EVT-025: two archives of identical run data are identical; an empty store
    carries no time, so the writer must not stamp one from the wall clock."""
    import time

    _p_in, _p_out, net = _chain_net()
    store = lp.InMemoryEventStore()
    writers = [
        lp.SessionArchiveWriter.write_v1,
        lp.SessionArchiveWriter.write_v2,
        lp.SessionArchiveWriter.write_from_store,
    ]
    for i, write in enumerate(writers):
        first = tmp_path / f"empty-{i}-a.lpa"
        second = tmp_path / f"empty-{i}-b.lpa"
        write(first, session_id="empty", net=net, store=store)
        # Let the millisecond clock advance, so a clock-stamped header differs.
        before = time.time_ns() // 1_000_000
        while time.time_ns() // 1_000_000 <= before:
            pass
        write(second, session_id="empty", net=net, store=store)
        assert first.read_bytes() == second.read_bytes()


def test_evt_025_archive_header_structure_lists_the_nets_places_and_transitions(
    tmp_path,
) -> None:
    """EVT-025: the header carries the session's own fields, and the session of a
    Python archive is the net it is given: ``structure`` names its places and
    transitions."""
    p_in, _p_out, net = _chain_net()
    store = lp.InMemoryEventStore()
    lp.run_sync(net, initial={p_in: ["v"]}, event_store=store)

    path = tmp_path / "structure.lpa"
    lp.SessionArchiveWriter.write_from_store(path, session_id="st", net=net, store=store)
    structure = _read_header(path)["structure"]
    assert sorted(p["name"] for p in structure["places"]) == ["p_in", "p_out"]
    assert [t["name"] for t in structure["transitions"]] == ["t1"]
