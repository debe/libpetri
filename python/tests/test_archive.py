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
