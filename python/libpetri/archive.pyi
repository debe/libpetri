"""Type stubs for libpetri.archive."""

from __future__ import annotations

import os
from typing import Any

from .events import InMemoryEventStore, NetEvent
from .model import BuiltNet

class ComputedState:
    @property
    def marking(self) -> dict[str, int]: ...
    @property
    def enabled_transitions(self) -> list[str]: ...
    @property
    def in_flight_transitions(self) -> list[str]: ...

class MarkingCache:
    def __init__(self) -> None: ...
    def compute_at(
        self, store: InMemoryEventStore, event_index: int
    ) -> ComputedState: ...
    def invalidate(self) -> None: ...

class SessionArchive:
    @property
    def version(self) -> int: ...
    @property
    def session_id(self) -> str: ...
    @property
    def net_name(self) -> str: ...
    @property
    def event_count(self) -> int: ...
    @property
    def dot_diagram(self) -> str: ...
    @property
    def start_time(self) -> str: ...
    @property
    def end_time(self) -> str | None: ...
    @property
    def tags(self) -> dict[str, str]: ...
    def events(self) -> list[NetEvent]: ...

class SessionArchiveWriter:
    @classmethod
    def write_from_store(
        cls,
        path: str | os.PathLike[str],
        *,
        session_id: str,
        net: BuiltNet,
        store: InMemoryEventStore,
        tags: dict[str, str] | None = ...,
    ) -> None: ...

class SessionArchiveReader:
    @classmethod
    def read(cls, path: str | os.PathLike[str]) -> SessionArchive: ...
