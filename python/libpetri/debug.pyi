"""Type stubs for libpetri.debug."""

from __future__ import annotations

from collections.abc import Callable, Mapping
from typing import Any, TypeAlias

from . import _libpetri as _ext
from .model import BuiltNet

HAS_DEBUG: bool

def require_debug() -> None: ...

SessionSummary: TypeAlias = _ext.SessionSummary

class DebugProtocolHandler:
    def __init__(self) -> None: ...
    def register_session(
        self,
        session_id: str,
        net: BuiltNet,
        *,
        tags: Mapping[str, str] | None = ...,
    ) -> None: ...
    def complete_session(self, session_id: str) -> None: ...
    def remove_session(self, session_id: str) -> None: ...
    def list_sessions(
        self,
        *,
        limit: int = ...,
        active_only: bool | None = ...,
        tag_filter: Mapping[str, str] | None = ...,
    ) -> list[SessionSummary]: ...
    def connect(
        self,
        client_id: str,
        callback: Callable[[dict[str, Any]], None],
    ) -> None: ...
    def disconnect(self, client_id: str) -> None: ...
    def send(self, client_id: str, command: Mapping[str, Any]) -> None: ...
    def handle_command(self, client_id: str, command: Mapping[str, Any]) -> None: ...
