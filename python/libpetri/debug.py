"""Debug protocol facade (guarded by HAS_DEBUG)."""

from __future__ import annotations

import json
from collections.abc import Callable, Mapping
from typing import Any

from . import _libpetri as _ext
from .model import BuiltNet, _coerce_net

HAS_DEBUG = bool(_ext.HAS_DEBUG)


def require_debug() -> None:
    if not HAS_DEBUG:
        raise ImportError("libpetri wheel was built without debug support")


if HAS_DEBUG:
    SessionSummary = _ext.SessionSummary

    class DebugProtocolHandler:
        def __init__(self) -> None:
            self._inner = _ext.DebugProtocolHandler()

        def register_session(
            self,
            session_id: str,
            net: BuiltNet,
            *,
            tags: Mapping[str, str] | None = None,
        ) -> None:
            self._inner.register_session(
                session_id,
                _coerce_net(net),
                dict(tags) if tags else None,
            )

        def complete_session(self, session_id: str) -> None:
            self._inner.complete_session(session_id)

        def remove_session(self, session_id: str) -> None:
            self._inner.remove_session(session_id)

        def list_sessions(
            self,
            *,
            limit: int = 50,
            active_only: bool | None = None,
            tag_filter: Mapping[str, str] | None = None,
        ) -> "list[SessionSummary]":
            return self._inner.list_sessions(
                limit=limit,
                active_only=active_only,
                tag_filter=dict(tag_filter) if tag_filter else None,
            )

        def connect(
            self,
            client_id: str,
            callback: Callable[[dict[str, Any]], None],
        ) -> None:
            def _sink(message: str) -> None:
                callback(json.loads(message))

            self._inner.client_connected(client_id, _sink)

        def disconnect(self, client_id: str) -> None:
            self._inner.client_disconnected(client_id)

        def send(self, client_id: str, command: Mapping[str, Any]) -> None:
            self._inner.handle_command(client_id, json.dumps(dict(command)))

        handle_command = send

else:

    class SessionSummary:
        def __init__(self, *_args, **_kwargs) -> None:
            require_debug()

    class DebugProtocolHandler:
        def __init__(self, *_args, **_kwargs) -> None:
            require_debug()


__all__ = ["DebugProtocolHandler", "HAS_DEBUG", "SessionSummary", "require_debug"]
