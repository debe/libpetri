"""Asyncio helpers for libpetri async transition actions.

Libpetri drives Python ``async def`` actions from a tokio worker thread that
has no asyncio event loop installed. Awaits inside the action coroutine are
resolved against the asyncio loop that was running when ``run_async`` /
``start_async`` was called, but *synchronous* asyncio calls (``gather``,
``create_task``, ``get_running_loop``, ``ensure_future``, ``wait_for``,
``as_completed``) reach for the current thread's loop and raise
``RuntimeError: no running event loop``.

For parallel work inside an action, prefer **structural fan-out** — fire N
transitions in parallel from a single FanOut. The marking is the join.
``action_gather`` exists for the case where you genuinely need to await N
Python coroutines side-by-side without putting that fan-out into the net
structure (e.g. dispatching to N tools via ``BaseTool._arun``).
"""

from __future__ import annotations

import asyncio
from collections.abc import Awaitable, Coroutine
from typing import Any, TypeVar

from . import _libpetri

__all__ = ["action_gather", "action_to_thread"]

_T = TypeVar("_T")


def action_gather(*coros: Coroutine[Any, Any, Any]) -> Awaitable[list[Any]]:
    """Parallel ``asyncio.gather`` for libpetri async actions.

    Schedules ``asyncio.gather(*coros)`` on the asyncio loop captured by the
    most recent ``run_async`` / ``start_async`` call, where the synchronous
    ``gather`` API is legal. Returns an awaitable that resolves to the list
    of results in input order. N concurrent 300ms sleeps complete in ~300ms
    — real parallelism, not sequential awaits.

    Raises ``RuntimeError`` if called outside an in-flight
    ``run_async`` / ``start_async`` (no loop has been captured yet).
    """
    loop = _libpetri.captured_event_loop()

    async def _inner() -> list[Any]:
        return await asyncio.gather(*coros)

    cf = asyncio.run_coroutine_threadsafe(_inner(), loop)
    return asyncio.wrap_future(cf, loop=loop)


def action_to_thread(fn, /, *args: Any, **kwargs: Any) -> Awaitable[Any]:
    """``asyncio.to_thread`` equivalent that works inside libpetri actions.

    Schedules ``asyncio.to_thread(fn, *args, **kwargs)`` on the captured
    loop and returns an awaitable on the result. Use for blocking sync
    work (file I/O, blocking SDK calls) inside an async action.
    """
    loop = _libpetri.captured_event_loop()

    async def _inner() -> Any:
        return await asyncio.to_thread(fn, *args, **kwargs)

    cf = asyncio.run_coroutine_threadsafe(_inner(), loop)
    return asyncio.wrap_future(cf, loop=loop)
