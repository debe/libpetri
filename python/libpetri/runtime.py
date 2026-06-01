"""Sync + async execution facade."""

from __future__ import annotations

import time
from collections.abc import Awaitable, Iterable, Iterator, Mapping
from dataclasses import dataclass
from typing import Any

from . import _libpetri as _ext
from .model import BuiltNet, PlaceLike, _coerce_net, _coerce_place_name


def _now_ms() -> int:
    return int(time.time() * 1000)


class MarkingView(Mapping[str, tuple[Any, ...]]):
    """Read-only marking view with per-token `created_at` timestamps preserved.

    Constructor accepts both forms — auto-detected by element shape:

    - **Legacy value-only:** ``{place: [v1, v2, ...]}``. Each token's
      timestamp is filled with the current wall clock (`time.time()`).
      Useful for callers building an `initial=` argument from plain values.
    - **Structured snapshot:** ``{place: [{"value": v, "created_at": ms},
      ...]}``. Timestamps are preserved verbatim. This is the form executor
      runs return as of 2.7.0 and the form `snapshot()` emits, so passing a
      previous run's view back as `initial=` does a timestamp-faithful
      restore (deadlines, windows, and the `created_at`-driven freshness
      patterns survive the round-trip).

    Iteration, ``view[place]``, and `tokens(place)` all yield the
    **value-only** tuple — backward-compatible with pre-2.7.0 callers.
    Use `timestamps(place)` or `snapshot()` to reach the `created_at` data.
    """

    def __init__(
        self,
        data: Mapping[str, Iterable[Any]] | None = None,
    ) -> None:
        if isinstance(data, MarkingView):
            self._values = dict(data._values)
            self._created_at = dict(data._created_at)
            return
        self._values: dict[str, tuple[Any, ...]] = {}
        self._created_at: dict[str, tuple[int, ...]] = {}
        if data is None:
            return
        fallback_ts: int | None = None
        for place_name, tokens in data.items():
            values_list: list[Any] = []
            ts_list: list[int] = []
            for token in tokens:
                if (
                    isinstance(token, Mapping)
                    and "value" in token
                    and "created_at" in token
                ):
                    values_list.append(token["value"])
                    ts_list.append(int(token["created_at"]))
                else:
                    if fallback_ts is None:
                        fallback_ts = _now_ms()
                    values_list.append(token)
                    ts_list.append(fallback_ts)
            self._values[place_name] = tuple(values_list)
            self._created_at[place_name] = tuple(ts_list)

    @classmethod
    def from_snapshot(
        cls,
        data: Mapping[str, Iterable[Mapping[str, Any]]],
    ) -> "MarkingView":
        """Explicit constructor for the structured-snapshot form.

        Equivalent to `MarkingView(data)` (the constructor auto-detects), but
        the named entry point makes restore intent obvious at call sites.
        """
        return cls(data)

    def __getitem__(self, place_name: str) -> tuple[Any, ...]:
        return self._values[place_name]

    def __iter__(self) -> Iterator[str]:
        return iter(self._values)

    def __len__(self) -> int:
        return len(self._values)

    def places(self) -> tuple[str, ...]:
        return tuple(self._values)

    def tokens(self, place: PlaceLike) -> tuple[Any, ...]:
        return self._values.get(_coerce_place_name(place), ())

    def timestamps(self, place: PlaceLike) -> tuple[int, ...]:
        """Per-token `created_at` (ms since epoch) for `place`, in token order."""
        return self._created_at.get(_coerce_place_name(place), ())

    def count(self, place: PlaceLike) -> int:
        return len(self.tokens(place))

    def has_tokens(self, place: PlaceLike) -> bool:
        return self.count(place) > 0

    def first(self, place: PlaceLike, default: Any = None) -> Any:
        tokens = self.tokens(place)
        return tokens[0] if tokens else default

    def to_dict(self) -> dict[str, list[Any]]:
        """Legacy value-only projection — drops timestamps.

        Use `snapshot()` for the timestamp-preserving structured form.
        """
        return {
            place_name: list(tokens)
            for place_name, tokens in self._values.items()
        }

    def snapshot(self) -> dict[str, list[dict[str, Any]]]:
        """Structured snapshot with per-token `created_at` preserved.

        Round-trip via `MarkingView.from_snapshot(view.snapshot())` reproduces
        the marking exactly. Pass this (or the view itself) as `initial=` to
        `run_sync`/`run_async` to resume a timed net without losing clocks.
        """
        return {
            place: [
                {"value": value, "created_at": ts}
                for value, ts in zip(
                    self._values[place], self._created_at[place], strict=True
                )
            ]
            for place in self._values
        }

    def __repr__(self) -> str:
        return f"MarkingView({self.to_dict()!r})"


@dataclass(slots=True, frozen=True)
class ExecutorOptions:
    environment_places: tuple[PlaceLike, ...] = ()
    skip_output_validation: bool = False

    def native(self) -> _ext.ExecutorOptions:
        return _ext.ExecutorOptions(
            environment_places=[
                _coerce_place_name(p) for p in self.environment_places
            ],
            skip_output_validation=self.skip_output_validation,
        )


def _normalize_initial(initial):
    if initial is None:
        return None
    if isinstance(initial, MarkingView):
        # Use the structured form so per-token `created_at` survives the
        # round-trip back into the executor (required for timed nets).
        return initial.snapshot()
    return dict(initial)


def _native_options(options):
    if options is None:
        return None
    if isinstance(options, _ext.ExecutorOptions):
        return options
    if isinstance(options, ExecutorOptions):
        return options.native()
    raise TypeError("options must be ExecutorOptions or _libpetri.ExecutorOptions")


class CompiledNet:
    def __init__(self, target) -> None:
        if isinstance(target, _ext.CompiledNet):
            self._inner = target
        else:
            self._inner = _ext.CompiledNet(_coerce_net(target))

    @classmethod
    def _from_native(cls, inner: _ext.CompiledNet) -> "CompiledNet":
        instance = cls.__new__(cls)
        instance._inner = inner
        return instance

    @property
    def name(self) -> str:
        return self._inner.name

    def run_sync(
        self, *, initial=None, options=None, event_store=None
    ) -> MarkingView:
        result = self._inner.run_sync(
            _normalize_initial(initial),
            _native_options(options),
            event_store,
        )
        return MarkingView(result)

    def start_async(self, *, initial=None, options=None, event_store=None):
        if not _ext.HAS_TOKIO:
            raise ImportError(
                "libpetri wheel was built without tokio async support"
            )
        native_handle, native_awaitable = self._inner.run_async(
            _normalize_initial(initial),
            _native_options(options),
            event_store,
        )

        async def _wait_for_result() -> MarkingView:
            return MarkingView(await native_awaitable)

        return ExecutorHandle(native_handle), _wait_for_result()

    async def run_async(
        self, *, initial=None, options=None, event_store=None
    ) -> MarkingView:
        _handle, awaitable = self.start_async(
            initial=initial, options=options, event_store=event_store
        )
        return await awaitable


if _ext.HAS_TOKIO:

    class ExecutorHandle:
        def __init__(self, inner: _ext.ExecutorHandle) -> None:
            self._inner = inner

        def inject(self, place: PlaceLike, value: Any) -> bool:
            return self._inner.inject(_coerce_place_name(place), value)

        def drain(self) -> bool:
            return self._inner.drain()

        def close(self) -> bool:
            return self._inner.close()

        @property
        def drained(self) -> bool:
            return self._inner.drained

        async def snapshot(self) -> MarkingView:
            """Request a mid-execution marking snapshot.

            The executor materializes its current marking and returns it as a
            `MarkingView` with per-token `created_at` preserved. Does not
            affect lifecycle — the executor keeps running. Use this for
            checkpoint-saver patterns (e.g. periodic persistence).

            Raises `RuntimeError` if the handle is drained, closed, or the
            executor has already exited.
            """
            data = await self._inner.snapshot()
            return MarkingView.from_snapshot(data)

else:

    class ExecutorHandle:
        def __init__(self, *_args, **_kwargs) -> None:
            raise ImportError(
                "libpetri wheel was built without tokio async support"
            )


ExecutionTarget = BuiltNet | CompiledNet | _ext.CompiledNet


def _ensure_compiled(target) -> CompiledNet:
    if isinstance(target, CompiledNet):
        return target
    if isinstance(target, _ext.CompiledNet):
        return CompiledNet._from_native(target)
    return CompiledNet(_coerce_net(target))


def compile(net: BuiltNet) -> CompiledNet:  # noqa: A001 — intentional shadow on `compile`
    return CompiledNet(_coerce_net(net))


def run_sync(target, *, initial=None, options=None, event_store=None) -> MarkingView:
    return _ensure_compiled(target).run_sync(
        initial=initial, options=options, event_store=event_store
    )


def start_async(target, *, initial=None, options=None, event_store=None):
    return _ensure_compiled(target).start_async(
        initial=initial, options=options, event_store=event_store
    )


async def run_async(
    target, *, initial=None, options=None, event_store=None
) -> MarkingView:
    return await _ensure_compiled(target).run_async(
        initial=initial, options=options, event_store=event_store
    )


__all__ = [
    "CompiledNet",
    "ExecutionTarget",
    "ExecutorHandle",
    "ExecutorOptions",
    "MarkingView",
    "compile",
    "run_async",
    "run_sync",
    "start_async",
]
