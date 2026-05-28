"""Sync + async execution facade."""

from __future__ import annotations

from collections.abc import Awaitable, Iterable, Iterator, Mapping
from dataclasses import dataclass
from typing import Any

from . import _libpetri as _ext
from .model import BuiltNet, PlaceLike, _coerce_net, _coerce_place_name


class MarkingView(Mapping[str, tuple[Any, ...]]):
    def __init__(self, data: Mapping[str, Iterable[Any]] | None = None) -> None:
        self._data = {
            place_name: tuple(tokens)
            for place_name, tokens in (data or {}).items()
        }

    def __getitem__(self, place_name: str) -> tuple[Any, ...]:
        return self._data[place_name]

    def __iter__(self) -> Iterator[str]:
        return iter(self._data)

    def __len__(self) -> int:
        return len(self._data)

    def places(self) -> tuple[str, ...]:
        return tuple(self._data)

    def tokens(self, place: PlaceLike) -> tuple[Any, ...]:
        return self._data.get(_coerce_place_name(place), ())

    def count(self, place: PlaceLike) -> int:
        return len(self.tokens(place))

    def has_tokens(self, place: PlaceLike) -> bool:
        return self.count(place) > 0

    def first(self, place: PlaceLike, default: Any = None) -> Any:
        tokens = self.tokens(place)
        return tokens[0] if tokens else default

    def to_dict(self) -> dict[str, list[Any]]:
        return {
            place_name: list(tokens)
            for place_name, tokens in self._data.items()
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
        return initial.to_dict()
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

    def run_sync(self, *, initial=None, options=None) -> MarkingView:
        result = self._inner.run_sync(
            _normalize_initial(initial),
            _native_options(options),
        )
        return MarkingView(result)

    def start_async(self, *, initial=None, options=None):
        if not _ext.HAS_TOKIO:
            raise ImportError(
                "libpetri wheel was built without tokio async support"
            )
        native_handle, native_awaitable = self._inner.run_async(
            _normalize_initial(initial),
            _native_options(options),
        )

        async def _wait_for_result() -> MarkingView:
            return MarkingView(await native_awaitable)

        return ExecutorHandle(native_handle), _wait_for_result()

    async def run_async(self, *, initial=None, options=None) -> MarkingView:
        _handle, awaitable = self.start_async(initial=initial, options=options)
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


def run_sync(target, *, initial=None, options=None) -> MarkingView:
    return _ensure_compiled(target).run_sync(initial=initial, options=options)


def start_async(target, *, initial=None, options=None):
    return _ensure_compiled(target).start_async(initial=initial, options=options)


async def run_async(target, *, initial=None, options=None) -> MarkingView:
    return await _ensure_compiled(target).run_async(initial=initial, options=options)


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
