"""Sync + async execution facade."""

from __future__ import annotations

import operator
import time
from collections.abc import Awaitable, Iterable, Iterator, Mapping
from dataclasses import dataclass
from typing import Any

from . import _libpetri as _ext
from .model import BuiltNet, PlaceLike, _coerce_net, _coerce_place_name


def _now_ms() -> int:
    return int(time.time() * 1000)


_CREATED_AT_LIMIT = 2**64  # `Token.created_at` is a u64 on the Rust side


def _coerce_created_at(raw: Any) -> int:
    """Validates a snapshot token's `created_at` — never alters it.

    The same rule as the binding's `marking_from_python`, so a dict means the
    same thing whether or not it passes through a `MarkingView` first
    ([CORE-073] AC#9): an integer (anything with ``__index__``, so numpy
    scalars count) or an integral float (JSON pipelines produce
    ``1700000000000.0``), in ``0 <= ms < 2**64``. ``TypeError`` for a value
    that is not a number of milliseconds at all, ``ValueError`` for one that
    is but cannot be a timestamp.
    """
    if isinstance(raw, bool):
        raise TypeError(
            f"snapshot token 'created_at' must be an int (ms since epoch), got {raw!r}"
        )
    if isinstance(raw, float):
        if not raw.is_integer():  # also False for nan / inf
            raise ValueError(
                "snapshot token 'created_at' must be a whole number of "
                f"milliseconds, got {raw!r}"
            )
        value = int(raw)
    else:
        try:
            value = operator.index(raw)
        except TypeError:
            raise TypeError(
                "snapshot token 'created_at' must be an int (ms since epoch), "
                f"got {raw!r}"
            ) from None
    if not 0 <= value < _CREATED_AT_LIMIT:
        raise ValueError(
            "snapshot token 'created_at' must be a non-negative int that fits "
            f"in 64 bits (ms since epoch), got {raw!r}"
        )
    return value


def _reject_snapshot_result(value: Any, where: str) -> None:
    """A `SnapshotResult` is not a marking. Unwrapping it silently would skip
    the one check it exists to force ([ENV-014] AC5), so every entry point
    that takes a marking refuses it and says what to write instead — rather
    than failing later with "'SnapshotResult' object is not iterable"."""
    if isinstance(value, SnapshotResult):
        raise TypeError(
            f"{where} takes a marking, not a SnapshotResult: pass "
            "`result.marking` — after checking `result.is_restore_point` "
            "(a snapshot taken with work in flight is an observation, not a "
            "restore point; [ENV-014])"
        )


class MarkingView(Mapping[str, tuple[Any, ...]]):
    """Read-only marking view with per-token `created_at` timestamps preserved.

    Constructor accepts both forms — auto-detected by element shape:

    - **Legacy value-only:** ``{place: [v1, v2, ...]}``. Each token's
      timestamp is filled with the current wall clock (`time.time()`).
      Useful for callers building an `initial=` argument from plain values.
    - **Structured snapshot:** ``{place: [{"value": v, "created_at": ms},
      ...]}``. Timestamps are preserved verbatim — and validated, never
      coerced: `created_at` must be an integer (or an integral float) in
      ``0 <= ms < 2**64``, the same rule the engine applies, so a bad value
      fails here rather than later inside a run. This is the form executor
      runs return as of 2.7.0 and the form `snapshot()` emits, so passing a
      previous run's view back as `initial=` preserves every token's
      `created_at`, and with it the `created_at`-driven freshness patterns.

      **Timing clocks do not survive the round-trip** ([CORE-073] AC#3/AC#4).
      A restored marking pre-populates places like any other initial marking,
      so a `delayed`/`window` transition it enables waits its **full**
      interval measured from the *resuming* executor's enablement, and a
      `deadline(d)` is reaped `d` after that enablement — the original hard
      bound is gone, and no timeout is emitted for the budget already spent.
      The asymmetry matters: re-waiting a lower bound is conservative and
      stays sound, but a hard upper bound is silently **renewed**, so a token
      that should have been reaped gets a fresh full budget on every restore.
      Restoring more often than `d` therefore means `deadline(d)` never
      fires at all.

    Iteration, ``view[place]``, and `tokens(place)` all yield the
    **value-only** tuple — backward-compatible with pre-2.7.0 callers.
    Use `timestamps(place)` or `snapshot()` to reach the `created_at` data.

    A view returned by a run also carries `termination_reason` ([EXEC-041]
    AC3): why the run ended.
    """

    def __init__(
        self,
        data: Mapping[str, Iterable[Any]] | None = None,
    ) -> None:
        self._termination_reason: str | None = None
        if isinstance(data, MarkingView):
            self._values = dict(data._values)
            self._created_at = dict(data._created_at)
            self._termination_reason = data._termination_reason
            return
        _reject_snapshot_result(data, "MarkingView(...)")
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
                    ts_list.append(_coerce_created_at(token["created_at"]))
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

    @classmethod
    def _from_run(cls, result: tuple[Any, str]) -> "MarkingView":
        data, reason = result
        view = cls(data)
        view._termination_reason = reason
        return view

    @property
    def termination_reason(self) -> str | None:
        """Why the run that returned this view ended ([EXEC-041] AC3), or
        ``None`` for a view that no run returned.

        ``"quiescent"`` — nothing enabled and nothing in flight ([EXEC-040]);
        ``"terminal"`` — a terminal place was marked ([EXEC-042]), and the run
        stopped at once, abandoning actions in flight; ``"closed"`` — a
        ``close()`` truncated the run ([ENV-013]); ``"stopped"`` — another
        caller-requested stop. The first two are designed ends: the marking
        is the one the net was built to finish in.
        """
        return self._termination_reason

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

        Places appear in ascending code-point order (a dict is an ordered
        medium, so insertion order would otherwise leak into whatever a host
        does with it). Use `snapshot()` for the timestamp-preserving
        structured form.
        """
        return {
            place_name: list(self._values[place_name])
            for place_name in sorted(self._values)
        }

    def snapshot(self) -> dict[str, list[dict[str, Any]]]:
        """Structured snapshot with per-token `created_at` preserved.

        Round-trip via `MarkingView.from_snapshot(view.snapshot())` reproduces
        the marking exactly — every value and every `created_at`.

        This is Python's [CORE-073] snapshot form, so it is **canonical**
        however the view was built: places in ascending code-point order
        (AC#12 — ``sorted()`` on `str` is exactly that order, so two hosts
        snapshotting the same marking agree key for key), and places holding
        no tokens omitted. A restore accepts a snapshot with or without empty
        places identically. Iterating the view itself (``for place in view``,
        `places()`) still follows construction order.

        What it does **not** reproduce is timing state ([CORE-073] AC#3/AC#4):
        pass this back as `initial=` and a `delayed`/`window` transition waits
        its full interval again from the resuming executor's enablement, while
        a `deadline(d)` gets a fresh full `d`. Token freshness survives; net
        clocks restart. See `MarkingView` for why the upper-bound half is the
        unsafe one.
        """
        return {
            place: [
                {"value": value, "created_at": ts}
                for value, ts in zip(
                    self._values[place], self._created_at[place], strict=True
                )
            ]
            for place in sorted(self._values)
            if self._values[place]
        }

    def __repr__(self) -> str:
        return f"MarkingView({self.to_dict()!r})"


@dataclass(slots=True, frozen=True)
class SnapshotResult:
    """[ENV-014] AC5/AC6 — what a mid-execution snapshot returns.

    The marking **and** whether work was in flight when it was taken, as one
    value. Deliberately not a separately-queryable flag: that would be
    read at a different instant than the marking, which is the race AC5 exists
    to close.

    Nothing suspends the run to serve a snapshot, so an action may be in
    flight — having consumed its inputs and not yet produced its outputs.
    Those tokens are in *neither* place at the instant you observe them. The
    marking is a valid **observation**; it is not a valid **restore point**,
    because restoring it loses that work silently. Check `is_restore_point`.

    `action_in_flight` means **work in flight: an action, or an accepted but
    un-injected external event**. The second half is there for parity with the
    other implementations and cannot occur in Python: `inject` and `snapshot`
    travel down one FIFO channel to the Rust executor and an inject is applied
    on receipt, so every event accepted before the snapshot request is already
    in its marking.

    `action_in_flight` is singular and boolean on purpose: a count would
    invite reading it as a live gauge of what is running *now*, which is the
    racy reading AC5 forbids. It is a fact about one instant, not a
    measurement you can re-check.
    """

    marking: MarkingView
    action_in_flight: bool

    @property
    def is_restore_point(self) -> bool:
        """True when nothing was in flight, so the marking is safe to restore.

        Named for the question a caller is actually asking.
        """
        return not self.action_in_flight


@dataclass(slots=True, frozen=True)
class ExecutorOptions:
    environment_places: tuple[PlaceLike, ...] = ()
    skip_output_validation: bool = False
    #: Grace band (ms) beyond a hard deadline (``deadline()`` / ``window()``) before a
    #: transition is force-disabled (TIME-013). ``None`` uses the library default (5ms);
    #: must be non-negative. Does not affect ``exact()`` transitions, which are enforced
    #: softly and never force-disabled (TIME-006).
    deadline_tolerance_ms: float | None = None
    #: [NU-011] Scope folded into every minted ν-name (``<transition>#<scope>:<n>``).
    #: ``None`` draws a fresh random scope per executor — 128 bits as exactly 32
    #: lowercase hex characters, unique across processes — so two executions resumed
    #: from one snapshot, even in different processes, cannot mint colliding names by
    #: default. It is *not* the executor's run identifier and is **not reproducible**:
    #: pin a scope to make a resumed segment's minted names reproducible (NU-011 AC#3)
    #: — for a fixed scope and firing order the sequence is identical, ``<n>`` being a
    #: per-executor counter from 0. A pinned scope must be unique within its restore
    #: lineage; reusing one is the collision NU-011 forbids.
    #:
    #: Must not be empty (whitespace is legal) and must not contain ``':'`` or ``'#'``
    #: — ``ValueError`` otherwise. With both separators banned a minted name parses
    #: uniquely whatever the transition is called: the last ``':'`` splits off the
    #: counter, then the last ``'#'`` before it splits off the scope.
    execution_scope: str | None = None

    def __post_init__(self) -> None:
        # Validate here rather than only at `native()`: the scope is a
        # construction-time choice, and an error raised where the caller
        # wrote the value points at the mistake instead of at the run.
        # The rule is identical in all four implementations and in the
        # binding (`_libpetri.ExecutorOptions`): empty — not blank — and the
        # two separators.
        scope = self.execution_scope
        if scope is None:
            return
        if len(scope) == 0:
            raise ValueError("execution_scope must not be empty (NU-011)")
        if ":" in scope:
            raise ValueError(
                "execution_scope must not contain ':' (it separates scope from "
                f"counter in a minted name, NU-011): {scope!r}"
            )
        if "#" in scope:
            raise ValueError(
                "execution_scope must not contain '#' (it separates transition "
                f"from scope in a minted name, NU-011): {scope!r}"
            )

    def native(self) -> _ext.ExecutorOptions:
        return _ext.ExecutorOptions(
            environment_places=[
                _coerce_place_name(p) for p in self.environment_places
            ],
            skip_output_validation=self.skip_output_validation,
            deadline_tolerance_ms=self.deadline_tolerance_ms,
            execution_scope=self.execution_scope,
        )


def _normalize_initial(initial):
    if initial is None:
        return None
    _reject_snapshot_result(initial, "`initial=`")
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
        return MarkingView._from_run(result)

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
            return MarkingView._from_run(await native_awaitable)

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

        def inject_many(self, place: PlaceLike, values: Iterable[Any]) -> bool:
            return self._inner.inject_many(_coerce_place_name(place), values)

        def drain(self) -> bool:
            return self._inner.drain()

        def close(self) -> bool:
            return self._inner.close()

        @property
        def drained(self) -> bool:
            return self._inner.drained

        @property
        def termination_reason(self) -> str:
            """Why the run ended ([EXEC-041] AC3): ``"running"`` until it
            has, then ``"quiescent"``, ``"terminal"`` ([EXEC-042]),
            ``"closed"`` or ``"stopped"`` — the value the run's `MarkingView`
            carries."""
            return self._inner.termination_reason

        async def snapshot(self) -> SnapshotResult:
            """Request a mid-execution marking snapshot.

            The executor materializes its current marking and returns a
            `SnapshotResult`: the marking as a `MarkingView` with per-token
            `created_at` preserved, **and** `action_in_flight`, read at the
            same instant ([ENV-014] AC5/AC6). Does not affect lifecycle — the
            executor keeps running. Every `inject` accepted before this call
            is already in the marking (one FIFO channel serves both).

            Nothing suspends the run to take the snapshot, so an action may
            be in flight — having consumed its inputs and not yet produced
            its outputs. Those tokens are in neither place at the instant you
            observe them, so check `is_restore_point` before resuming from
            one. A mid-flight snapshot remains perfectly good for diagnostics
            and monitoring.

            **From inside an action** ([ENV-014] AC8). An ``async def`` action
            may ``await handle.snapshot()``; the firing running it has
            consumed its inputs and deposited nothing, so the result reports
            `action_in_flight` and is not a restore point. A **sync** action
            under `start_async` / `run_async` runs inline in the executor's
            loop: it must not *block* on the reply (for example through
            ``asyncio.run_coroutine_threadsafe(...).result()``) — the reply
            can only be produced once the action has returned, so an unbounded
            wait never ends.

            Raises `RuntimeError` if the handle is drained, closed, or the
            executor has already exited.
            """
            data = await self._inner.snapshot()
            return SnapshotResult(
                marking=MarkingView.from_snapshot(data["marking"]),
                action_in_flight=bool(data["action_in_flight"]),
            )

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
    "SnapshotResult",
    "compile",
    "run_async",
    "run_sync",
    "start_async",
]
