"""SMT verification facade."""

from __future__ import annotations

from collections.abc import Callable, Iterable, Mapping
from typing import Any

from . import _libpetri as _ext
from .model import (
    BuiltNet,
    BuiltSubnetDef,
    PlaceLike,
    _coerce_net,
    _coerce_place_name,
    _coerce_subnet,
)

SmtProperty = _ext.SmtProperty
EnvironmentAnalysisMode = _ext.EnvironmentAnalysisMode
VerificationResult = _ext.VerificationResult
PropertyResult = _ext.PropertyResult
SubnetVerificationResult = _ext.SubnetVerificationResult


class VerificationHarness:
    def __init__(self) -> None:
        self._inner = _ext.VerificationHarness()

    def input(self, port_name: str, supplier: Callable[[], Any]) -> "VerificationHarness":
        self._inner = self._inner.input(port_name, supplier)
        return self

    def property(self, property: SmtProperty) -> "VerificationHarness":
        self._inner = self._inner.property(property)
        return self

    @classmethod
    def from_properties(cls, properties: Iterable[SmtProperty]) -> "VerificationHarness":
        harness = cls()
        for property in properties:
            harness.property(property)
        return harness


def always_available() -> EnvironmentAnalysisMode:
    """Environment mode (VER-006): the outside world may inject env tokens without
    bound — the broadest reachability, recommended for reactive nets."""
    return _ext.always_available()


def bounded(max_tokens: int) -> EnvironmentAnalysisMode:
    """Environment mode (VER-006): each firing may draw at most ``max_tokens`` from
    an environment place."""
    return _ext.bounded(max_tokens)


def ignore() -> EnvironmentAnalysisMode:
    """Environment mode (VER-006): env places are treated as ordinary (not modeled
    as injected). A would-be vacuous ``proven`` is downgraded to ``unknown``."""
    return _ext.ignore()


def deadlock_free() -> SmtProperty:
    return _ext.deadlock_free()


def mutual_exclusion(places: Iterable[PlaceLike]) -> SmtProperty:
    return _ext.mutual_exclusion([_coerce_place_name(p) for p in places])


def place_bound(place: PlaceLike, bound: int) -> SmtProperty:
    return _ext.place_bound(_coerce_place_name(place), bound)


def unreachable(places: Iterable[PlaceLike]) -> SmtProperty:
    return _ext.unreachable([_coerce_place_name(p) for p in places])


def branch_place_bound(place: PlaceLike, bound: int) -> SmtProperty:
    """ν-net budget / fork-branch place bound (NU-040): ``place`` never exceeds
    ``bound`` tokens. Encodes like :func:`place_bound`, but pairing it with a
    ``budget_places`` declaration in :func:`verify` keeps a name-minting net in
    the decidable bounded fragment."""
    return _ext.branch_place_bound(_coerce_place_name(place), bound)


def joined_or_dead_lettered(pending: PlaceLike) -> SmtProperty:
    """ν-net liveness (NU-040): every forked name is joined or dead-lettered —
    no reachable quiescent (deadlocked) state still holds a token in
    ``pending``."""
    return _ext.joined_or_dead_lettered(_coerce_place_name(pending))


def verify(
    net: BuiltNet,
    property: SmtProperty,
    *,
    initial_marking: Mapping[PlaceLike, int] | None = None,
    environment_places: Iterable[PlaceLike] | None = None,
    environment_mode: EnvironmentAnalysisMode | None = None,
    sink_places: Iterable[PlaceLike] | None = None,
    budget_places: Iterable[PlaceLike] | None = None,
    timeout_ms: int = 30_000,
    nu_max_classes: int | None = None,
) -> VerificationResult:
    """Verify ``property`` against ``net`` via SMT (Z3).

    ``initial_marking`` maps places to their starting token counts (empty by
    default). Reactive nets instead leave it empty and model arriving tokens via
    ``environment_places`` + ``environment_mode``.

    ``environment_mode`` (VER-006) controls how registered ``environment_places``
    are modeled: :func:`always_available` (unbounded injection), :func:`bounded`,
    or :func:`ignore` (default). With env places present but no mode (i.e. Ignore),
    a would-be vacuous ``proven`` is downgraded to ``unknown``.

    ``budget_places`` (NU-040) declares the places whose token count bounds the
    live correlation pool of a ν-net (they gate fresh-name minting). For a
    budget-bounded ν-net under a reachability-safety bound, name equality is
    decided exactly via bounded name-colouring (NU-050 #1, Route A). For
    quiescence properties (deadlock-freedom, joined-or-dead-lettered), unbudgeted
    ν-nets, and timed ν-nets, ν-join correlation is decided exactly via the
    name-aware state-class-graph name-partition quotient (NU-050, Route B) — which
    also discovers structural boundedness without a declared budget. When the live
    correlation pool is not structurally bounded the name-aware graph is truncated
    at ``nu_max_classes`` (default 100 000) and the verdict is ``unknown``.
    """
    return _ext.verify_net(
        _coerce_net(net),
        property,
        initial_marking={
            _coerce_place_name(p): n for p, n in (initial_marking or {}).items()
        },
        environment_places=[
            _coerce_place_name(p) for p in (environment_places or ())
        ],
        environment_mode=environment_mode,
        sink_places=[_coerce_place_name(p) for p in (sink_places or ())],
        budget_places=[_coerce_place_name(p) for p in (budget_places or ())],
        timeout_ms=timeout_ms,
        nu_max_classes=nu_max_classes,
    )


def _coerce_harness(harness):
    if isinstance(harness, VerificationHarness):
        return harness._inner
    return VerificationHarness.from_properties(harness)._inner


def verify_subnet(subnet: BuiltSubnetDef, harness) -> SubnetVerificationResult:
    return _ext.verify_subnet(_coerce_subnet(subnet), _coerce_harness(harness))


__all__ = [
    "EnvironmentAnalysisMode",
    "PropertyResult",
    "SmtProperty",
    "SubnetVerificationResult",
    "VerificationHarness",
    "VerificationResult",
    "always_available",
    "bounded",
    "branch_place_bound",
    "deadlock_free",
    "ignore",
    "joined_or_dead_lettered",
    "mutual_exclusion",
    "place_bound",
    "unreachable",
    "verify",
    "verify_subnet",
]
