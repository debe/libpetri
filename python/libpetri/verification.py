"""SMT verification facade."""

from __future__ import annotations

from collections.abc import Callable, Iterable
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


def verify(
    net: BuiltNet,
    property: SmtProperty,
    *,
    environment_places: Iterable[PlaceLike] | None = None,
    environment_mode: EnvironmentAnalysisMode | None = None,
    sink_places: Iterable[PlaceLike] | None = None,
    timeout_ms: int = 30_000,
) -> VerificationResult:
    """Verify ``property`` against ``net`` via SMT (Z3).

    ``environment_mode`` (VER-006) controls how registered ``environment_places``
    are modeled: :func:`always_available` (unbounded injection), :func:`bounded`,
    or :func:`ignore` (default). With env places present but no mode (i.e. Ignore),
    a would-be vacuous ``proven`` is downgraded to ``unknown``.
    """
    return _ext.verify_net(
        _coerce_net(net),
        property,
        environment_places=[
            _coerce_place_name(p) for p in (environment_places or ())
        ],
        environment_mode=environment_mode,
        sink_places=[_coerce_place_name(p) for p in (sink_places or ())],
        timeout_ms=timeout_ms,
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
    "deadlock_free",
    "ignore",
    "mutual_exclusion",
    "place_bound",
    "unreachable",
    "verify",
    "verify_subnet",
]
