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
    sink_places: Iterable[PlaceLike] | None = None,
    timeout_ms: int = 30_000,
) -> VerificationResult:
    return _ext.verify_net(
        _coerce_net(net),
        property,
        environment_places=[
            _coerce_place_name(p) for p in (environment_places or ())
        ],
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
    "PropertyResult",
    "SmtProperty",
    "SubnetVerificationResult",
    "VerificationHarness",
    "VerificationResult",
    "deadlock_free",
    "mutual_exclusion",
    "place_bound",
    "unreachable",
    "verify",
    "verify_subnet",
]
