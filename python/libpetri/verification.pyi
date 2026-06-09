"""Type stubs for libpetri.verification."""

from __future__ import annotations

from collections.abc import Callable, Iterable, Mapping
from typing import Any, TypeAlias

from . import _libpetri as _ext
from .model import BuiltNet, BuiltSubnetDef, PlaceLike

SmtProperty: TypeAlias = _ext.SmtProperty
VerificationResult: TypeAlias = _ext.VerificationResult
PropertyResult: TypeAlias = _ext.PropertyResult
SubnetVerificationResult: TypeAlias = _ext.SubnetVerificationResult
EnvironmentAnalysisMode: TypeAlias = _ext.EnvironmentAnalysisMode

class VerificationHarness:
    def __init__(self) -> None: ...
    def input(
        self, port_name: str, supplier: Callable[[], Any]
    ) -> VerificationHarness: ...
    def property(self, property: SmtProperty) -> VerificationHarness: ...
    @classmethod
    def from_properties(
        cls, properties: Iterable[SmtProperty]
    ) -> VerificationHarness: ...

def always_available() -> EnvironmentAnalysisMode: ...
def bounded(max_tokens: int) -> EnvironmentAnalysisMode: ...
def ignore() -> EnvironmentAnalysisMode: ...
def deadlock_free() -> SmtProperty: ...
def mutual_exclusion(places: Iterable[PlaceLike]) -> SmtProperty: ...
def place_bound(place: PlaceLike, bound: int) -> SmtProperty: ...
def unreachable(places: Iterable[PlaceLike]) -> SmtProperty: ...
def branch_place_bound(place: PlaceLike, bound: int) -> SmtProperty: ...
def joined_or_dead_lettered(pending: PlaceLike) -> SmtProperty: ...
def verify(
    net: BuiltNet,
    property: SmtProperty,
    *,
    initial_marking: Mapping[PlaceLike, int] | None = ...,
    environment_places: Iterable[PlaceLike] | None = ...,
    environment_mode: EnvironmentAnalysisMode | None = ...,
    sink_places: Iterable[PlaceLike] | None = ...,
    budget_places: Iterable[PlaceLike] | None = ...,
    timeout_ms: int = ...,
) -> VerificationResult: ...
def verify_subnet(
    subnet: BuiltSubnetDef,
    harness: VerificationHarness | Iterable[SmtProperty],
) -> SubnetVerificationResult: ...
