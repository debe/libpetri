"""Type stubs for libpetri.verification."""

from __future__ import annotations

from collections.abc import Callable, Iterable, Mapping
from typing import Any, Literal, TypeAlias

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
def terminates_at_sink() -> SmtProperty: ...
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
    nu_max_classes: int | None = ...,
    fragment_mode: str | int | None = ...,
    carrier_places: Iterable[PlaceLike] | None = ...,
    priority_semantics: str | int | None = ...,
    certificate_check: bool = ...,
    counterexample_replay: bool = ...,
    semiflow_invariants: bool | Literal["auto"] = ...,
    sink_places_when: Mapping[PlaceLike, Iterable[PlaceLike]] | None = ...,
    linear_bound: bool = ...,
    state_equation: bool = ...,
    enumeration_max_classes: int | None = ...,
) -> VerificationResult:
    """``sink_places_when`` declares, in dict order, the places where a token may
    rest while its marker place holds a token (VER-014). ``linear_bound`` (default
    on) proves a reachability-safety property from one exactly re-checked linear
    state-equation bound before any fixpoint query (VER-015). ``state_equation``
    (default off) adds firing counters and the marking equation to the flat
    encoding (VER-016). ``enumeration_max_classes`` (``None`` keeps the engine
    default of 50 000) is the class
    budget of the bounded state-space enumeration route, which decides an untimed
    closed net exactly with no solver at all; ``0`` disables it (VER-017).
    ``semiflow_invariants="auto"`` unions the P-semiflows exactly when the
    null-space basis lost a law to the H1 guard (VER-007). The result names the
    deciding route in ``route`` (VER-003)."""
def verify_subnet(
    subnet: BuiltSubnetDef,
    harness: VerificationHarness | Iterable[SmtProperty],
    *,
    environment_mode: EnvironmentAnalysisMode | None = ...,
) -> SubnetVerificationResult: ...
def encode_smt_scripts(
    net: BuiltNet,
    property: SmtProperty,
    *,
    initial_marking: Mapping[PlaceLike, int] | None = ...,
    environment_places: Iterable[PlaceLike] | None = ...,
    environment_mode: EnvironmentAnalysisMode | None = ...,
    sink_places: Iterable[PlaceLike] | None = ...,
    budget_places: Iterable[PlaceLike] | None = ...,
    fragment_mode: str | int | None = ...,
    carrier_places: Iterable[PlaceLike] | None = ...,
    counterexample_replay: bool = ...,
    semiflow_invariants: bool | Literal["auto"] = ...,
    sink_places_when: Mapping[PlaceLike, Iterable[PlaceLike]] | None = ...,
    linear_bound: bool = ...,
    state_equation: bool = ...,
) -> dict[str, str | bool | None]:
    """Returns ``horn``, ``certificate``, ``coloured`` and ``bound`` -- the linear
    state-equation bound query, present exactly when :func:`verify` would send it
    (VER-015). ``sink_places_when`` (VER-014), ``linear_bound`` (VER-015; ``False``
    returns ``bound: None``) and ``state_equation`` (VER-016) shape the scripts
    as they do for :func:`verify`."""
def z3_available() -> bool: ...
