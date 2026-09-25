"""Type stubs for libpetri.verification."""

from __future__ import annotations

from collections.abc import Callable, Iterable, Mapping
from typing import Any, Literal, TypeAlias

from . import _libpetri as _ext
from .model import BuiltNet, BuiltSubnetDef, BuiltTransition, Place, PlaceLike

SmtProperty: TypeAlias = _ext.SmtProperty
VerificationResult: TypeAlias = _ext.VerificationResult
PropertyResult: TypeAlias = _ext.PropertyResult
SubnetVerificationResult: TypeAlias = _ext.SubnetVerificationResult
StateSpaceCache: TypeAlias = _ext.StateSpaceCache
EnvironmentAnalysisMode: TypeAlias = _ext.EnvironmentAnalysisMode
OpenNetResult: TypeAlias = _ext.OpenNetResult
ContractViolation: TypeAlias = _ext.ContractViolation
PortStep: TypeAlias = _ext.PortStep

# `Mapping` is invariant in its key, so `Mapping[PlaceLike, V]` alone would reject a
# `dict[str, V]` or `dict[Place, V]` held in a variable.
_PlaceCounts: TypeAlias = Mapping[str, int] | Mapping[Place, int] | Mapping[PlaceLike, int]
_PlaceSets: TypeAlias = (
    Mapping[str, Iterable[PlaceLike]]
    | Mapping[Place, Iterable[PlaceLike]]
    | Mapping[PlaceLike, Iterable[PlaceLike]]
)

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
def quiescent_count(
    places: Iterable[PlaceLike],
    min: int,
    max: int | float,
    waived_by: Iterable[PlaceLike] | None = ...,
) -> SmtProperty:
    """Every quiescent marking holds between ``min`` and ``max`` tokens across
    ``places``, the lower bound waived while a ``waived_by`` place is marked
    (VER-002). ``max`` is ``math.inf`` for no upper bound."""
def verify(
    net: BuiltNet,
    property: SmtProperty,
    *,
    initial_marking: _PlaceCounts | None = ...,
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
    sink_places_when: _PlaceSets | None = ...,
    linear_bound: bool = ...,
    state_equation: bool = ...,
    enumeration_max_classes: int | None = ...,
    state_equation_phase: bool = ...,
    firing_bound: bool = ...,
    state_space_cache: StateSpaceCache | None = ...,
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
    null-space basis lost a law to the H1 guard (VER-007). ``state_equation_phase``
    (VER-018) and ``firing_bound`` (VER-019), both on by default, can decide the
    property before the fixpoint query; ``False`` forces the fixpoint path.
    ``state_space_cache`` shares the enumeration route's state-class graph across
    queries on one net and initial marking (VER-017). The result names the
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
    initial_marking: _PlaceCounts | None = ...,
    environment_places: Iterable[PlaceLike] | None = ...,
    environment_mode: EnvironmentAnalysisMode | None = ...,
    sink_places: Iterable[PlaceLike] | None = ...,
    budget_places: Iterable[PlaceLike] | None = ...,
    fragment_mode: str | int | None = ...,
    carrier_places: Iterable[PlaceLike] | None = ...,
    counterexample_replay: bool = ...,
    semiflow_invariants: bool | Literal["auto"] = ...,
    sink_places_when: _PlaceSets | None = ...,
    linear_bound: bool = ...,
    state_equation: bool = ...,
    state_equation_phase: bool = ...,
) -> dict[str, str | bool | None]:
    """Returns ``horn``, ``certificate``, ``coloured``, ``bound`` -- the linear
    state-equation bound query, present exactly when :func:`verify` would send it
    (VER-015) -- and ``state_equation``, the first query of the VER-018 phase,
    present exactly where that phase runs. ``sink_places_when`` (VER-014),
    ``linear_bound`` (VER-015; ``False`` returns ``bound: None``),
    ``state_equation`` (VER-016's counters in ``horn``) and ``state_equation_phase``
    (VER-018; ``False`` returns ``state_equation: None``) shape the scripts as they
    do for :func:`verify`."""
def z3_available() -> bool: ...

class OpenNetContract:
    def __init__(self, inner: _ext.OpenNetContract) -> None: ...
    @classmethod
    def builder(cls) -> OpenNetContractBuilder: ...
    def places(self) -> list[str]: ...
    def describe(self) -> list[str]: ...
    @property
    def requires_termination(self) -> bool: ...

class OpenNetContractBuilder:
    def __init__(self) -> None: ...
    def initial_marking(self, marking: _PlaceCounts) -> OpenNetContractBuilder: ...
    def initial_tokens(self, place: PlaceLike, count: int) -> OpenNetContractBuilder: ...
    def arrive(self, count: int, *places: PlaceLike) -> OpenNetContractBuilder: ...
    def arrive_at_most(self, max: int, *places: PlaceLike) -> OpenNetContractBuilder: ...
    def arrive_between(self, min: int, max: int, *places: PlaceLike) -> OpenNetContractBuilder: ...
    def expect(self, name: str, count: int, *places: PlaceLike) -> OpenNetContractBuilder: ...
    def expect_between(
        self, name: str, min: int, max: int | float, *places: PlaceLike
    ) -> OpenNetContractBuilder: ...
    def rest(self, *places: PlaceLike) -> OpenNetContractBuilder: ...
    def terminal(self, marker: PlaceLike, *excused: PlaceLike) -> OpenNetContractBuilder: ...
    def environment(self, *transitions: BuiltTransition) -> OpenNetContractBuilder: ...
    def require_termination(self, required: bool) -> OpenNetContractBuilder: ...
    def build(self) -> OpenNetContract: ...

def verify_open_net(
    net: BuiltNet,
    contract: OpenNetContract,
    *,
    max_classes: int = ...,
    smt: bool = ...,
    termination_timeout_ms: int = ...,
    timeout_ms: int = ...,
    linear_bound: bool = ...,
    state_equation: bool = ...,
    state_equation_phase: bool = ...,
    firing_bound: bool = ...,
    semiflow_invariants: bool | Literal["auto"] = ...,
) -> OpenNetResult:
    """Verifies ``net`` in isolation against ``contract`` (VER-022): the closed
    net's untimed state-class graph within ``max_classes``, then, unless ``smt`` is
    ``False``, one SMT query per part of the contract, configured by the remaining
    keywords as :func:`verify` is."""
