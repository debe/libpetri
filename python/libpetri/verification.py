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
    fragment_mode: str | int | None = None,
    carrier_places: Iterable[PlaceLike] | None = None,
    priority_semantics: str | int | None = None,
    certificate_check: bool = True,
    counterexample_replay: bool = True,
    semiflow_invariants: bool = False,
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

    ``fragment_mode`` (NU-051) selects which coloured-place fragment the
    ν-aware state-class graph admits. ``"base"`` (the default, also selectable
    as ``0``) reproduces the shipped mint to matched-join behaviour.
    ``"extended"`` (or ``1``) additionally admits the opt-in drain/relay
    coloured-consumer role and the declared ``carrier_places``. When EXTENDED is
    requested but the net falls outside the coloured-consumer fragment, the
    verifier appends a short "Route B (EXTENDED) declined" note to
    ``result.report`` and verifies via the sound over-approximation instead.

    ``carrier_places`` (NU-051) declares intermediate places that carry a fresh
    name from the minting fork onward to a ν-join input, so the fork co-mints
    one name into each of them. Effective only under ``fragment_mode="extended"``
    and ignored under ``"base"``. A declared carrier name that is not a place in
    ``net`` surfaces as an ``unknown`` verdict whose ``reason`` names the
    offending place, never a silent fall-back.

    ``priority_semantics`` (NU-052) selects how the ν-aware Route B analyzer
    treats transition priority. ``"none"`` (the default, also selectable as
    ``0``) is the priority- and timing-blind over-approximation: it expands every
    base-enabled transition, so a delayed, lower-priority drain competing for a
    coloured token with an immediate, higher-priority ν-join is reported as a
    spurious stall. ``"conflict"`` (or ``1``) models the executor's conflict-only
    priority resolution: a lower-priority transition is not expanded when a ready,
    conflicting (shares a consumed input place), strictly-higher-priority
    transition can pre-empt it — pruning exactly those interleavings the eager,
    priority-ordered executor never produces, without hiding a genuine stall.

    ``certificate_check`` (default ``True``) re-verifies a ``proven`` verdict
    from the flat IC3/PDR path: the solver's inductive invariant is re-checked
    against the unstrengthened step relation in a second, independent solver
    run, and a failing or unrunnable check downgrades the verdict to
    ``unknown`` rather than certify on the solver's say-so.

    ``counterexample_replay`` (default ``True``) re-validates a ``violated``
    verdict by replaying the states decoded from the solver's refutation
    against the abstract semantics. ``result.counterexample_confirmed`` is the
    tri-state outcome (canonical definition:
    ``VerificationResult::counterexample_confirmed`` in the Rust verifier):

    * ``None`` -- the replay did not apply (turned off here, a non-violated
      verdict, or a verdict from the coloured / Route B / structural path);
    * ``False`` -- the replay applied and did not confirm the counterexample.
      Either it could not conclude (nothing decodable in the proof, the initial
      marking absent from the decoded set, or a budget exhausted), in which case
      the ``violated`` verdict stands unconfirmed; or it refuted the trace
      outright by covering the successor space and finding no firing chain, in
      which case the verdict is downgraded to ``unknown``. A refutation is more
      informative than "did not apply", so it reports ``False``, never ``None``;
    * ``True`` -- the replay chained the initial marking to a violating state.

    Turning this off also turns off the only source of
    ``counterexample_trace``.

    ``semiflow_invariants`` (default ``False``, VER-007) also hands the
    gate-validated P-semiflows (the net's minimal non-negative conservation
    laws) to the encoders as invariants, alongside the null-space basis. The
    basis is one basis of many and on a reset-heavy net can lose every law of
    the chains the reset arcs touch, leaving IC3 to rediscover conservation it
    cannot within any practical budget; the semiflows are those laws.

    Turn it on if the net has any ``all()`` / ``at_least(n)`` or reset arc on a
    busy place -- draining an input queue is the everyday case. Every basis row
    whose support touches such a place fails the H1 guard and is dropped, so the
    encoders run on a deficient invariant set and nothing in the report says a
    law is missing beyond the ``Dropped`` lines. It reaches the name-coloured
    encoder (NU-050) as well as the flat one, and matters most there: on a
    113-place nu-net, whole-net deadlock-freedom went from ``unknown`` after 50
    minutes to ``proven`` in about 15 seconds on this option alone.

    Pure strengthening (Lean ``semiflow_union_sound``): the semiflows pass the
    same exact gate as the basis rows and the certificate check re-proves the
    strengthened invariant, so a ``violated`` verdict can never become
    ``proven``. That check is flat-path only -- a coloured ``proven`` reports
    ``Certificate check: not applicable (name-coloured encoding)``. When enabled
    the report carries ``  Semiflows encoded as invariants: N``; off by default
    so reports stay byte-identical.
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
        fragment_mode=fragment_mode,
        carrier_places=[_coerce_place_name(p) for p in (carrier_places or ())],
        priority_semantics=priority_semantics,
        certificate_check=certificate_check,
        counterexample_replay=counterexample_replay,
        semiflow_invariants=semiflow_invariants,
    )


def _coerce_harness(harness):
    if isinstance(harness, VerificationHarness):
        return harness._inner
    return VerificationHarness.from_properties(harness)._inner


def verify_subnet(
    subnet: BuiltSubnetDef,
    harness,
    *,
    environment_mode: EnvironmentAnalysisMode | None = None,
) -> SubnetVerificationResult:
    """Verifies a subnet in isolation under a harness (MOD-051).

    ``environment_mode`` decides how injection into the synthetic environment places
    (one per input and in-out port) is modeled, per VER-006. It defaults to
    :func:`always_available`, under which a ``proven`` verdict holds for any
    environment. Pass :func:`bounded` to prove a property that holds only when the
    environment injects at most ``k`` tokens -- that is the mode which expresses a
    generator bounding the input (MOD-051 AC3). :func:`ignore` is accepted but can
    never yield ``proven``: VER-006 refuses to certify a proof that holds only because
    injection was never modeled.
    """
    return _ext.verify_subnet(
        _coerce_subnet(subnet),
        _coerce_harness(harness),
        environment_mode=environment_mode,
    )


def encode_smt_scripts(
    net: BuiltNet,
    property: SmtProperty,
    *,
    initial_marking: Mapping[PlaceLike, int] | None = None,
    environment_places: Iterable[PlaceLike] | None = None,
    environment_mode: EnvironmentAnalysisMode | None = None,
    sink_places: Iterable[PlaceLike] | None = None,
    budget_places: Iterable[PlaceLike] | None = None,
    fragment_mode: str | int | None = None,
    carrier_places: Iterable[PlaceLike] | None = None,
    counterexample_replay: bool = True,
    semiflow_invariants: bool = False,
) -> dict:
    """The SMT-LIB2 scripts :func:`verify` would send to z3 for this configuration,
    without running a solver (VER-013 AC1).

    Returns ``{"horn": str, "certificate": str | None, "coloured": bool}``: the HORN
    query (flat, or name-coloured when a declared budget puts the net on Route A's
    exact encoding) and, for the flat encoding, the certificate-check script built
    around the placeholder certificate. This is what the cross-language golden
    tests diff byte for byte.

    Every option :func:`verify` takes is accepted here and changes the script the
    same way, ``semiflow_invariants`` included: with it enabled the strengthened
    invariant list is conjoined into the rule bodies, on the name-coloured encoding
    as well as the flat one, so the returned ``horn`` differs from the one the same
    configuration produces with it disabled. See :func:`verify` for when to turn it
    on.
    """
    return _ext.encode_smt_scripts(
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
        fragment_mode=fragment_mode,
        carrier_places=[_coerce_place_name(p) for p in (carrier_places or ())],
        counterexample_replay=counterexample_replay,
        semiflow_invariants=semiflow_invariants,
    )


def z3_available() -> bool:
    """Whether SMT verification can actually run on this machine.

    The verifier shells out to a ``z3`` executable (VER-013): ``LIBPETRI_Z3``
    if set, else ``z3`` on ``PATH``, version 4.8.0 or newer. ``libpetri.HAS_Z3``
    only says the wheel was *built* with the SMT surface; without a usable
    binary every :func:`verify` call returns ``unknown`` with a reason naming
    the command and the variable. Set ``LIBPETRI_SMT_DUMP`` to a directory to
    keep every script and solver reply.
    """
    return bool(_ext.z3_available())


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
    "encode_smt_scripts",
    "z3_available",
]
