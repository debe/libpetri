"""libpetri — Python bindings for the Rust Coloured Time Petri Net engine.

Note on token typing: the Java, TypeScript, and Rust implementations enforce
``Place[T]`` token types at compile time. The Python binding stores tokens as
``Py<PyAny>`` across the FFI boundary — net *structure* (arcs, transitions,
composition) is still validated, but token *runtime types* are not. A place
named ``"order"`` will accept dicts, integers, or strings interchangeably.
This is intentional: Python has no static generics across the FFI. If you need
type discipline, validate at your boundary (Pydantic, dataclasses, ``isinstance``)
and only put validated values into markings.
"""

from __future__ import annotations

from importlib.metadata import PackageNotFoundError, version

from . import _libpetri
from .asyncio_helpers import action_gather, action_to_thread
from .debug import DebugProtocolHandler, SessionSummary, require_debug
from .events import InMemoryEventStore, NetEvent
from .export import DotConfig, RankDir, dot_export

if _libpetri.HAS_TOKIO:
    from .events import EventStream, EventSubscription

if _libpetri.HAS_ARCHIVE:
    from .archive import (
        ComputedState,
        MarkingCache,
        SessionArchive,
        SessionArchiveReader,
        SessionArchiveWriter,
    )
from .model import (
    BuiltNet,
    BuiltSubnetDef,
    BuiltTransition,
    BuiltinAction,
    Channel,
    fork,
    passthrough,
    InputSpec,
    Instance,
    InhibitorArc,
    MatchSpec,
    Net,
    NetBuilder,
    OutputSpec,
    Place,
    Port,
    ReadArc,
    ResetArc,
    SubnetDef,
    SubnetDefBuilder,
    SubnetInstance,
    Timing,
    Transition,
    TransitionBuilder,
    TransitionContext,
    all_tokens,
    and_,
    and_outputs,
    at_least,
    deadline,
    delayed,
    exact,
    exactly,
    forward_input,
    immediate,
    inhibitor,
    match_spec,
    one,
    out,
    out_place,
    read,
    reset,
    timeout,
    window,
    xor,
    xor_outputs,
)
from .runtime import (
    CompiledNet,
    ExecutorHandle,
    ExecutorOptions,
    MarkingView,
    compile,
    run_async,
    run_sync,
    start_async,
)
from .verification import (
    EnvironmentAnalysisMode,
    PropertyResult,
    SmtProperty,
    SubnetVerificationResult,
    VerificationHarness,
    VerificationResult,
    always_available,
    bounded,
    branch_place_bound,
    deadlock_free,
    terminates_at_sink,
    ignore,
    joined_or_dead_lettered,
    mutual_exclusion,
    place_bound,
    unreachable,
    encode_smt_scripts,
    verify,
    verify_subnet,
    z3_available,
)

CallbackError = _libpetri.CallbackError
LibpetriError = _libpetri.LibpetriError
StructureError = _libpetri.StructureError

HAS_TOKIO = bool(_libpetri.HAS_TOKIO)
# Compile feature only: the wheel carries the SMT surface. Whether a ``z3``
# executable is actually available is :func:`z3_available` (VER-013).
HAS_Z3 = bool(_libpetri.HAS_Z3)
HAS_DEBUG = bool(_libpetri.HAS_DEBUG)
HAS_ARCHIVE = bool(_libpetri.HAS_ARCHIVE)

try:
    __version__ = version("libpetri")
except PackageNotFoundError:
    __version__ = "0+local"

__all__ = [
    "__version__",
    "BuiltinAction",
    "CallbackError",
    "Channel",
    "fork",
    "passthrough",
    "CompiledNet",
    "DebugProtocolHandler",
    "DotConfig",
    "EnvironmentAnalysisMode",
    "ExecutorHandle",
    "ExecutorOptions",
    "HAS_ARCHIVE",
    "HAS_DEBUG",
    "HAS_TOKIO",
    "HAS_Z3",
    "InMemoryEventStore",
    "InputSpec",
    "InhibitorArc",
    "MatchSpec",
    "match_spec",
    "Instance",
    "LibpetriError",
    "MarkingView",
    "Net",
    "NetBuilder",
    "NetEvent",
    "OutputSpec",
    "Place",
    "Port",
    "PropertyResult",
    "RankDir",
    "ReadArc",
    "ResetArc",
    "SessionSummary",
    "SmtProperty",
    "StructureError",
    "SubnetDef",
    "SubnetDefBuilder",
    "SubnetInstance",
    "SubnetVerificationResult",
    "Timing",
    "Transition",
    "TransitionBuilder",
    "TransitionContext",
    "VerificationHarness",
    "VerificationResult",
    "action_gather",
    "action_to_thread",
    "all_tokens",
    "always_available",
    "and_",
    "and_outputs",
    "at_least",
    "bounded",
    "branch_place_bound",
    "compile",
    "deadlock_free",
    "terminates_at_sink",
    "deadline",
    "delayed",
    "dot_export",
    "exact",
    "exactly",
    "forward_input",
    "ignore",
    "immediate",
    "inhibitor",
    "joined_or_dead_lettered",
    "mutual_exclusion",
    "one",
    "out",
    "out_place",
    "place_bound",
    "read",
    "require_debug",
    "reset",
    "run_async",
    "run_sync",
    "start_async",
    "timeout",
    "unreachable",
    "verify",
    "verify_subnet",
    "encode_smt_scripts",
    "z3_available",
    "window",
    "xor",
    "xor_outputs",
    "BuiltNet",
    "BuiltSubnetDef",
    "BuiltTransition",
]

if HAS_ARCHIVE:
    __all__.extend(
        [
            "ComputedState",
            "MarkingCache",
            "SessionArchive",
            "SessionArchiveReader",
            "SessionArchiveWriter",
        ]
    )

if HAS_TOKIO:
    __all__.extend(["EventStream", "EventSubscription"])
