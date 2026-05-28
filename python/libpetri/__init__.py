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
from .debug import DebugProtocolHandler, SessionSummary, require_debug
from .export import DotConfig, RankDir, dot_export
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
    PropertyResult,
    SmtProperty,
    SubnetVerificationResult,
    VerificationHarness,
    VerificationResult,
    deadlock_free,
    mutual_exclusion,
    place_bound,
    unreachable,
    verify,
    verify_subnet,
)

CallbackError = _libpetri.CallbackError
LibpetriError = _libpetri.LibpetriError
StructureError = _libpetri.StructureError

HAS_TOKIO = bool(_libpetri.HAS_TOKIO)
HAS_Z3 = bool(_libpetri.HAS_Z3)
HAS_DEBUG = bool(_libpetri.HAS_DEBUG)

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
    "ExecutorHandle",
    "ExecutorOptions",
    "HAS_DEBUG",
    "HAS_TOKIO",
    "HAS_Z3",
    "InputSpec",
    "InhibitorArc",
    "Instance",
    "LibpetriError",
    "MarkingView",
    "Net",
    "NetBuilder",
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
    "all_tokens",
    "and_",
    "and_outputs",
    "at_least",
    "compile",
    "deadlock_free",
    "deadline",
    "delayed",
    "dot_export",
    "exact",
    "exactly",
    "forward_input",
    "immediate",
    "inhibitor",
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
    "window",
    "xor",
    "xor_outputs",
    "BuiltNet",
    "BuiltSubnetDef",
    "BuiltTransition",
]
