"""Type stubs for the libpetri public surface."""

from __future__ import annotations

from . import _libpetri
from .debug import (
    DebugProtocolHandler as DebugProtocolHandler,
    SessionSummary as SessionSummary,
    require_debug as require_debug,
)
from .export import (
    DotConfig as DotConfig,
    RankDir as RankDir,
    dot_export as dot_export,
)
from .model import (
    BuiltNet as BuiltNet,
    BuiltSubnetDef as BuiltSubnetDef,
    BuiltTransition as BuiltTransition,
    BuiltinAction as BuiltinAction,
    Channel as Channel,
    InhibitorArc as InhibitorArc,
    InputSpec as InputSpec,
    Instance as Instance,
    Net as Net,
    NetBuilder as NetBuilder,
    OutputSpec as OutputSpec,
    Place as Place,
    PlaceLike as PlaceLike,
    Port as Port,
    ReadArc as ReadArc,
    ResetArc as ResetArc,
    SubnetDef as SubnetDef,
    SubnetDefBuilder as SubnetDefBuilder,
    SubnetInstance as SubnetInstance,
    Timing as Timing,
    Transition as Transition,
    TransitionBuilder as TransitionBuilder,
    TransitionContext as TransitionContext,
    all_tokens as all_tokens,
    and_ as and_,
    and_outputs as and_outputs,
    at_least as at_least,
    deadline as deadline,
    delayed as delayed,
    exact as exact,
    exactly as exactly,
    fork as fork,
    forward_input as forward_input,
    immediate as immediate,
    inhibitor as inhibitor,
    one as one,
    out as out,
    out_place as out_place,
    passthrough as passthrough,
    read as read,
    reset as reset,
    timeout as timeout,
    window as window,
    xor as xor,
    xor_outputs as xor_outputs,
)
from .runtime import (
    CompiledNet as CompiledNet,
    ExecutorHandle as ExecutorHandle,
    ExecutorOptions as ExecutorOptions,
    MarkingView as MarkingView,
    compile as compile,
    run_async as run_async,
    run_sync as run_sync,
    start_async as start_async,
)
from .verification import (
    PropertyResult as PropertyResult,
    SmtProperty as SmtProperty,
    SubnetVerificationResult as SubnetVerificationResult,
    VerificationHarness as VerificationHarness,
    VerificationResult as VerificationResult,
    deadlock_free as deadlock_free,
    mutual_exclusion as mutual_exclusion,
    place_bound as place_bound,
    unreachable as unreachable,
    verify as verify,
    verify_subnet as verify_subnet,
)

CallbackError = _libpetri.CallbackError
LibpetriError = _libpetri.LibpetriError
StructureError = _libpetri.StructureError

HAS_TOKIO: bool
HAS_Z3: bool
HAS_DEBUG: bool
__version__: str
