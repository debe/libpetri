"""Type stubs for the libpetri public surface."""

from __future__ import annotations

from . import _libpetri
from .asyncio_helpers import (
    action_gather as action_gather,
    action_to_thread as action_to_thread,
)
from .debug import (
    DebugProtocolHandler as DebugProtocolHandler,
    SessionSummary as SessionSummary,
    require_debug as require_debug,
)
from .archive import (
    ComputedState as ComputedState,
    MarkingCache as MarkingCache,
    SessionArchive as SessionArchive,
    SessionArchiveReader as SessionArchiveReader,
    SessionArchiveWriter as SessionArchiveWriter,
)
from .events import (
    EventStream as EventStream,
    EventSubscription as EventSubscription,
    InMemoryEventStore as InMemoryEventStore,
    NetEvent as NetEvent,
)
from .export import (
    DotConfig as DotConfig,
    RankDir as RankDir,
    dot_export as dot_export,
)
from .model import (
    BuiltInterface as BuiltInterface,
    BuiltNet as BuiltNet,
    BuiltSubnetDef as BuiltSubnetDef,
    BuiltTransition as BuiltTransition,
    BuiltinAction as BuiltinAction,
    Channel as Channel,
    InhibitorArc as InhibitorArc,
    InputSpec as InputSpec,
    Instance as Instance,
    Interface as Interface,
    InterfaceBuilder as InterfaceBuilder,
    MatchSpec as MatchSpec,
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
    match_spec as match_spec,
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
    SnapshotResult as SnapshotResult,
    compile as compile,
    run_async as run_async,
    run_sync as run_sync,
    start_async as start_async,
)
from .verification import (
    ContractViolation as ContractViolation,
    EnvironmentAnalysisMode as EnvironmentAnalysisMode,
    OpenNetContract as OpenNetContract,
    OpenNetContractBuilder as OpenNetContractBuilder,
    OpenNetResult as OpenNetResult,
    PortStep as PortStep,
    PropertyResult as PropertyResult,
    SmtProperty as SmtProperty,
    StateSpaceCache as StateSpaceCache,
    SubnetVerificationResult as SubnetVerificationResult,
    VerificationHarness as VerificationHarness,
    VerificationResult as VerificationResult,
    always_available as always_available,
    bounded as bounded,
    branch_place_bound as branch_place_bound,
    deadlock_free as deadlock_free,
    terminates_at_sink as terminates_at_sink,
    ignore as ignore,
    joined_or_dead_lettered as joined_or_dead_lettered,
    mutual_exclusion as mutual_exclusion,
    place_bound as place_bound,
    quiescent_count as quiescent_count,
    unreachable as unreachable,
    encode_smt_scripts as encode_smt_scripts,
    verify as verify,
    verify_open_net as verify_open_net,
    verify_subnet as verify_subnet,
    z3_available as z3_available,
)

CallbackError = _libpetri.CallbackError
LibpetriError = _libpetri.LibpetriError
StructureError = _libpetri.StructureError

HAS_TOKIO: bool
HAS_Z3: bool
HAS_DEBUG: bool
HAS_ARCHIVE: bool
__version__: str
