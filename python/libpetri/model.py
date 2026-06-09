"""Authoring facade: builders, helpers, type aliases over the Rust model."""

from __future__ import annotations

from typing import TypeAlias

from . import _libpetri as _ext

Place = _ext.Place
InputSpec = _ext.InputSpec
MatchSpec = _ext.MatchSpec
OutputSpec = _ext.OutputSpec
InhibitorArc = _ext.InhibitorArc
ReadArc = _ext.ReadArc
ResetArc = _ext.ResetArc
Timing = _ext.Timing
TransitionContext = _ext.TransitionContext

BuiltTransition = _ext.Transition
TransitionBuilder = _ext.TransitionBuilder
BuiltinAction = _ext.BuiltinAction
fork = _ext.BuiltinAction.Fork
passthrough = _ext.BuiltinAction.Passthrough
BuiltNet = _ext.Net
NetBuilder = _ext.NetBuilder
Port = _ext.Port
Channel = _ext.Channel
SubnetInstance = _ext.SubnetInstance
Instance = _ext.Instance
BuiltSubnetDef = _ext.SubnetDef
SubnetDefBuilder = _ext.SubnetDefBuilder

PlaceLike: TypeAlias = str | Place
OutputLike: TypeAlias = Place | OutputSpec


def _coerce_place_name(place: PlaceLike) -> str:
    if isinstance(place, Place):
        return place.name
    if isinstance(place, str):
        return place
    raise TypeError("expected a Place or place-name string")


def _coerce_output(child: OutputLike) -> OutputSpec:
    if isinstance(child, OutputSpec):
        return child
    if isinstance(child, Place):
        return _ext.out_place(child)
    raise TypeError("expected a Place or OutputSpec")


def _coerce_net(net: BuiltNet) -> BuiltNet:
    if not isinstance(net, BuiltNet):
        raise TypeError("expected a built Net; call .build() on the builder first")
    return net


def _coerce_subnet(subnet: BuiltSubnetDef) -> BuiltSubnetDef:
    if not isinstance(subnet, BuiltSubnetDef):
        raise TypeError("expected a built SubnetDef; call .build() on the builder first")
    return subnet


def Transition(name: str) -> TransitionBuilder:
    return TransitionBuilder(name)


def Net(name: str) -> NetBuilder:
    return NetBuilder(name)


def SubnetDef(name: str) -> SubnetDefBuilder:
    return SubnetDefBuilder(name)


one = _ext.one
exactly = _ext.exactly
all_tokens = _ext.all_tokens
at_least = _ext.at_least
match_spec = _ext.match_spec
out_place = _ext.out_place
out = out_place
forward_input = _ext.forward_input
inhibitor = _ext.inhibitor
read = _ext.read
reset = _ext.reset
immediate = _ext.immediate
deadline = _ext.deadline
delayed = _ext.delayed
window = _ext.window
exact = _ext.exact


def and_(*children: OutputLike) -> OutputSpec:
    return _ext.and_outputs([_coerce_output(child) for child in children])


def and_outputs(*children: OutputLike) -> OutputSpec:
    return and_(*children)


def xor(*children: OutputLike) -> OutputSpec:
    return _ext.xor_outputs([_coerce_output(child) for child in children])


def xor_outputs(*children: OutputLike) -> OutputSpec:
    return xor(*children)


def timeout(after_ms: int, child: OutputLike) -> OutputSpec:
    return _ext.timeout_output(after_ms, _coerce_output(child))


__all__ = [
    "BuiltNet",
    "BuiltSubnetDef",
    "BuiltTransition",
    "BuiltinAction",
    "Channel",
    "fork",
    "passthrough",
    "InputSpec",
    "Instance",
    "InhibitorArc",
    "MatchSpec",
    "match_spec",
    "Net",
    "NetBuilder",
    "OutputSpec",
    "Place",
    "PlaceLike",
    "Port",
    "ReadArc",
    "ResetArc",
    "SubnetDef",
    "SubnetDefBuilder",
    "SubnetInstance",
    "Timing",
    "Transition",
    "TransitionBuilder",
    "TransitionContext",
    "all_tokens",
    "and_",
    "and_outputs",
    "at_least",
    "deadline",
    "delayed",
    "exact",
    "exactly",
    "forward_input",
    "immediate",
    "inhibitor",
    "one",
    "out",
    "out_place",
    "read",
    "reset",
    "timeout",
    "window",
    "xor",
    "xor_outputs",
]
