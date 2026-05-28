"""DOT export facade."""

from __future__ import annotations

from . import _libpetri as _ext
from .model import BuiltNet, _coerce_net

RankDir = _ext.RankDir
DotConfig = _ext.DotConfig


def dot_export(net: BuiltNet, config: DotConfig | None = None) -> str:
    return _ext.dot_export(_coerce_net(net), config)


__all__ = ["DotConfig", "RankDir", "dot_export"]
