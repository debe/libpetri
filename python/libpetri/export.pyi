"""Type stubs for libpetri.export."""

from __future__ import annotations

from typing import TypeAlias

from . import _libpetri as _ext
from .model import BuiltNet

RankDir: TypeAlias = _ext.RankDir
DotConfig: TypeAlias = _ext.DotConfig

def dot_export(net: BuiltNet, config: DotConfig | None = ...) -> str: ...
