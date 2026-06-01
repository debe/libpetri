"""Session archive (v3) read/write.

Wraps `libpetri_debug::archive::*` — gzip-compressed, length-prefixed binary
archives wire-compatible with the TypeScript and Rust readers. The writer
takes a Rust-side `InMemoryEventStore` handle and serializes on a Rust
thread with the GIL released; events never round-trip through Python.

Available only when the wheel was built with the `archive` feature
(`libpetri.HAS_ARCHIVE == True`).
"""

from __future__ import annotations

from . import _libpetri as _ext

if not _ext.HAS_ARCHIVE:
    raise ImportError(
        "libpetri wheel was built without the 'archive' feature; "
        "rebuild with `maturin develop --features full archive`."
    )

ComputedState = _ext.ComputedState
MarkingCache = _ext.MarkingCache
SessionArchive = _ext.SessionArchive
SessionArchiveReader = _ext.SessionArchiveReader
SessionArchiveWriter = _ext.SessionArchiveWriter


__all__ = [
    "ComputedState",
    "MarkingCache",
    "SessionArchive",
    "SessionArchiveReader",
    "SessionArchiveWriter",
]
