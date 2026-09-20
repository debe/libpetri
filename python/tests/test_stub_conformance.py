"""The shipped ``.pyi`` stubs are a boundary: ``py.typed`` makes them the only
thing a type checker sees, so a stub that drifts from the runtime turns every
correct call into a type error (or hides a wrong one) without a single test
going red. These tests compare each stub against the module it describes by
introspection — names, parameters, parameter kinds, which parameters carry a
default, and dataclass shape.

They do not check annotations; that needs a type checker. They catch what has
actually gone wrong here: a dataclass field that lost its ``= ...``, names
exported from ``__init__.py`` but not from ``__init__.pyi``, and a frozen
dataclass declared as a plain class.
"""

from __future__ import annotations

import ast
import dataclasses
import importlib
import inspect
from pathlib import Path

import pytest

import libpetri as lp

PACKAGE_DIR = Path(lp.__file__).parent

MODULES = [
    "libpetri",
    "libpetri.archive",
    "libpetri.asyncio_helpers",
    "libpetri.debug",
    "libpetri.events",
    "libpetri.export",
    "libpetri.model",
    "libpetri.runtime",
    "libpetri.verification",
    "libpetri._libpetri",
]


def _stub_path(module_name: str) -> Path:
    leaf = module_name.split(".", 1)[1] if "." in module_name else "__init__"
    return PACKAGE_DIR / f"{leaf}.pyi"


def _parse(module_name: str) -> ast.Module:
    return ast.parse(_stub_path(module_name).read_text(encoding="utf-8"))


def _declared(body: list[ast.stmt]) -> dict[str, ast.AST]:
    """Every name a stub body binds: imports, assignments, annotated names,
    functions and classes — descending into ``if`` blocks, which stubs use
    for feature-gated names."""
    names: dict[str, ast.AST] = {}
    for node in body:
        if isinstance(node, (ast.Import, ast.ImportFrom)):
            for alias in node.names:
                names[(alias.asname or alias.name).split(".")[0]] = node
        elif isinstance(node, ast.Assign):
            for target in node.targets:
                if isinstance(target, ast.Name):
                    names[target.id] = node
        elif isinstance(node, ast.AnnAssign) and isinstance(node.target, ast.Name):
            names[node.target.id] = node
        elif isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
            # An `@overload` set binds the name once; keep the first.
            names.setdefault(node.name, node)
        elif isinstance(node, ast.If):
            for name, inner in _declared(node.body + node.orelse).items():
                names.setdefault(name, inner)
    return names


def _stub_params(fn: ast.FunctionDef | ast.AsyncFunctionDef) -> list[tuple[str, str, bool]]:
    """``(name, kind, has_default)`` per parameter, in ``inspect`` vocabulary."""
    a = fn.args
    out: list[tuple[str, str, bool]] = []
    positional = a.posonlyargs + a.args
    first_default = len(positional) - len(a.defaults)
    for i, arg in enumerate(positional):
        kind = "POSITIONAL_ONLY" if i < len(a.posonlyargs) else "POSITIONAL_OR_KEYWORD"
        out.append((arg.arg, kind, i >= first_default))
    if a.vararg:
        out.append((a.vararg.arg, "VAR_POSITIONAL", False))
    for arg, default in zip(a.kwonlyargs, a.kw_defaults, strict=True):
        out.append((arg.arg, "KEYWORD_ONLY", default is not None))
    if a.kwarg:
        out.append((a.kwarg.arg, "VAR_KEYWORD", False))
    return out


def _runtime_params(obj: object) -> list[tuple[str, str, bool]] | None:
    try:
        sig = inspect.signature(obj)  # type: ignore[arg-type]
    except (TypeError, ValueError):
        return None  # a builtin without a text signature: nothing to compare
    return [
        (p.name, p.kind.name, p.default is not inspect.Parameter.empty)
        for p in sig.parameters.values()
    ]


def _is_overload(fn: ast.AST) -> bool:
    return any(
        (isinstance(d, ast.Name) and d.id == "overload")
        or (isinstance(d, ast.Attribute) and d.attr == "overload")
        for d in getattr(fn, "decorator_list", [])
    )


def _decorator_names(node: ast.AST) -> set[str]:
    out = set()
    for d in getattr(node, "decorator_list", []):
        d = d.func if isinstance(d, ast.Call) else d
        out.add(d.id if isinstance(d, ast.Name) else getattr(d, "attr", ""))
    return out


def _drop_self(params: list[tuple[str, str, bool]]) -> list[tuple[str, str, bool]]:
    return params[1:] if params and params[0][0] in {"self", "cls"} else params


def _compare_callable(where: str, stub_fn, runtime_obj, problems: list[str], *, method: bool) -> None:
    if _is_overload(stub_fn):
        return  # the overloads jointly describe one signature; not comparable 1:1
    expected = _runtime_params(runtime_obj)
    if expected is None:
        return
    declared = _stub_params(stub_fn)
    if method:
        declared, expected = _drop_self(declared), _drop_self(expected)
    # Positional-only vs positional-or-keyword is not observable from a PyO3
    # text signature in a way stubs mirror; everything else must match.
    norm = lambda ps: [  # noqa: E731
        (n, "POSITIONAL" if k.startswith("POSITIONAL_") else k, d) for n, k, d in ps
    ]
    if norm(declared) != norm(expected):
        problems.append(f"{where}: stub {declared} != runtime {expected}")


def _compare_class(where: str, stub_cls: ast.ClassDef, runtime_cls: type, problems: list[str]) -> None:
    stub_members = _declared(stub_cls.body)

    # Dataclass shape: decorator, frozen-ness, and which fields have defaults.
    stub_is_dc = "dataclass" in _decorator_names(stub_cls)
    if dataclasses.is_dataclass(runtime_cls) != stub_is_dc:
        problems.append(
            f"{where}: runtime dataclass={dataclasses.is_dataclass(runtime_cls)} "
            f"but stub dataclass={stub_is_dc}"
        )
    elif stub_is_dc:
        runtime_frozen = runtime_cls.__dataclass_params__.frozen  # type: ignore[attr-defined]
        stub_frozen = any(
            isinstance(d, ast.Call)
            and any(k.arg == "frozen" and getattr(k.value, "value", False) for k in d.keywords)
            for d in stub_cls.decorator_list
        )
        if runtime_frozen != stub_frozen:
            problems.append(f"{where}: frozen={runtime_frozen} at runtime, {stub_frozen} in stub")
        stub_fields = [
            (n.target.id, n.value is not None)
            for n in stub_cls.body
            if isinstance(n, ast.AnnAssign) and isinstance(n.target, ast.Name)
        ]
        runtime_fields = [
            (
                f.name,
                f.default is not dataclasses.MISSING
                or f.default_factory is not dataclasses.MISSING,
            )
            for f in dataclasses.fields(runtime_cls)
        ]
        if stub_fields != runtime_fields:
            problems.append(
                f"{where}: dataclass fields (name, has_default) stub {stub_fields} "
                f"!= runtime {runtime_fields}"
            )

    # Every public member the class itself defines must be in the stub...
    for name, member in vars(runtime_cls).items():
        if name.startswith("_"):
            continue
        if name not in stub_members:
            problems.append(f"{where}.{name}: defined at runtime, missing from stub")
    # ...and every stub member must exist, with a matching signature.
    for name, node in stub_members.items():
        if isinstance(node, (ast.Import, ast.ImportFrom)):
            continue
        if name.startswith("__") and name not in vars(runtime_cls) and name != "__init__":
            if not hasattr(runtime_cls, name):
                problems.append(f"{where}.{name}: in stub, missing at runtime")
            continue
        if not hasattr(runtime_cls, name):
            # A dataclass(slots=True) field or an instance attribute set in
            # __init__ is legitimately absent from the class object.
            if isinstance(node, ast.AnnAssign):
                continue
            problems.append(f"{where}.{name}: in stub, missing at runtime")
            continue
        if not isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            continue
        raw = inspect.getattr_static(runtime_cls, name)
        decorators = _decorator_names(node)
        if "property" in decorators or name + ".setter" in decorators:
            continue
        if name == "__init__":
            if stub_is_dc:
                continue
            target = runtime_cls  # signature(cls) covers both __init__ and PyO3 __new__
            declared = _drop_self(_stub_params(node))
            expected = _runtime_params(target)
            if expected is None:
                continue
            norm = lambda ps: [  # noqa: E731
                (n, "POSITIONAL" if k.startswith("POSITIONAL_") else k, d) for n, k, d in ps
            ]
            if norm(declared) != norm(expected):
                problems.append(f"{where}.__init__: stub {declared} != runtime {expected}")
            continue
        is_static = isinstance(raw, staticmethod) or "staticmethod" in decorators
        if isinstance(node, ast.AsyncFunctionDef) != inspect.iscoroutinefunction(
            getattr(runtime_cls, name)
        ) and not module_is_native(runtime_cls):
            problems.append(f"{where}.{name}: async-ness differs between stub and runtime")
        _compare_callable(
            f"{where}.{name}", node, getattr(runtime_cls, name), problems, method=not is_static
        )


def module_is_native(cls: type) -> bool:
    return getattr(cls, "__module__", "") in {"_libpetri", "builtins"}


@pytest.mark.parametrize("module_name", MODULES)
def test_stub_matches_runtime(module_name: str) -> None:
    module = importlib.import_module(module_name)
    declared = _declared(_parse(module_name).body)
    problems: list[str] = []

    exported = getattr(module, "__all__", None)
    if exported is None:
        exported = [n for n in vars(module) if not n.startswith("_")]
        # A native module re-exports nothing; a Python one may import helpers.
        if module_name != "libpetri._libpetri":
            exported = [
                n
                for n in exported
                if getattr(vars(module)[n], "__module__", module_name) == module_name
            ]
    for name in exported:
        if name not in declared:
            problems.append(f"{module_name}.{name}: exported at runtime, missing from stub")

    for name, node in declared.items():
        if isinstance(node, (ast.Import, ast.ImportFrom)):
            if module_name == "libpetri" and not hasattr(module, name) and name != "annotations":
                problems.append(f"{module_name}.{name}: re-exported by stub, missing at runtime")
            continue
        if name.startswith("_") and not name.startswith("__"):
            continue
        if not hasattr(module, name):
            problems.append(f"{module_name}.{name}: in stub, missing at runtime")
            continue
        obj = getattr(module, name)
        if isinstance(node, ast.ClassDef) and inspect.isclass(obj):
            _compare_class(f"{module_name}.{name}", node, obj, problems)
        elif isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            if isinstance(node, ast.AsyncFunctionDef) != inspect.iscoroutinefunction(obj):
                problems.append(f"{module_name}.{name}: async-ness differs")
            _compare_callable(f"{module_name}.{name}", node, obj, problems, method=False)

    assert not problems, "stub drift:\n  " + "\n  ".join(problems)


def test_runtime_all_names_the_snapshot_result() -> None:
    """`ExecutorHandle.snapshot()` returns it, so `from libpetri.runtime import *`
    must bring it in."""
    import libpetri.runtime as rt

    assert "SnapshotResult" in vars(rt)["__all__"]
