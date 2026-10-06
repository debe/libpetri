from collections.abc import Awaitable, Coroutine
from typing import Any, Callable, TypeVar

_T = TypeVar("_T")

__all__ = ["action_gather", "action_on_loop", "action_to_thread"]

def action_gather(*coros: Coroutine[Any, Any, Any]) -> Awaitable[list[Any]]: ...
def action_on_loop(coro: Coroutine[Any, Any, _T]) -> Awaitable[_T]: ...
def action_to_thread(
    fn: Callable[..., Any], /, *args: Any, **kwargs: Any
) -> Awaitable[Any]: ...
