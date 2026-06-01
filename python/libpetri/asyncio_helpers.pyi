from collections.abc import Awaitable, Coroutine
from typing import Any, Callable

__all__ = ["action_gather", "action_to_thread"]

def action_gather(*coros: Coroutine[Any, Any, Any]) -> Awaitable[list[Any]]: ...
def action_to_thread(
    fn: Callable[..., Any], /, *args: Any, **kwargs: Any
) -> Awaitable[Any]: ...
