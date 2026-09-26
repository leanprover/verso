import time

from playwright.sync_api import Locator, TimeoutError as PlaywrightTimeoutError


def hover_for_tooltip(
    target: Locator,
    tooltip: Locator,
    timeout_ms: float = 30_000,
    attempt_ms: float = 2_000,
) -> None:
    """Hover ``target`` until ``tooltip`` is visible.

    Each attempt hovers ``target`` and waits up to ``attempt_ms`` for ``tooltip``. If the tooltip
    stays hidden, the pointer moves to the page's corner and the next attempt hovers again. After
    ``timeout_ms`` in total, an assertion fails that names the target and the tooltip.
    """
    page = target.page
    deadline = time.monotonic() + timeout_ms / 1000

    def remaining_ms() -> float:
        return max(1.0, (deadline - time.monotonic()) * 1000)

    while True:
        target.hover(timeout=remaining_ms())
        try:
            tooltip.wait_for(state="visible", timeout=min(attempt_ms, remaining_ms()))
            return
        except PlaywrightTimeoutError:
            pass
        if time.monotonic() >= deadline:
            raise AssertionError(
                f"Hovering {target} for {timeout_ms / 1000:g} s never showed {tooltip}"
            )
        page.mouse.move(0, 0)
