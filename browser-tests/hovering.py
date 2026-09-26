from playwright.sync_api import Locator

# The hovers that `hover_for_tooltip` makes before it gives up on a `mouseenter` reaching the
# tooltip's reference.
HOVER_ATTEMPTS = 5

# Installs a one-shot `mouseenter` listener on an element that sets a flag on the element.
LISTEN_FOR_MOUSEENTER = """el => {
    el.__hoverEntered = false;
    el.addEventListener('mouseenter', () => { el.__hoverEntered = true; }, { once: true });
}"""


def hover_for_tooltip(target: Locator, tooltip: Locator, reference: Locator | None = None) -> None:
    """
    Hover ``target`` and wait until ``tooltip`` is visible.

    ``reference`` is the element whose Tippy instance shows the tooltip: ``target`` itself or an
    element that contains it. It defaults to ``target``. The helper proceeds in three steps:

    1. It waits until ``reference`` has a Tippy instance.
    2. It hovers ``target`` and checks that ``reference`` received ``mouseenter``. If it received
       none, the pointer moves to the page's corner and the hover repeats, up to
       ``HOVER_ATTEMPTS`` hovers in all; then an assertion fails that names the target.
    3. It waits until ``tooltip`` is visible.

    The waits of steps 1 and 3 use Playwright's default timeout.
    """
    page = target.page
    if reference is None:
        reference = target
    reference.wait_for(state="attached")
    page.wait_for_function("el => !!el._tippy", arg=reference.element_handle())
    for _ in range(HOVER_ATTEMPTS):
        reference.evaluate(LISTEN_FOR_MOUSEENTER)
        target.hover()
        if reference.evaluate("el => el.__hoverEntered"):
            tooltip.wait_for(state="visible")
            return
        page.mouse.move(0, 0)
    raise AssertionError(
        f"The pointer's mouseenter never reached {reference} in {HOVER_ATTEMPTS} hovers of {target}"
    )
