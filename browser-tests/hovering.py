from playwright.sync_api import Locator, TimeoutError

# The hovers that `hover_for_tooltip` makes before it gives up on a `mouseenter` reaching the
# tooltip's reference.
HOVER_ATTEMPTS = 5

# Installs a one-shot `mouseenter` listener on an element that sets a flag on the element, and
# records the pointer events that reach the element and the triggers of its Tippy instance, each
# with its time, for the message of a tooltip that never became visible.
LISTEN_FOR_MOUSEENTER = """el => {
    el.__hoverEntered = false;
    el.addEventListener('mouseenter', () => { el.__hoverEntered = true; }, { once: true });
    if (!el.__hoverTrace) {
        el.__hoverTrace = [];
        const note = what => el.__hoverTrace.push(`${what}@${Math.round(performance.now())}`);
        for (const type of ['mouseenter', 'mouseleave', 'mouseover', 'mouseout']) {
            el.addEventListener(type, () => note(type));
        }
        if (el._tippy && el._tippy.setProps) {
            el._tippy.setProps({
                onTrigger: (_, event) => note(`trigger:${event.type}`),
                onUntrigger: (_, event) => note(`untrigger:${event.type}`),
            });
        }
    }
    el.__hoverTrace.push(`hover@${Math.round(performance.now())}`);
}"""

# Describes the state of a tooltip's reference and of the element under the center of the hovered
# target, for the message of a tooltip that never became visible.
DESCRIBE_HOVER = """(el, box) => {
    const describe = e => e ? `${e.tagName.toLowerCase()}.${[...e.classList].join('.')}` : 'none';
    const x = box.x + box.width / 2, y = box.y + box.height / 2;
    const under = document.elementFromPoint(x, y);
    const chain = [];
    for (let e = under; e && e !== el.parentElement; e = e.parentElement) {
        chain.push(describe(e) + (e._tippy ? ' (tippy)' : ''));
    }
    const state = el._tippy ? el._tippy.state : null;
    const toggle = el.querySelector(':scope > input.tactic-toggle');
    return JSON.stringify({
        reference: describe(el),
        tippyState: state && {
            isEnabled: state.isEnabled, isVisible: state.isVisible,
            isShown: state.isShown, isMounted: state.isMounted, isDestroyed: state.isDestroyed },
        toggleChecked: toggle ? toggle.checked : null,
        pointAt: [Math.round(x), Math.round(y)],
        underPointer: chain,
        tippyBoxes: document.querySelectorAll('.tippy-box').length,
        visibility: document.visibilityState,
        focused: document.hasFocus(),
        now: Math.round(performance.now()),
        trace: el.__hoverTrace || [],
    });
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
    missed = 0
    for _ in range(HOVER_ATTEMPTS):
        reference.evaluate(LISTEN_FOR_MOUSEENTER)
        target.hover()
        if reference.evaluate("el => el.__hoverEntered"):
            try:
                tooltip.wait_for(state="visible")
            except TimeoutError as error:
                raise AssertionError(
                    f"{tooltip} never became visible after mouseenter reached {reference} "
                    f"({missed} hovers without mouseenter before it): "
                    f"{reference.evaluate(DESCRIBE_HOVER, target.bounding_box())}"
                ) from error
            return
        missed += 1
        page.mouse.move(0, 0)
    raise AssertionError(
        f"The pointer's mouseenter never reached {reference} in {HOVER_ATTEMPTS} hovers of {target}"
    )
