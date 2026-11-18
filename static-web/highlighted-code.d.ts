// Declarations for the globals that highlighted-code.js uses. Tippy.js is loaded from
// vendored-js/tippy, and highlightingJs defines versoLoadDocData.

interface TippyInstance {
    reference: HTMLElement;
    show(): void;
    hide(): void;
    destroy(): void;
}

interface TippyProps {
    maxWidth?: string;
    appendTo?: () => Element;
    interactive?: boolean;
    delay?: [number | null, number | null];
    followCursor?: string;
    onShow?(instance: TippyInstance): boolean;
    onShown?(instance: TippyInstance): void;
    onHidden?(instance: TippyInstance): void;
    content?(reference: HTMLElement): Element;
}

declare function tippy(targets: Element | Element[], props: TippyProps): unknown;

declare function versoRenderMath(root: ParentNode): void;

interface Element {
    _tippy?: TippyInstance;
}

interface Window {
    versoLoadDocData(): Promise<Record<string, string>>;
}
