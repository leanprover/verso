// Minimal ambient declarations for the npm packages the run-test widget imports. The widget is
// served as-is to the InfoView, which supplies React and the InfoView RPC API at runtime, so only
// the surface the widget uses is declared here, enough for `tsc` to type-check the rest.

declare module "react" {
    export function createElement(type: any, props?: any, ...children: any[]): any;
    export function useState(initial: any): [any, (value: any) => void];
    export function useReducer<S, A>(
        reducer: (state: S, action: A) => S,
        initialArg: any,
        init?: (arg: any) => S,
    ): [S, (action: A) => void];
    export function useEffect(effect: () => void | (() => void), deps?: any[]): void;
    export function useRef(initial: any): { current: any };
    export function useContext(context: any): any;
    export function memo<T>(component: T): T;
    export interface ToggleEvent<T = Element> {
        currentTarget: T;
        target: EventTarget;
    }
}

declare module "react-dom" {
    export function createPortal(children: any, container: Element): any;
}

declare module "@leanprover/infoview" {
    export function useRpcSession(): {
        call(method: string, params: any): Promise<any>;
    };
    export const EnvPosContext: any;
    export const EditorContext: any;
    export function Markdown(props: { contents: string }): any;
    export function useClientNotificationEffect(
        method: string,
        f: (params: any) => void,
        deps?: any[],
    ): void;
    export function useEvent(ev: any, f: (value: any) => void, deps?: any[], key?: any): void;
}
