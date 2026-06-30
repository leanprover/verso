// Minimal ambient declarations for the npm packages the run-test widget imports. The widget is
// served as-is to the infoview, which supplies React and the infoview RPC API at runtime, so only
// the surface the widget uses is declared here, enough for `tsc` to type-check the rest.

declare module "react" {
    export function createElement(type: any, props?: any, ...children: any[]): any;
    export function useState(initial: any): [any, (value: any) => void];
    export function useEffect(effect: () => void | (() => void), deps?: any[]): void;
    export function useRef(initial: any): { current: any };
}

declare module "@leanprover/infoview" {
    export function useRpcSession(): {
        call(method: string, params: any): Promise<any>;
    };
}
