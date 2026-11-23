// The editor that hosts the InfoView in the widget tests. It stands in for the Lean extension of
// VS Code: it relays LSP messages between the InfoView and the Lean server that the test harness
// runs, and it records what the InfoView asks of the editor so tests can check it.
//
// Messages to the server are posted to `/lsp`. Messages from the server, replies and notifications
// alike, are collected by a long-running `GET /lsp` that the page repeats for as long as it is open.
// The request names the page by the prefix of its request ids, so the collection that a page left
// waiting when it was loaded again takes none of the messages meant for the page that replaced it.

import { loadRenderInfoview } from "/infoview/loader.production.min.js";

/** @import { EditorApi, InfoviewApi } from "@leanprover/infoview" */

/**
 * @typedef {{id?: string | number, method?: string, params?: unknown, result?: unknown,
 *   error?: unknown}} Message a JSON-RPC message from the server
 */

/** @type {Map<string, {resolve: (result: unknown) => void, reject: (error: unknown) => void}>} */
const pending = new Map();
let nextId = 0;
// A random prefix for this page's request ids. The tests of a session share one Lean server, so a
// reply to a request from an earlier test's page can arrive while this page is open, and the prefix
// keeps it from matching one of this page's requests.
const idPrefix = Math.random().toString(36).slice(2);

// How many times the InfoView has subscribed to each notification, by method.
/** @type {Map<string, number>} */
const serverSubscriptions = new Map();
/** @type {Map<string, number>} */
const clientSubscriptions = new Map();

// What the InfoView asked of the editor, in order, for tests to inspect.
/** @type {Record<string, unknown>[]} */
const editorCalls = [];
// The text that the InfoView asked the editor to copy to the clipboard, in order.
/** @type {string[]} */
const copied = [];

/** @param message {object} */
function post(message) {
    return fetch("/lsp", { method: "POST", body: JSON.stringify(message) });
}

/**
 * @param method {string}
 * @param params {unknown}
 * @returns {Promise<unknown>}
 */
function request(method, params) {
    const id = "page-" + idPrefix + "-" + nextId++;
    return new Promise(function (resolve, reject) {
        pending.set(id, { resolve, reject });
        post({ jsonrpc: "2.0", id, method, params }).catch(function (err) {
            pending.delete(id);
            reject(err);
        });
    });
}

/**
 * @param subscriptions {Map<string, number>}
 * @param method {string}
 * @param delta {number}
 */
function count(subscriptions, method, delta) {
    subscriptions.set(method, (subscriptions.get(method) || 0) + delta);
}

/**
 * @param subscriptions {Map<string, number>}
 * @param method {string}
 */
function subscribed(subscriptions, method) {
    return (subscriptions.get(method) || 0) > 0;
}

/** @type {InfoviewApi | null} */
let infoview = null;
/** @type {() => void} */
let infoviewReady = function () {};
/** @type {Promise<void>} */
const ready = new Promise(function (resolve) {
    infoviewReady = resolve;
});

/** The InfoView, which the harness drives once it has loaded. */
function loadedInfoview() {
    if (!infoview) throw new Error("the InfoView has not loaded");
    return infoview;
}

// The keep-alive timers of the open RPC sessions, by session.
/** @type {Map<string, number>} */
const keepAlive = new Map();

/** @type {EditorApi} */
const editorApi = {
    saveConfig: async function () {},
    sendClientRequest: async function (_uri, method, params) {
        return request(method, params);
    },
    sendClientNotification: async function (_uri, method, params) {
        await post({ jsonrpc: "2.0", method, params });
    },
    subscribeServerNotifications: async function (method) {
        count(serverSubscriptions, method, 1);
    },
    unsubscribeServerNotifications: async function (method) {
        count(serverSubscriptions, method, -1);
    },
    subscribeClientNotifications: async function (method) {
        count(clientSubscriptions, method, 1);
    },
    unsubscribeClientNotifications: async function (method) {
        count(clientSubscriptions, method, -1);
    },
    copyToClipboard: async function (text) {
        copied.push(text);
    },
    insertText: async function (text, kind, pos) {
        editorCalls.push({ kind: "insertText", text, insertKind: kind, pos });
    },
    applyEdit: async function (edit) {
        editorCalls.push({ kind: "applyEdit", edit });
    },
    showDocument: async function (show) {
        editorCalls.push({ kind: "showDocument", show });
    },
    restartFile: async function (uri) {
        editorCalls.push({ kind: "restartFile", uri });
    },
    createRpcSession: async function (uri) {
        const reply = /** @type {{sessionId: string}} */ (
            await request("$/lean/rpc/connect", { uri })
        );
        const sessionId = reply.sessionId;
        keepAlive.set(
            sessionId,
            setInterval(function () {
                post({
                    jsonrpc: "2.0",
                    method: "$/lean/rpc/keepAlive",
                    params: { uri, sessionId },
                });
            }, 5000),
        );
        return sessionId;
    },
    closeRpcSession: async function (sessionId) {
        clearInterval(keepAlive.get(sessionId));
        keepAlive.delete(sessionId);
    },
};

/** @param message {Message} */
function receive(message) {
    const waiter = typeof message.id === "string" ? pending.get(message.id) : undefined;
    if (typeof message.id === "string" && waiter) {
        pending.delete(message.id);
        if (message.error) waiter.reject(message.error);
        else waiter.resolve(message.result);
    } else if (message.method && infoview && subscribed(serverSubscriptions, message.method)) {
        infoview.gotServerNotification(message.method, message.params);
    }
}

async function poll() {
    for (;;) {
        /** @type {Message[]} */
        let messages;
        try {
            const reply = await fetch("/lsp?page=" + idPrefix);
            messages = await reply.json();
        } catch (err) {
            await new Promise(function (resolve) {
                setTimeout(resolve, 100);
            });
            continue;
        }
        for (const message of messages) receive(message);
    }
}

/**
 * @typedef {Parameters<InfoviewApi["initialize"]>[0]} Location a place in a document
 * @typedef {Parameters<InfoviewApi["serverRestarted"]>[0]} InitializeResult the server's reply to
 *   `initialize`
 */

// The operations the test harness drives the editor with, through `page.evaluate`.
const harness = {
    ready,
    editorCalls,
    copied,
    /**
     * Starts the InfoView at a place in a document, connected to a server that has just started.
     * @param location {Location}
     * @param initializeResult {InitializeResult}
     */
    start: async function (location, initializeResult) {
        await ready;
        const { defaultInfoviewConfig } = /** @type {typeof import("@leanprover/infoview")} */ (
            await importShim("@leanprover/infoview")
        );
        await loadedInfoview().initialize(location);
        await loadedInfoview().changedInfoviewConfig(defaultInfoviewConfig);
        await loadedInfoview().serverRestarted(initializeResult);
    },
    /** @param location {Location} */
    moveCursor: async function (location) {
        await loadedInfoview().changedCursorLocation(location);
    },
    /** @param initializeResult {InitializeResult} */
    serverRestarted: async function (initializeResult) {
        await loadedInfoview().serverRestarted(initializeResult);
    },
    /**
     * Tells the InfoView about a notification that the editor sent to the server.
     * @param method {string}
     * @param params {unknown}
     */
    sentClientNotification: async function (method, params) {
        if (subscribed(clientSubscriptions, method)) {
            await loadedInfoview().sentClientNotification(method, params);
        }
    },
};
Object.assign(window, { harness });

poll();

const origin = window.location.origin;
const container = document.getElementById("infoview");
if (!container) throw new Error("the page has no element for the InfoView");
loadRenderInfoview(
    {
        "@leanprover/infoview": origin + "/infoview/index.production.min.js",
        react: origin + "/infoview/react.production.min.js",
        "react/jsx-runtime": origin + "/infoview/react-jsx-runtime.production.min.js",
        "react-dom": origin + "/infoview/react-dom.production.min.js",
    },
    [editorApi, container],
    function (api) {
        infoview = api;
        infoviewReady();
    },
);
