"""
The test harness for the Errata widget: a Lean language server, a page that hosts the real InfoView
connected to it, and an editor that the tests drive in place of VS Code.

The browser reaches the server through a small HTTP relay. The relay can hold or reject particular
RPC calls, which lets a test arrange the order in which replies arrive.

One Lean server serves every test in a session. Under Errata, one Lean server serves every test of
a run: the suite's Errata fixture starts this module as a host process, `python harness.py serve
READY`, which starts the server and serves one test at a time over TCP (`LeanHost`), and each test
reaches it through a `RemoteLeanSession`. Each test gets its own page and relay. When a test ends,
the editor ends the test's builds and runs and closes the documents it opened, which ends their file
workers.
"""

import json
import mimetypes
import os
import signal
import socket
import subprocess
import sys
import threading
import time
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path

REPO = Path(__file__).resolve().parents[2]
FIXTURE = REPO / "test-projects" / "errata-widget"
PAGE = Path(__file__).resolve().parent / "page"
INFOVIEW = REPO / "node_modules" / "@leanprover" / "infoview" / "dist"


class LspError(Exception):
    """An error reply from the Lean server, or the server's exit before it replied."""


def children(pid):
    """The process ids of the processes whose parent is `pid`."""
    found = subprocess.run(["pgrep", "-P", str(pid)], capture_output=True, text=True)
    return [int(child) for child in found.stdout.split()]


def descendants(pid):
    """The process ids of every process below `pid`."""
    found = []
    waiting = [pid]
    while waiting:
        for child in children(waiting.pop()):
            found.append(child)
            waiting.append(child)
    return found


def matching(pattern):
    """The process ids of the processes whose command lines match `pattern`."""
    found = subprocess.run(["pgrep", "-f", pattern], capture_output=True, text=True)
    return {int(pid) for pid in found.stdout.split()}


def kill_trees(pids):
    """
    Kills processes and every process below them. Each process is stopped before its children are
    looked up, so a process can neither start another nor exit while the tree is gathered, and the
    process ids that are killed all still name the processes that were found.
    """
    stopped = []
    waiting = list(pids)
    while waiting:
        pid = waiting.pop()
        if pid in stopped:
            continue
        try:
            os.kill(pid, signal.SIGSTOP)
        except ProcessLookupError:
            continue
        stopped.append(pid)
        waiting.extend(children(pid))
    for pid in stopped:
        try:
            os.kill(pid, signal.SIGKILL)
        except ProcessLookupError:
            pass


def frame(message):
    """A message as LSP frames it: a `Content-Length` header, a blank line, and the JSON body."""
    body = json.dumps(message).encode("utf-8")
    return f"Content-Length: {len(body)}\r\n\r\n".encode("ascii") + body


def read_message(stream):
    """The next LSP message of a byte stream, or `None` at the stream's end."""
    length = None
    while True:
        line = stream.readline()
        if not line:
            return None
        line = line.strip()
        if not line:
            break
        name, _, value = line.decode("ascii").partition(":")
        if name.lower() == "content-length":
            length = int(value)
    if length is None:
        raise LspError("an LSP message had no Content-Length")
    return json.loads(stream.read(length))


class LspPeer:
    """
    The harness's end of an LSP connection over a pair of byte streams. It sends messages, matches
    the replies to its own requests by their ids, answers requests from the other end with an empty
    result, as an editor answers a capability registration, and hands every other message to
    `on_message`. Its request ids begin with `id_prefix`.
    """

    def __init__(self, reader, writer, on_message, id_prefix):
        self.reader = reader
        self.writer = writer
        self.on_message = on_message
        self.id_prefix = id_prefix
        self.write_lock = threading.Lock()
        self.next_id = 0
        self.replies = {}
        self.replies_lock = threading.Lock()
        self.exited = False
        self.reading = threading.Thread(target=self._read, daemon=True)

    @property
    def running(self):
        return not self.exited

    def _exited_error(self):
        """The message of the error that requests receive once the other end has gone."""
        return "the Lean server exited"

    def _note(self, text):
        """Records a problem of the harness's own among the diagnostics of the connection."""

    def _ended(self):
        """Runs once the other end's messages have ended and every waiting request has failed."""

    def send(self, message):
        data = frame(message)
        with self.write_lock:
            try:
                self.writer.write(data)
                self.writer.flush()
            except (OSError, ValueError) as error:
                raise LspError(self._exited_error()) from error

    def request(self, method, params, timeout=120, control=False):
        """
        Sends a request and waits for its reply. A `control` request is one that the host of a
        remote server answers itself, which waits for its reply after the server has exited too.
        """
        with self.write_lock:
            request_id = f"{self.id_prefix}{self.next_id}"
            self.next_id += 1
        waiter = {"done": threading.Event(), "control": control}
        with self.replies_lock:
            if self.exited and not control:
                raise LspError(self._exited_error())
            self.replies[request_id] = waiter
        self.send(
            {"jsonrpc": "2.0", "id": request_id, "method": method, "params": params}
        )
        if not waiter["done"].wait(timeout):
            raise TimeoutError(f"no reply to {method} within {timeout}s")
        reply = waiter["reply"]
        if "error" in reply:
            raise LspError(reply["error"])
        return reply.get("result")

    def notify(self, method, params):
        self.send({"jsonrpc": "2.0", "method": method, "params": params})

    def end_runs(self):
        """
        Kills the drivers that the server's file workers have started, with the runners and the
        test executables below them.
        """
        drivers = matching("Errata.run run -E name") & set(descendants(self.pid))
        kill_trees(drivers)

    def runner_processes(self, decl):
        """
        The process ids of the processes below this server that run a test named `decl`: the driver
        that the widget started for it, and the interpreted test executable that runs it.
        """
        runs = matching(rf"run -E name\(={decl}\) ") | matching(
            rf"errata-interpret .* errata-run \S+ {decl}( |$)"
        )
        return sorted(runs & set(descendants(self.pid)))

    def _read(self):
        try:
            while (message := read_message(self.reader)) is not None:
                self._receive(message)
        except Exception as error:  # noqa: BLE001 - whatever ends the reading fails the waiters
            self._note(f"harness: reading the Lean server's messages failed: {error!r}\n")
        self._fail_waiters()
        self._ended()

    def _receive(self, message):
        request_id = message.get("id")
        if "method" in message and request_id is not None:
            # A request from the server to the editor, such as a capability registration.
            self.send({"jsonrpc": "2.0", "id": request_id, "result": None})
            return
        with self.replies_lock:
            waiter = (
                self.replies.pop(request_id, None)
                if isinstance(request_id, str)
                else None
            )
        if waiter is not None:
            waiter["reply"] = message
            waiter["done"].set()
        else:
            self.on_message(message)

    def _fail_waiters(self, keep_control=False):
        """
        Answers the harness's unanswered requests with an error once the server has gone, apart from
        control requests when `keep_control` is true.
        """
        # The stderr reader may still be reading the server's last words.
        time.sleep(0.2)
        with self.replies_lock:
            self.exited = True
            waiters = {
                request_id: waiter
                for request_id, waiter in self.replies.items()
                if not (keep_control and waiter["control"])
            }
            for request_id in waiters:
                del self.replies[request_id]
        error = {"code": -32603, "message": self._exited_error()}
        for waiter in waiters.values():
            waiter["reply"] = {"error": error}
            waiter["done"].set()


class LeanServer(LspPeer):
    """
    A Lean language server started in the fixture workspace, speaking LSP over its stdio.

    `lake env` starts the server as a child process, and the server starts a file worker per
    document, which starts the builds and runs of the widget. Stopping the server stops all of them.
    When the server's output ends, `on_exit` runs.
    """

    def __init__(self, on_message, on_exit=None):
        # The server's messages that are not replies to the harness go to `on_message`.
        self.proc = subprocess.Popen(
            ["lake", "env", "lean", "--server"],
            cwd=FIXTURE,
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
        )
        super().__init__(self.proc.stdout, self.proc.stdin, on_message, "harness-")
        self.on_exit = on_exit
        self.stderr = []
        self.readers = [
            self.reading,
            threading.Thread(target=self._read_stderr, daemon=True),
        ]
        for reader in self.readers:
            reader.start()

    @property
    def running(self):
        return not self.exited and self.proc.poll() is None

    def stderr_tail(self, lines=100):
        return "".join(self.stderr[-lines:])

    def _exited_error(self):
        return f"the Lean server exited; its stderr ends:\n{self.stderr_tail()}"

    def _note(self, text):
        self.stderr.append(text)

    def _ended(self):
        if self.on_exit is not None:
            self.on_exit()

    def initialize(self):
        result = self.request(
            "initialize",
            {"processId": None, "rootUri": FIXTURE.as_uri(), "capabilities": {}},
        )
        self.notify("initialized", {})
        return result

    def stop(self):
        """Kills the server and every process below it, and waits for the server to exit."""
        kill_trees([self.proc.pid])
        self.proc.wait()
        # The readers end at the end of their pipes, which the server's exit closed, and the pipes
        # are closed after them, so a session that starts several servers holds the pipes of one.
        for reader in self.readers:
            reader.join(timeout=5)
        for pipe in (self.proc.stdin, self.proc.stdout, self.proc.stderr):
            pipe.close()

    @property
    def pid(self):
        return self.proc.pid

    def _read_stderr(self):
        for line in self.proc.stderr:
            self.stderr.append(line.decode("utf-8", "replace"))


class LeanSession:
    """The Lean server that the tests of a session share, which a test may restart."""

    def __init__(self):
        # Where the server's messages go: the relay of the test that is running, if any.
        self.route = None
        self.lean = None
        self.initialize_result = None
        self.start()

    def start(self):
        self.lean = LeanServer(self._on_message)
        self.initialize_result = self.lean.initialize()

    def restart(self):
        self.lean.stop()
        self.start()

    def ensure_running(self):
        """Starts a new server when the last one has exited."""
        if not self.lean.running:
            self.restart()

    def stop(self):
        self.lean.stop()

    def _on_message(self, message):
        route = self.route
        if route is not None:
            route(message)


class RemoteLeanServer(LspPeer):
    """
    The Lean server of a `LeanHost`, which this process reaches over TCP at `address`, a host and a
    port joined by a colon. It serves as a `LeanServer` does, and `control` sends the host its own
    requests.
    """

    def __init__(self, address, on_message):
        host, port = address.rsplit(":", 1)
        self.sock = socket.create_connection((host, int(port)))
        super().__init__(
            self.sock.makefile("rb"), self.sock.makefile("wb"), on_message,
            f"harness-{os.getpid()}-",
        )
        self.pid = None
        self.exit_text = ""
        self.reading.start()

    def control(self, method, timeout=300):
        """
        Sends the host the request `$/harness/METHOD` and returns its reply. A reply that describes
        the server updates what this connection knows of it: its process id and whether it runs.
        """
        reply = self.request(f"$/harness/{method}", None, timeout, control=True)
        if isinstance(reply, dict) and "pid" in reply:
            self.pid = reply["pid"]
            with self.replies_lock:
                self.exited = not reply["running"]
        return reply

    def stderr_tail(self, lines=100):
        try:
            return self.control("stderr", timeout=10)["text"]
        except (LspError, TimeoutError):
            return self.exit_text

    def _exited_error(self):
        return f"the Lean server exited; its stderr ends:\n{self.exit_text}"

    def _receive(self, message):
        if message.get("method") == "$/harness/exited":
            self.exit_text = message.get("params", {}).get("stderr", "")
            self._fail_waiters(keep_control=True)
            return
        super()._receive(message)

    def close(self):
        """Ends the connection, which the host then offers to the next test."""
        try:
            self.sock.shutdown(socket.SHUT_RDWR)
        except OSError:
            pass
        self.sock.close()
        self.reading.join(timeout=5)


class RemoteLeanSession:
    """
    The session of a test whose Lean server a `LeanHost` hosts at `address`. Restarting it restarts
    the host's server, and stopping it ends the test's connection.
    """

    def __init__(self, address):
        self.route = None
        self.lean = RemoteLeanServer(address, self._on_message)
        self.initialize_result = self.lean.control("hello")["initialize"]

    def restart(self):
        self.initialize_result = self.lean.control("restart")["initialize"]

    def ensure_running(self):
        """Starts a new server when the last one has exited."""
        if not self.lean.running:
            self.restart()

    def stop(self):
        self.lean.close()

    def _on_message(self, message):
        route = self.route
        if route is not None:
            route(message)


class LeanHost:
    """
    The host of a Lean server that the tests of a run share. It starts the server and initializes
    it, then serves one test at a time over a TCP connection: it passes the test's messages to the
    server and the server's messages to the test, and answers the harness's own requests, whose
    methods begin with `$/harness/`. `hello` and `restart` reply with the server's process id,
    whether it runs, and its reply to `initialize`, after starting a new server for `restart`;
    `stderr` replies with the end of the server's stderr; `reset` readies the server for the next
    test, ending the runs its file workers started and closing the documents that earlier tests left
    open, or starting a new server when the last one has exited. When the server exits, the test
    receives the notification `$/harness/exited` with the end of the server's stderr.
    """

    def __init__(self):
        self.client = None
        self.client_lock = threading.Lock()
        # The documents that tests opened and have not closed, by URI.
        self.documents = set()
        self.restarting = False
        self.lean = None
        self.initialize_result = None
        self.start_server()

    def start_server(self):
        self.lean = LeanServer(self._to_client, on_exit=self._server_exited)
        self.initialize_result = self.lean.initialize()

    def restart(self):
        self.restarting = True
        try:
            self.lean.stop()
        finally:
            self.restarting = False
        self.documents.clear()
        self.start_server()

    def stop(self):
        self.restarting = True
        self.lean.stop()

    def info(self):
        return {
            "pid": self.lean.pid,
            "running": self.lean.running,
            "initialize": self.initialize_result,
        }

    def control(self, method):
        """The reply to the harness's request `$/harness/METHOD`."""
        if method == "hello":
            return self.info()
        if method == "restart":
            self.restart()
            return self.info()
        if method == "stderr":
            return {"text": self.lean.stderr_tail()}
        if method == "reset":
            if not self.lean.running:
                self.restart()
            else:
                self.lean.end_runs()
                for uri in self.documents:
                    self.lean.notify("textDocument/didClose", {"textDocument": {"uri": uri}})
                self.documents.clear()
            return self.info()
        raise LspError(f"the host has no request {method}")

    def serve(self, conn):
        """Serves the test at the other end of the connection until it closes the connection."""
        reader = conn.makefile("rb")
        with self.client_lock:
            self.client = conn
        try:
            while (message := read_message(reader)) is not None:
                self._from_client(message)
        except (OSError, ValueError, LspError):
            pass
        finally:
            with self.client_lock:
                self.client = None
            reader.close()
            conn.close()

    def _to_client(self, message):
        with self.client_lock:
            if self.client is not None:
                try:
                    self.client.sendall(frame(message))
                except OSError:
                    pass

    def _server_exited(self):
        if not self.restarting:
            self._to_client(
                {
                    "jsonrpc": "2.0",
                    "method": "$/harness/exited",
                    "params": {"stderr": self.lean.stderr_tail()},
                }
            )

    def _from_client(self, message):
        method = message.get("method") or ""
        request_id = message.get("id")
        if method.startswith("$/harness/"):
            try:
                reply = {"result": self.control(method.removeprefix("$/harness/"))}
            except Exception as error:  # noqa: BLE001 - every failure is the request's error reply
                reply = {"error": {"code": -32603, "message": str(error)}}
            self._to_client({"jsonrpc": "2.0", "id": request_id, **reply})
            return
        params = message.get("params")
        document = params.get("textDocument") if isinstance(params, dict) else None
        uri = document.get("uri") if isinstance(document, dict) else None
        if method == "textDocument/didOpen" and uri:
            self.documents.add(uri)
        elif method == "textDocument/didClose" and uri:
            self.documents.discard(uri)
        try:
            self.lean.send(message)
        except LspError as error:
            if request_id is not None:
                self._to_client(
                    {
                        "jsonrpc": "2.0",
                        "id": request_id,
                        "error": {"code": -32603, "message": str(error)},
                    }
                )


def serve(ready):
    """
    Runs a `LeanHost` on a free port of the local interface, writes `{"port": N}` to the file
    `ready` once the server has been initialized, and serves tests until a terminate signal, which
    stops the server and every process below it.
    """
    host = LeanHost()
    listener = socket.create_server(("127.0.0.1", 0))

    def terminate(signum, frame):
        host.stop()
        os._exit(0)

    signal.signal(signal.SIGTERM, terminate)
    ready = Path(ready)
    written = ready.with_name(ready.name + ".partial")
    written.write_text(json.dumps({"port": listener.getsockname()[1]}))
    written.rename(ready)
    while True:
        conn, _ = listener.accept()
        host.serve(conn)


def decl_name(params):
    """The last component of the declaration that an RPC call of the widget names, if any."""
    decl = params.get("decl") if isinstance(params, dict) else None
    if isinstance(decl, dict) and "str" in decl:
        return decl["str"][1]
    return None


class Rule:
    """A change to how the relay passes on calls of one RPC method, for a number of calls."""

    def __init__(self, lock, method, action, count, after=0):
        # The relay's lock, which guards whether the rule is released and what it holds.
        self.lock = lock
        self.method = method
        self.action = action
        self.remaining = count
        # How many calls the rule lets pass before it applies.
        self.skip = after
        self.held = []
        self.matched = threading.Event()
        self.released = False

    def release(self):
        """Passes on the messages held so far, and every later one."""
        with self.lock:
            self.released = True
            held, self.held = self.held, []
        for deliver in held:
            deliver()

    def stop(self):
        """Lets later calls pass as usual, and passes on the messages held so far."""
        with self.lock:
            self.remaining = 0
        self.release()

    def wait_until_matched(self, timeout=60):
        if not self.matched.wait(timeout):
            raise TimeoutError(f"no call of {self.method} within {timeout}s")


class LspRelay:
    """Serves the test page and relays LSP messages between it and the Lean server."""

    def __init__(self):
        self.lean = None
        self.inbox = []
        self.inbox_ready = threading.Condition()
        # The prefix of the request ids of the latest page to collect its messages.
        self.page = None
        # For each request from the page that awaits its reply, by request id: the RPC method, the
        # name of the declaration it is about, and the request's place in the order of requests.
        self.page_requests = {}
        self.requests_sent = 0
        self.rules = []
        # The replies that have reached the page, as (method, declaration name, place) triples.
        self.delivered = []
        self.delivered_changed = threading.Condition()
        # Set while a server that has finished starting receives the page's messages.
        self.connected = threading.Event()
        self.lock = threading.Lock()
        relay = self

        class Handler(BaseHTTPRequestHandler):
            def log_message(self, *args):
                pass

            def do_GET(self):
                if self.path.startswith("/lsp?page="):
                    relay._serve_inbox(self, self.path.removeprefix("/lsp?page="))
                elif self.path == "/":
                    relay._serve_file(self, PAGE / "index.html")
                elif self.path == "/editor.js":
                    relay._serve_file(self, PAGE / "editor.js")
                elif self.path.startswith("/infoview/"):
                    relay._serve_file(
                        self, INFOVIEW / self.path.removeprefix("/infoview/")
                    )
                else:
                    self.send_error(404)

            def do_POST(self):
                length = int(self.headers.get("Content-Length", "0"))
                message = json.loads(self.rfile.read(length))
                self.send_response(204)
                self.end_headers()
                relay._from_page(message)

        self.server = ThreadingHTTPServer(("127.0.0.1", 0), Handler)
        self.server.daemon_threads = True
        threading.Thread(target=self.server.serve_forever, daemon=True).start()

    @property
    def url(self):
        host, port = self.server.server_address
        return f"http://{host}:{port}/"

    def close(self):
        self.connected.clear()
        self.server.shutdown()
        self.server.server_close()

    def hold_requests(self, method, count=1):
        """Keeps the next calls of `method` from reaching the server until the rule is released."""
        return self._add_rule(method, "hold-request", count)

    def hold_replies(self, method, count=1, after=0):
        """
        Keeps the server's replies to the next calls of `method` from the page until released,
        after letting the replies to `after` calls pass.
        """
        return self._add_rule(method, "hold-reply", count, after)

    def reject_requests(self, method, count=1):
        """Answers the next calls of `method` with an error, without passing them to the server."""
        return self._add_rule(method, "reject", count)

    def reject_replies(self, method, count=1):
        """Passes the next calls of `method` to the server, and answers the page with an error."""
        return self._add_rule(method, "reject-reply", count)

    def mark(self):
        """A place in the order of the page's requests, for `wait_for_reply`."""
        with self.lock:
            return self.requests_sent

    def wait_for_reply(self, method, decl=None, after=0, timeout=60):
        """
        Waits until the page has a reply to a call of `method` that was sent after the place `after`
        from `mark`. With `decl`, the call must be about the declaration of that name.
        """

        def arrived():
            return any(
                m == method and (decl is None or d == decl) and place > after
                for m, d, place in self.delivered
            )

        with self.delivered_changed:
            if not self.delivered_changed.wait_for(arrived, timeout):
                about = f" about {decl}" if decl else ""
                raise TimeoutError(f"no reply to {method}{about} within {timeout}s")

    def _add_rule(self, method, action, count, after=0):
        rule = Rule(self.lock, method, action, count, after)
        with self.lock:
            self.rules.append(rule)
        return rule

    def _apply_rule(self, method, action, deliver=None):
        """
        Finds a rule with the action for a call of `method` and counts the call against it. When
        `deliver` is given and the rule is unreleased, the rule holds `deliver` for later. The rule is
        released only under the same lock, so a held message is always passed on by the release.
        Returns the rule, if any, and whether it holds the message.
        """
        with self.lock:
            for rule in self.rules:
                if (
                    rule.method == method
                    and rule.action == action
                    and rule.remaining > 0
                ):
                    if rule.skip > 0:
                        rule.skip -= 1
                        continue
                    rule.remaining -= 1
                    held = deliver is not None and not rule.released
                    if held:
                        rule.held.append(deliver)
                    rule.matched.set()
                    return rule, held
        return None, False

    def _deliver(self, message):
        with self.inbox_ready:
            self.inbox.append(message)
            self.inbox_ready.notify_all()

    def _from_page(self, message):
        request_id = message.get("id")
        if request_id is not None:
            method = message.get("method")
            params = message.get("params")
            if method == "$/lean/rpc/call":
                method = params["method"]
                params = params.get("params")
            with self.lock:
                self.requests_sent += 1
                self.page_requests[request_id] = (
                    method,
                    decl_name(params),
                    self.requests_sent,
                )
            rejected, _ = self._apply_rule(method, "reject")
            if rejected:
                with self.lock:
                    self.page_requests.pop(request_id, None)
                self._deliver(
                    {
                        "jsonrpc": "2.0",
                        "id": request_id,
                        "error": {
                            "code": -32603,
                            "message": "rejected by the test harness",
                        },
                    }
                )
                return
            _, held = self._apply_rule(
                method, "hold-request", lambda: self._to_server(message)
            )
            if held:
                return
        self._to_server(message)

    def connect(self, lean):
        """Passes the page's messages to `lean`, a server that has finished starting."""
        self.lean = lean
        self.connected.set()

    def disconnect(self):
        """
        Holds the page's messages until a new server is connected, and fails the requests that the
        stopped server has yet to answer, as an editor does when its language server stops.
        """
        self.connected.clear()
        with self.lock:
            unanswered, self.page_requests = self.page_requests, {}
        for request_id in unanswered:
            self._deliver(
                {
                    "jsonrpc": "2.0",
                    "id": request_id,
                    "error": {"code": -32603, "message": "the Lean server stopped"},
                }
            )

    def _to_server(self, message):
        # A server only reads requests once it has been initialized, so messages wait until then.
        if not self.connected.wait(timeout=120):
            raise TimeoutError("no Lean server was connected within 120s")
        self.lean.send(message)

    def from_server(self, message):
        request_id = message.get("id")
        if request_id is None:
            self._deliver(message)
            return
        with self.lock:
            request = self.page_requests.pop(request_id, None)
        # A reply to a request that this page is no longer waiting on, such as one that was failed
        # when the server stopped, goes nowhere.
        if request is None:
            return
        method = request[0]
        rejected, _ = self._apply_rule(method, "reject-reply")
        if rejected:
            message = {
                "jsonrpc": "2.0",
                "id": request_id,
                "error": {"code": -32603, "message": "rejected by the test harness"},
            }
        _, held = self._apply_rule(
            method, "hold-reply", lambda: self._deliver_reply(request, message)
        )
        if not held:
            self._deliver_reply(request, message)

    def _deliver_reply(self, request, message):
        self._deliver(message)
        with self.delivered_changed:
            self.delivered.append(request)
            self.delivered_changed.notify_all()

    def _serve_inbox(self, handler, page):
        """
        Answers a page's collection of messages. The latest page to ask is the one that the messages
        are for, so a collection that an earlier page left waiting ends empty-handed.
        """
        with self.inbox_ready:
            if page != self.page:
                self.page = page
                self.inbox_ready.notify_all()
            self.inbox_ready.wait_for(
                lambda: self.inbox or self.page != page, timeout=20
            )
            if self.page == page:
                messages, self.inbox = self.inbox, []
            else:
                messages = []
        body = json.dumps(messages).encode("utf-8")
        handler.send_response(200)
        handler.send_header("Content-Type", "application/json")
        handler.send_header("Content-Length", str(len(body)))
        handler.end_headers()
        handler.wfile.write(body)

    def _serve_file(self, handler, path):
        if not path.is_file():
            handler.send_error(404)
            return
        body = path.read_bytes()
        kind = mimetypes.guess_type(path.name)[0] or "application/octet-stream"
        if path.suffix == ".js":
            kind = "text/javascript"
        handler.send_response(200)
        handler.send_header("Content-Type", kind)
        handler.send_header("Content-Length", str(len(body)))
        handler.end_headers()
        handler.wfile.write(body)


class Editor:
    """
    The editor that the tests drive: it opens fixture files in the Lean server, moves the cursor,
    edits and saves, and restarts the server, telling the InfoView of each as VS Code would.
    """

    def __init__(self, page, relay, session):
        self.page = page
        self.relay = relay
        self.session = session
        self.documents = {}
        # The harness's own RPC session for each open document, by document URI.
        self.rpc_sessions = {}

    @property
    def lean(self):
        return self.session.lean

    @property
    def initialize_result(self):
        return self.session.initialize_result

    def start(self):
        """Connects the page to the session's server and loads the InfoView."""
        self.session.ensure_running()
        self.relay.connect(self.lean)
        self.session.route = self.relay.from_server
        self.page.goto(self.relay.url)
        self.page.wait_for_function("window.harness !== undefined")

    def close(self):
        """
        Ends the test's builds and runs and closes its documents, so the next test starts with the
        server as it was. A server that fails to do so is restarted, or started by the next test.
        """
        self.session.route = None
        try:
            self.lean.end_runs()
            for module in self.documents:
                self.lean.notify(
                    "textDocument/didClose",
                    {"textDocument": {"uri": self.path(module).as_uri()}},
                )
        except Exception:  # noqa: BLE001 - after any failure, the server's state is unknown
            try:
                self.session.restart()
            except Exception:  # noqa: BLE001 - the next test starts a server of its own
                pass
        finally:
            self.documents = {}
            self.rpc_sessions = {}
            scratch = self.path("Scratch")
            if scratch.exists():
                scratch.unlink()

    def write_scratch(self, body):
        """
        Writes the module `WidgetFixtures.Scratch`, a test module for a test to change as it goes. The
        module's text differs from one test to the next, so Lake builds it afresh for each.
        """
        header = (
            "/-\nCopyright (c) 2026 Lean FRO LLC. All rights reserved.\n"
            "Released under Apache 2.0 license as described in the file LICENSE.\n"
            "Author: David Thrane Christiansen\n-/\n"
            "module\n\npublic import Errata\n\nopen Errata\n\npublic section\n\n"
        )
        nonce = f"\n-- written by the test harness at {time.time_ns()}\n"
        self.path("Scratch").write_text(header + body + nonce, encoding="utf-8")

    def call_rpc(self, module, decl, method, params, timeout=120):
        """
        Calls an RPC method of the server at `decl` in `module`. The harness keeps one RPC session per
        document, and connects a new one when the server has let the last one lapse.
        """
        location = self.location_of(module, decl)
        uri = location["uri"]
        for attempt in (0, 1):
            if uri not in self.rpc_sessions:
                reply = self.lean.request("$/lean/rpc/connect", {"uri": uri}, timeout)
                self.rpc_sessions[uri] = reply["sessionId"]
            try:
                return self.lean.request(
                    "$/lean/rpc/call",
                    {
                        "sessionId": self.rpc_sessions[uri],
                        "textDocument": {"uri": uri},
                        "position": location["range"]["start"],
                        "method": method,
                        "params": params,
                    },
                    timeout,
                )
            except LspError:
                del self.rpc_sessions[uri]
                if attempt == 1:
                    raise
        raise AssertionError("unreachable")

    def widget_props(self, module, decl, timeout=120):
        """The props of the Errata widget that the server shows at `decl` in `module`."""
        location = self.location_of(module, decl)
        [widget] = self.call_rpc(
            module, decl, "Lean.Widget.getWidgets", location["range"]["start"], timeout
        )["widgets"]
        return widget["props"]

    def server_run(self, module, decl):
        """
        What the server reports of its run of `decl` in `module`, from the start. A report with no
        start time means the server holds no run of the test.
        """
        props = self.widget_props(module, decl)
        return self.call_rpc(
            module,
            decl,
            "Errata.Widget.awaitOutput",
            {
                "decl": props["decl"],
                "since": 0,
                "sinceResults": 0,
                "version": props["version"],
                "phase": "",
            },
        )

    def runner_processes(self, decl):
        """The process ids of the test runners that the server has started for a test named `decl`."""
        return self.lean.runner_processes(decl)

    def path(self, module):
        """The file of a fixture module, given by its name below `WidgetFixtures`."""
        return FIXTURE / "WidgetFixtures" / (module.replace(".", "/") + ".lean")

    def open(self, module):
        path = self.path(module)
        text = path.read_text(encoding="utf-8")
        self.documents[module] = {"text": text, "version": 1}
        self.lean.notify(
            "textDocument/didOpen",
            {
                "textDocument": {
                    "uri": path.as_uri(),
                    "languageId": "lean4",
                    "version": 1,
                    "text": text,
                }
            },
        )

    def location_of(self, module, decl):
        """The place in a fixture module just inside the name of the declaration `decl`."""
        text = self.documents[module]["text"]
        for line, content in enumerate(text.split("\n")):
            if content.startswith(f"def {decl} "):
                position = {"line": line, "character": 5}
                return {
                    "uri": self.path(module).as_uri(),
                    "range": {"start": position, "end": position},
                }
        raise ValueError(f"no `def {decl}` in {module}")

    def reload_page(self):
        """Loads the page again, which starts the InfoView afresh, with none of its earlier state."""
        self.page.reload()
        self.page.wait_for_function("window.harness !== undefined")

    def show_at_text(self, module, text):
        """Opens the module if need be and starts the InfoView with the cursor on the line with `text`."""
        if module not in self.documents:
            self.open(module)
        lines = self.documents[module]["text"].split("\n")
        line = next(i for i, content in enumerate(lines) if text in content)
        position = {"line": line, "character": lines[line].index(text)}
        location = {
            "uri": self.path(module).as_uri(),
            "range": {"start": position, "end": position},
        }
        self.page.evaluate(
            "([location, result]) => window.harness.start(location, result)",
            [location, self.initialize_result],
        )

    def show(self, module, decl):
        """Opens the module if need be and starts the InfoView with the cursor on `decl`."""
        if module not in self.documents:
            self.open(module)
        self.page.evaluate(
            "([location, result]) => window.harness.start(location, result)",
            [self.location_of(module, decl), self.initialize_result],
        )

    def move_to(self, module, decl):
        if module not in self.documents:
            self.open(module)
        self.page.evaluate(
            "(location) => window.harness.moveCursor(location)",
            self.location_of(module, decl),
        )

    def edit(self, module, text):
        """Replaces the text of an open module in the editor, leaving the file on disk as it was."""
        document = self.documents[module]
        document["version"] += 1
        document["text"] = text
        params = {
            "textDocument": {
                "uri": self.path(module).as_uri(),
                "version": document["version"],
            },
            "contentChanges": [{"text": text}],
        }
        self.lean.notify("textDocument/didChange", params)
        self.page.evaluate(
            "(params) => window.harness.sentClientNotification('textDocument/didChange', params)",
            params,
        )

    def save(self, module):
        """Writes the editor's text of a module to its file."""
        path = self.path(module)
        path.write_text(self.documents[module]["text"], encoding="utf-8")
        self.lean.notify(
            "textDocument/didSave", {"textDocument": {"uri": path.as_uri()}}
        )

    def restart_server(self):
        """Stops the Lean server and starts a new one with the same documents open."""
        self.relay.disconnect()
        self.session.restart()
        self.rpc_sessions = {}
        documents = self.documents
        self.documents = {}
        for module, document in documents.items():
            self.open(module)
            if document["text"] != self.documents[module]["text"]:
                self.edit(module, document["text"])
        self.relay.connect(self.lean)
        self.page.evaluate(
            "(result) => window.harness.serverRestarted(result)", self.initialize_result
        )

    def editor_calls(self):
        return self.page.evaluate("window.harness.editorCalls")

    def copied(self):
        return self.page.evaluate("window.harness.copied")


if __name__ == "__main__":
    if len(sys.argv) != 3 or sys.argv[1] != "serve":
        print("usage: python harness.py serve READY-FILE", file=sys.stderr)
        sys.exit(2)
    serve(sys.argv[2])
