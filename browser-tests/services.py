"""
Processes that Errata fixtures start once per run and share between the tests of a suite: a browser,
an HTTP server, a Lean server. Each fixture phase runs in a process of its own, so a fixture's setup
starts its service in a session of its own, which outlives the setup's process and the runner's
cleanup of that process's group, and its teardown stops the service.

A service's state directory holds its process id and its log. The directory is named after the run,
from `ERRATA_RUN_ID`, and after the suite and the fixture, so a teardown finds what the setup
started even when the setup failed or was stopped before it produced a value. Without
`ERRATA_RUN_ID`, as in a chain of invocations run by hand, the directory is named after the process
that runs the chain.
"""

import hashlib
import json
import os
import shutil
import signal
import socket
import subprocess
import tempfile
import time
from pathlib import Path


def state_dir(context, name):
    """
    The state directory of the service that the fixture `name` of the suite starts, given the
    fixture phase's context.
    """
    run = os.environ.get("ERRATA_RUN_ID") or f"pid{os.getpid()}"
    args = json.dumps([str(a) for a in context.config.invocation_params.args])
    suite = hashlib.sha1(args.encode("utf-8")).hexdigest()[:12]
    return Path(tempfile.gettempdir()) / "verso-browser-tests" / run / suite / name


def start(context, name, args, cwd=None):
    """
    Starts the command `args` as the service of the fixture `name`, in a session of its own, with
    its output in the log of its state directory, and returns its process. The directory records
    the process id before this returns.
    """
    state = state_dir(context, name)
    state.mkdir(parents=True, exist_ok=True)
    with open(state / "log", "wb") as log:
        proc = subprocess.Popen(
            args,
            cwd=cwd,
            stdin=subprocess.DEVNULL,
            stdout=log,
            stderr=subprocess.STDOUT,
            start_new_session=True,
        )
    (state / "pid").write_text(str(proc.pid))
    return proc


def log_of(context, name):
    """What the service of the fixture `name` has written so far."""
    try:
        return (state_dir(context, name) / "log").read_text(errors="replace")
    except OSError:
        return ""


def alive(pid):
    """
    Whether a process with the id exists. A service that a chain of invocations started in this
    process is this process's child, and is reaped here once it has exited.
    """
    try:
        os.waitpid(pid, os.WNOHANG)
    except ChildProcessError:
        pass
    try:
        os.kill(pid, 0)
    except ProcessLookupError:
        return False
    except PermissionError:
        return True
    return True


def signal_group(pid, sig):
    """Sends the signal to the process group whose leader is `pid`, if it has members."""
    try:
        os.killpg(pid, sig)
    except (ProcessLookupError, PermissionError):
        pass


def stop(context, name, group_first=True, grace=10.0):
    """
    Stops the service of the fixture `name` and removes its state directory. The service receives a
    terminate signal, to its whole group when `group_first` is true and to its leader alone
    otherwise, which then stops what it started itself; after the leader exits, or after `grace`
    seconds, whatever remains of the group is killed.
    """
    state = state_dir(context, name)
    try:
        pid = int((state / "pid").read_text())
    except (OSError, ValueError):
        pid = None
    if pid is not None:
        if group_first:
            signal_group(pid, signal.SIGTERM)
        else:
            try:
                os.kill(pid, signal.SIGTERM)
            except ProcessLookupError:
                pass
        deadline = time.monotonic() + grace
        while alive(pid) and time.monotonic() < deadline:
            time.sleep(0.05)
        signal_group(pid, signal.SIGKILL)
    shutil.rmtree(state, ignore_errors=True)
    # The directories of the suite and the run go with their last service.
    for parent in (state.parent, state.parent.parent):
        try:
            parent.rmdir()
        except OSError:
            break


def wait_until(ready, timeout, what, proc=None, context=None, name=None):
    """
    Waits until `ready()` returns a value other than `None`, and returns it. Fails with a message
    naming `what` after `timeout` seconds, or once the process `proc` has exited, with the service's
    log when the fixture's `context` and `name` are given.
    """
    deadline = time.monotonic() + timeout
    while True:
        value = ready()
        if value is not None:
            return value
        if proc is not None and proc.poll() is not None:
            problem = f"it exited with code {proc.returncode}"
        elif time.monotonic() > deadline:
            problem = f"it was not ready after {timeout} seconds"
        else:
            time.sleep(0.05)
            continue
        log = log_of(context, name) if context is not None else ""
        shown = f"; its log:\n{log}" if log else ""
        raise RuntimeError(f"{what} did not start: {problem}{shown}")


def free_port():
    """A port on the local interface that no process listens on at the moment."""
    with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as s:
        s.bind(("127.0.0.1", 0))
        return s.getsockname()[1]


def accepts(port):
    """Whether a server accepts connections on the local port."""
    try:
        with socket.create_connection(("127.0.0.1", port), timeout=0.5):
            return True
    except OSError:
        return False
