"""
Verso's pytest harness for Errata: a pytest suite becomes an Errata test executable through this
file, which needs only pytest. The test executable is

    python errata_pytest.py PYTEST-ARG... errata-list OUT
    python errata_pytest.py PYTEST-ARG... errata-run OUT NODE-ID [setting:NAME=VALUE]... [threads:N]

where the pytest arguments name the tests' paths and any options, as a pytest command line would.
`errata-list` collects the tests and writes the inventory to OUT: a test record per collected item,
named by its node id, with the node id's parts as its path, its markers as its tags, its docstring as
its description, and its file and line. `errata-run` runs the one item with that node id and writes
its verdict to OUT, with the location and the detail of a failure, and exits with 0 when it passed
and 1 otherwise. Several invocations may be chained, each separated by a `;` argument; they run in
order in one process, stopping at the first that exits non-zero.

A suite declares the settings its tests take in a module-level dictionary `errata_settings_decl` in a
`conftest.py`, which maps each setting's name to a dictionary with its `description` and optionally
its `default`. A test takes a setting through the marker `errata_setting(NAME)`, or
`errata_setting(NAME, optional=True)` for one it runs without, and reads the values it receives
through the `errata_settings` fixture, a dictionary from names to values.

pytest's own output, and what a test prints, goes to standard output and standard error, which the
runner captures as the test's output; the records go only to OUT.
"""

import inspect
import json
import os
import sys
import time

import pytest

# The markers that configure pytest itself, which the inventory leaves out of a test's tags.
BUILTIN_MARKERS = {
    "errata_setting",
    "filterwarnings",
    "parametrize",
    "skip",
    "skipif",
    "usefixtures",
    "xfail",
}

MODES = ("errata-list", "errata-run", "errata-fixture")

USAGE = """usage:
  python errata_pytest.py PYTEST-ARG... errata-list <out>
  python errata_pytest.py PYTEST-ARG... errata-run <out> <node-id> [setting:NAME=VALUE]... [threads:N]

Several invocations may be chained, each separated by a ';' argument. The Errata runner starts test executables; to run the tests, run the Errata driver, which is
usually `lake test`."""

ERRATA_SETTING_MARKER = (
    "errata_setting(name, optional=False): the test takes the Errata setting with this name, which a "
    "conftest.py declares in errata_settings_decl"
)


def write_record(out, record):
    """Appends one record to the output file as a line of JSON."""
    out.write(json.dumps(record, ensure_ascii=False) + "\n")
    out.flush()


def relative_path(path):
    """A path relative to the working directory, where the runner starts the test executable."""
    try:
        return os.path.relpath(str(path), os.getcwd())
    except ValueError:
        return str(path)


def node_path(nodeid):
    """
    The parts of a node id: the file's path components, the class if any, and the function with its
    parameter id, which may itself hold `::` and `/`.
    """
    head, bracket, params = nodeid.partition("[")
    file_part, *rest = head.split("::")
    parts = [p for p in file_part.split("/") if p] + rest
    if bracket and parts:
        parts[-1] += bracket + params
    return parts


def item_settings(item):
    """
    The settings that an item takes, as (name, optional) pairs, in the order its markers name them.
    """
    seen = {}
    for marker in item.iter_markers("errata_setting"):
        optional = bool(marker.kwargs.get("optional", False))
        for name in marker.args:
            if name not in seen:
                seen[name] = optional
    return list(seen.items())


def declared_settings(config):
    """
    The settings that the loaded `conftest.py` files declare, as a dictionary from names to their
    declarations, in the order the files were loaded. The result is the dictionary and a list of
    problems with the declarations.
    """
    declared = {}
    problems = []
    for _, plugin in config.pluginmanager.list_name_plugin():
        decl = getattr(plugin, "errata_settings_decl", None)
        if decl is None:
            continue
        where = getattr(plugin, "__file__", repr(plugin))
        if not isinstance(decl, dict):
            problems.append(f"{where}: errata_settings_decl must be a dictionary")
            continue
        for name, info in decl.items():
            if not isinstance(info, dict) or not isinstance(info.get("description", ""), str):
                problems.append(
                    f"{where}: the setting {name} must map to a dictionary with a description"
                )
            elif "default" in info and not isinstance(info["default"], str):
                problems.append(f"{where}: the default of the setting {name} must be a string")
            elif name in declared:
                problems.append(f"{where}: the setting {name} is declared more than once")
            else:
                declared[name] = info
    return declared, problems


class ListPlugin:
    """Collects the inventory once pytest has collected the tests."""

    def __init__(self):
        """Starts with no records and no problems."""
        self.records = []
        self.problems = []

    def pytest_configure(self, config):
        """Registers the marker through which a test takes a setting."""
        config.addinivalue_line("markers", ERRATA_SETTING_MARKER)

    def pytest_collection_finish(self, session):
        """
        Makes the inventory's records: the settings that the collected tests take, in the order the
        conftest.py files declare them, then a test record per collected item.
        """
        declared, problems = declared_settings(session.config)
        self.problems.extend(problems)
        used = set()
        tests = []
        for item in session.items:
            record = {"type": "test", "name": item.nodeid, "path": node_path(item.nodeid)}
            path = getattr(item, "path", None)
            if path is not None:
                record["file"] = relative_path(path)
            line = item.location[1] if item.location else None
            if line is not None:
                record["line"] = line + 1
            obj = getattr(item, "obj", None)
            doc = inspect.getdoc(obj) if obj is not None else None
            if doc:
                record["description"] = doc
            tags = []
            for marker in item.iter_markers():
                if marker.name not in BUILTIN_MARKERS and marker.name not in tags:
                    tags.append(marker.name)
            if tags:
                record["tags"] = tags
            settings = item_settings(item)
            for name, _ in settings:
                if name not in declared:
                    self.problems.append(
                        f"{item.nodeid} takes the setting {name}, which no conftest.py declares "
                        "in errata_settings_decl"
                    )
                used.add(name)
            if settings:
                record["settings"] = [{"name": n, "optional": o} for n, o in settings]
            tests.append(record)
        for name, info in declared.items():
            if name in used:
                record = {"type": "setting", "name": name, "description": info.get("description", "")}
                if "default" in info:
                    record["default"] = info["default"]
                self.records.append(record)
        self.records.extend(tests)


class RunPlugin:
    """Runs one item, collects its reports, and gives the tests their settings."""

    def __init__(self, nodeid, settings, out):
        """Runs the item with the node id, giving it the settings and writing records to `out`."""
        self.nodeid = nodeid
        self.settings = settings
        self.out = out
        self.found = False
        self.collect_errors = []
        self.reports = {}

    def pytest_configure(self, config):
        """Registers the marker through which a test takes a setting."""
        config.addinivalue_line("markers", ERRATA_SETTING_MARKER)

    @pytest.fixture(scope="session")
    def errata_settings(self):
        """The values of the Errata settings that the test received, by name."""
        return dict(self.settings)

    @pytest.hookimpl(trylast=True)
    def pytest_collection_modifyitems(self, config, items):
        """Keeps the one item with the node id, after every other plugin has selected its items."""
        selected = [i for i in items if i.nodeid == self.nodeid]
        others = [i for i in items if i.nodeid != self.nodeid]
        self.found = bool(selected)
        if others:
            config.hook.pytest_deselected(items=others)
        items[:] = selected

    def pytest_collectreport(self, report):
        """Keeps the reports of the collectors that failed."""
        if report.failed:
            self.collect_errors.append(report)

    def pytest_runtest_logstart(self, nodeid, location):
        """Writes the `start` record as the item's setup begins."""
        write_record(self.out, {"type": "start", "time_ms": int(time.time() * 1000)})

    def pytest_runtest_logreport(self, report):
        """Keeps the report of each phase of the item: setup, call, and teardown."""
        self.reports[report.when] = report

    def verdict(self, code):
        """
        The test's verdict record, from the reports of its setup, call, and teardown, and from
        pytest's exit code when the test did not run.
        """
        if not self.found:
            if self.collect_errors:
                return failure_verdict(
                    "error", self.collect_errors[0], "collecting the tests failed"
                )
            if code not in (pytest.ExitCode.OK, pytest.ExitCode.NO_TESTS_COLLECTED):
                return {
                    "type": "verdict",
                    "status": "error",
                    "message": f"pytest ended with exit code {int(code)} ({exit_code_name(code)}) "
                    "before it ran the test; its output says why",
                }
            return {"type": "verdict", "status": "error", "message": f"no test is named {self.nodeid}"}
        setup = self.reports.get("setup")
        call = self.reports.get("call")
        teardown = self.reports.get("teardown")
        duration = sum(r.duration for r in self.reports.values())
        if setup is not None and setup.failed:
            verdict = failure_verdict("error", setup, "the test's setup failed")
        elif setup is not None and setup.skipped:
            verdict = skipped_verdict(setup)
        elif call is None:
            verdict = {"type": "verdict", "status": "error", "message": "the test did not run"}
        elif call.failed:
            verdict = failure_verdict("fail", call, "the test failed")
        elif call.skipped:
            verdict = skipped_verdict(call)
        else:
            verdict = {"type": "verdict", "status": "pass"}
        if verdict["status"] == "pass" and teardown is not None and teardown.failed:
            verdict = failure_verdict("error", teardown, "the test's teardown failed")
        verdict["duration_ms"] = int(duration * 1000)
        return verdict


def exit_code_name(code):
    """The name of one of pytest's exit codes, such as `USAGE_ERROR`."""
    try:
        return pytest.ExitCode(int(code)).name
    except ValueError:
        return "an unknown code"


def failure_verdict(status, report, fallback):
    """A verdict with the message, location, and detail of a failed report."""
    verdict = {"type": "verdict", "status": status, "message": fallback}
    crash = getattr(report.longrepr, "reprcrash", None)
    if crash is not None:
        message = (crash.message or "").strip().splitlines()
        if message:
            verdict["message"] = message[0]
        verdict["location"] = {"file": relative_path(crash.path), "line": crash.lineno}
    detail = report.longreprtext
    if detail:
        verdict["detail"] = detail
    return verdict


def skipped_verdict(report):
    """
    The verdict of a skipped report. An expected failure passes, and any other skip is an error: a
    test whose precondition fails has shown nothing.
    """
    reason = ""
    if isinstance(report.longrepr, tuple) and len(report.longrepr) == 3:
        reason = str(report.longrepr[2])
    if hasattr(report, "wasxfail"):
        return {"type": "verdict", "status": "pass", "message": f"an expected failure: {report.wasxfail}"}
    return {"type": "verdict", "status": "error", "message": f"the test was skipped: {reason}"}


def list_tests(pytest_args, out_path):
    """Writes the inventory of the tests that pytest collects, and returns the exit code."""
    plugin = ListPlugin()
    code = pytest.main(
        [*pytest_args, "--collect-only", "-q", "-p", "no:cacheprovider"], plugins=[plugin]
    )
    if code not in (pytest.ExitCode.OK, pytest.ExitCode.NO_TESTS_COLLECTED):
        print(f"errata_pytest.py: collecting the tests failed with exit code {int(code)}", file=sys.stderr)
        return 1
    if plugin.problems:
        for problem in plugin.problems:
            print(f"errata_pytest.py: {problem}", file=sys.stderr)
        return 1
    with open(out_path, "a", encoding="utf-8") as out:
        write_record(out, {"type": "protocol", "version": 1})
        for record in plugin.records:
            write_record(out, record)
    return 0


def run_test(pytest_args, out_path, nodeid, rest):
    """Runs the item with the node id, writes its records, and returns the exit code."""
    settings = {}
    for arg in rest:
        if arg.startswith("setting:"):
            name, _, value = arg[len("setting:"):].partition("=")
            settings[name] = value
    with open(out_path, "a", encoding="utf-8") as out:
        write_record(out, {"type": "protocol", "version": 1})
        plugin = RunPlugin(nodeid, settings, out)
        # Without capturing, what the test prints reaches the runner as it is printed.
        code = pytest.main(
            ["--capture=no", *pytest_args, "-p", "no:cacheprovider"], plugins=[plugin]
        )
        verdict = plugin.verdict(code)
        write_record(out, verdict)
    return 0 if verdict["status"] == "pass" else 1


def split_chain(argv):
    """The invocations of a chain: the arguments, split at each `;` argument."""
    links = [[]]
    for arg in argv:
        if arg == ";":
            links.append([])
        else:
            links[-1].append(arg)
    return links


def main(argv):
    """
    Carries out the invocation that the arguments give, or each invocation of a chain whose
    invocations are separated by `;` arguments, in order, stopping at the first that exits
    non-zero, and returns the exit code of the last that ran. The pytest arguments precede the
    first invocation and serve them all.
    """
    links = split_chain(argv)
    first = links[0]
    mode_at = next((i for i, a in enumerate(first) if a in MODES), None)
    if mode_at is None:
        print(USAGE, file=sys.stderr)
        return 2
    pytest_args = first[:mode_at]
    links[0] = first[mode_at:]
    code = 2
    for link in links:
        # Each invocation imports the suite afresh, as a process of its own would.
        modules = set(sys.modules)
        try:
            code = invoke(pytest_args, link)
        finally:
            for name in set(sys.modules) - modules:
                del sys.modules[name]
        if code != 0:
            break
    return code


def invoke(pytest_args, link):
    """Carries out one invocation, and returns its exit code."""
    mode, rest = (link[0], link[1:]) if link else ("", [])
    if mode == "errata-list" and len(rest) == 1:
        return list_tests(pytest_args, rest[0])
    if mode == "errata-run" and len(rest) >= 2:
        return run_test(pytest_args, rest[0], rest[1], rest[2:])
    if mode == "errata-fixture":
        print(
            "errata_pytest.py: the pytest harness runs the modes errata-list and errata-run",
            file=sys.stderr,
        )
        return 2
    print(USAGE, file=sys.stderr)
    return 2


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
