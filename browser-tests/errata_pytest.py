"""
Verso's pytest harness for Errata: a pytest suite becomes an Errata test executable through this
file, which needs only pytest. The test executable is

    python errata_pytest.py PYTEST-ARG... errata-list OUT
    python errata_pytest.py PYTEST-ARG... errata-run OUT NODE-ID [setting:NAME=VALUE]...
        [fixture:NAME=VALUE]... [threads:N]
    python errata_pytest.py PYTEST-ARG... errata-fixture OUT NAME setup|prepare|teardown
        [setting:NAME=VALUE]... [fixture:NAME=VALUE]... [threads:N]

where the pytest arguments name the tests' paths and any options, as a pytest command line would.
`errata-list` collects the tests and writes the inventory to OUT: the settings and the Errata
fixtures that the tests use, then a test record per collected item, named by its node id, with the
node id's parts as its path, its markers as its tags, its docstring as its description, and its
file and line. `errata-run` runs the one item with that node id and writes its verdict to OUT, with
the location and the detail of a failure, and exits with 0 when it passed and 1 otherwise.
`errata-fixture` runs one phase of an Errata fixture, writes the value that a setup produces to OUT,
and exits with 0 when the phase succeeded and 1 otherwise. Several invocations may be chained, each
separated by a `;` argument; they run in order in one process, each value that a setup produces
reaches the later invocations, and after an invocation exits non-zero only teardowns run.

Suites declare the settings their tests take in a module-level dictionary `errata_settings_decl` in
a `conftest.py`, which maps each setting's name to a dictionary with its `description` and
optionally its `default`. Tests take settings through the marker `errata_setting(NAME)`, or
`errata_setting(NAME, optional=True)` for those they run without, and read the values they receive
through the `errata_settings` fixture, a dictionary from names to values.

Suites declare Errata fixtures, resources that the runner sets up once per run and shares between
tests, in a module-level dictionary `errata_fixtures_decl` in a `conftest.py`. It maps each
fixture's name to a dictionary with its `description`; optionally `settings`, a list whose items
are a setting's name, which the fixture needs, or a dictionary with the `name` and `optional`;
optionally `fixtures`, the names of fixtures declared before it that it takes; optionally
`threads`; and the callables `setup(context)`, which returns the value as a string,
`prepare(value, context)`, and `teardown(value, context)`, whose value is `None` when the setup
produced none. The context has the attributes `settings` and `fixtures`, dictionaries from names to
values, `threads`, and `config`, the pytest configuration of the loaded suite, which holds the
suite's command-line options. If a fixture declares no prepare or teardown, that phase does
nothing. Tests take fixtures through the marker `errata_fixture(NAME)`, which uses the fixture
alone among its users, or `errata_fixture(NAME, exclusive=False)`, which shares it with other shared
users, and read the values through the `errata_fixtures` fixture, a dictionary from names to values.

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
    "errata_fixture",
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
  python errata_pytest.py PYTEST-ARG... errata-run <out> <node-id> [setting:NAME=VALUE]...
      [fixture:NAME=VALUE]... [threads:N]
  python errata_pytest.py PYTEST-ARG... errata-fixture <out> <name> setup|prepare|teardown
      [setting:NAME=VALUE]... [fixture:NAME=VALUE]... [threads:N]

Several invocations may be chained, each separated by a ';' argument. The Errata runner starts test
executables; to run the tests, run the Errata driver, which is usually `lake test`."""

ERRATA_SETTING_MARKER = (
    "errata_setting(name, optional=False): the test takes the Errata setting with this name, which a "
    "conftest.py declares in errata_settings_decl"
)

ERRATA_FIXTURE_MARKER = (
    "errata_fixture(name, exclusive=True): the test uses the Errata fixture with this name, which a "
    "conftest.py declares in errata_fixtures_decl, alone among its users unless exclusive is False"
)

PHASES = ("setup", "prepare", "teardown")


def register_markers(config):
    """Registers the markers through which a test takes a setting or uses a fixture."""
    config.addinivalue_line("markers", ERRATA_SETTING_MARKER)
    config.addinivalue_line("markers", ERRATA_FIXTURE_MARKER)


def parse_args(rest):
    """
    The settings, the fixtures' values, and the thread grant among an invocation's arguments, as
    two dictionaries and a number.
    """
    settings = {}
    fixtures = {}
    threads = 1
    for arg in rest:
        kind, _, pair = arg.partition(":")
        if kind in ("setting", "fixture") and pair:
            name, _, value = pair.partition("=")
            (settings if kind == "setting" else fixtures)[name] = value
        elif kind == "threads" and pair.isdigit() and int(pair) > 0:
            threads = int(pair)
    return settings, fixtures, threads


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


def item_fixtures(item):
    """
    The Errata fixtures that an item uses, as (name, exclusive) pairs, in the order its markers name
    them.
    """
    seen = {}
    for marker in item.iter_markers("errata_fixture"):
        exclusive = bool(marker.kwargs.get("exclusive", True))
        for name in marker.args:
            if name not in seen:
                seen[name] = exclusive
    return list(seen.items())


def fixture_settings(info):
    """The settings that a fixture's declaration takes, as (name, optional) pairs."""
    out = []
    for item in info.get("settings", []):
        if isinstance(item, str):
            out.append((item, False))
        else:
            out.append((item["name"], bool(item.get("optional", False))))
    return out


def declared_fixtures(config):
    """
    The Errata fixtures that the loaded `conftest.py` files declare, as a dictionary from names to
    their declarations, in the order the files were loaded and declare them. The result is the
    dictionary and a list of problems with the declarations.
    """
    declared = {}
    problems = []
    for _, plugin in config.pluginmanager.list_name_plugin():
        decl = getattr(plugin, "errata_fixtures_decl", None)
        if decl is None:
            continue
        where = getattr(plugin, "__file__", repr(plugin))
        if not isinstance(decl, dict):
            problems.append(f"{where}: errata_fixtures_decl must be a dictionary")
            continue
        for name, info in decl.items():
            if not isinstance(info, dict) or not isinstance(info.get("description", ""), str):
                problems.append(
                    f"{where}: the fixture {name} must map to a dictionary with a description"
                )
            elif name in declared:
                problems.append(f"{where}: the fixture {name} is declared more than once")
            else:
                for dep in info.get("fixtures", []):
                    if dep not in declared:
                        problems.append(
                            f"{where}: the fixture {name} takes the fixture {dep}, which is not "
                            "declared before it"
                        )
                declared[name] = info
    return declared, problems


class FixtureContext:
    """
    What a fixture's phase receives: its settings, its fixtures' values, its thread grant, and the
    pytest configuration of the suite.
    """

    def __init__(self, settings, fixtures, threads, config):
        """A context with the given settings, fixtures' values, thread grant, and configuration."""
        self.settings = settings
        self.fixtures = fixtures
        self.threads = threads
        self.config = config


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
        """Registers the markers through which a test takes a setting or uses a fixture."""
        register_markers(config)

    def pytest_collection_finish(self, session):
        """
        Makes the inventory's records: the settings that the collected tests and their fixtures
        take, in the order the conftest.py files declare them, then the fixtures that the tests
        use, directly or through other fixtures, in the order they are declared, then a test record
        per collected item.
        """
        declared, problems = declared_settings(session.config)
        self.problems.extend(problems)
        fixtures, problems = declared_fixtures(session.config)
        self.problems.extend(problems)
        used = set()
        wanted = set()
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
            uses = item_fixtures(item)
            for name, _ in uses:
                if name not in fixtures:
                    self.problems.append(
                        f"{item.nodeid} uses the fixture {name}, which no conftest.py declares in "
                        "errata_fixtures_decl"
                    )
                wanted.add(name)
            if uses:
                record["fixtures"] = [{"name": n, "exclusive": e} for n, e in uses]
            tests.append(record)
        # Each fixture's own fixtures are declared before it, so one pass from the last reaches all.
        for name in reversed(list(fixtures)):
            if name in wanted:
                wanted.update(fixtures[name].get("fixtures", []))
        fixture_records = []
        for name, info in fixtures.items():
            if name not in wanted:
                continue
            record = {"type": "fixture", "name": name, "description": info.get("description", "")}
            settings = fixture_settings(info)
            for setting, _ in settings:
                if setting not in declared:
                    self.problems.append(
                        f"the fixture {name} takes the setting {setting}, which no conftest.py "
                        "declares in errata_settings_decl"
                    )
                used.add(setting)
            if settings:
                record["settings"] = [{"name": n, "optional": o} for n, o in settings]
            if info.get("fixtures"):
                record["fixtures"] = list(info["fixtures"])
            if "threads" in info:
                record["threads"] = int(info["threads"])
            fixture_records.append(record)
        for name, info in declared.items():
            if name in used:
                record = {"type": "setting", "name": name, "description": info.get("description", "")}
                if "default" in info:
                    record["default"] = info["default"]
                self.records.append(record)
        self.records.extend(fixture_records)
        self.records.extend(tests)


class RunPlugin:
    """Runs one item, collects its reports, and gives the tests their settings and fixtures."""

    def __init__(self, nodeid, settings, fixtures, out):
        """
        Runs the item with the node id, giving it the settings and the fixtures' values and
        writing records to `out`.
        """
        self.nodeid = nodeid
        self.settings = settings
        self.fixtures = fixtures
        self.out = out
        self.found = False
        self.collect_errors = []
        self.reports = {}

    def pytest_configure(self, config):
        """Registers the markers through which a test takes a setting or uses a fixture."""
        register_markers(config)

    @pytest.fixture(scope="session")
    def errata_settings(self):
        """The values of the Errata settings that the test received, by name."""
        return dict(self.settings)

    @pytest.fixture(scope="session")
    def errata_fixtures(self):
        """The values of the Errata fixtures that the test received, by name."""
        return dict(self.fixtures)

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
    The verdict of a skipped report. Expected failures pass, and all other skips are errors: tests
    whose preconditions fail have shown nothing.
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
    settings, fixtures, _ = parse_args(rest)
    with open(out_path, "a", encoding="utf-8") as out:
        write_record(out, {"type": "protocol", "version": 1})
        plugin = RunPlugin(nodeid, settings, fixtures, out)
        # Without capturing, what the test prints reaches the runner as it is printed.
        code = pytest.main(
            ["--capture=no", *pytest_args, "-p", "no:cacheprovider"], plugins=[plugin]
        )
        verdict = plugin.verdict(code)
        write_record(out, verdict)
    return 0 if verdict["status"] == "pass" else 1


class FixturePlugin:
    """Learns the Errata fixtures that the suite's `conftest.py` files declare."""

    def __init__(self):
        """Starts with no fixtures and no configuration."""
        self.fixtures = {}
        self.problems = []
        self.config = None

    def pytest_configure(self, config):
        """Registers the markers through which a test takes a setting or uses a fixture."""
        register_markers(config)

    def pytest_collection_finish(self, session):
        """Reads the fixtures' declarations and keeps the suite's configuration."""
        self.fixtures, self.problems = declared_fixtures(session.config)
        self.config = session.config


# What a fixture's phase may raise and the harness reports as the phase's verdict: any error, and
# the exceptions that `pytest.fail`, `pytest.skip`, `pytest.exit`, and `sys.exit` raise, which
# derive from `BaseException` alone. `KeyboardInterrupt` ends the process as it would anywhere else.
PHASE_ERRORS = (
    Exception,
    SystemExit,
    pytest.fail.Exception,
    pytest.skip.Exception,
    pytest.exit.Exception,
)


def failed_phase_verdict(error):
    """
    The verdict of a phase that raised an error: a failed assertion fails, and the rest are errors,
    with the message of `pytest.fail`, `pytest.skip`, or `pytest.exit`, or the code of `sys.exit`.
    """
    status = "fail" if isinstance(error, AssertionError) else "error"
    if isinstance(error, (pytest.fail.Exception, pytest.skip.Exception, pytest.exit.Exception)):
        detail = getattr(error, "msg", "") or str(error)
        message = f"{type(error).__name__}: {detail}" if detail else type(error).__name__
    elif isinstance(error, SystemExit):
        message = f"the phase called sys.exit({error.code!r})"
    else:
        message = str(error) or type(error).__name__
    return {"type": "verdict", "status": status, "message": message}


def run_fixture(pytest_args, out_path, name, phase, rest):
    """
    Runs one phase of the Errata fixture with the name, writes its records, and returns the exit
    code with the value that a setup produced.
    """
    settings, fixtures, threads = parse_args(rest)
    with open(out_path, "a", encoding="utf-8") as out:
        write_record(out, {"type": "protocol", "version": 1})
        plugin = FixturePlugin()
        code = pytest.main(
            [*pytest_args, "--collect-only", "-p", "no:terminal", "-p", "no:cacheprovider"],
            plugins=[plugin],
        )
        if code not in (pytest.ExitCode.OK, pytest.ExitCode.NO_TESTS_COLLECTED):
            message = f"pytest ended with exit code {int(code)} ({exit_code_name(code)}) while it " \
                "loaded the suite; its output says why"
            write_record(out, {"type": "verdict", "status": "error", "message": message})
            return 1, None
        for problem in plugin.problems:
            print(f"errata_pytest.py: {problem}", file=sys.stderr)
        info = plugin.fixtures.get(name)
        if info is None:
            message = f"no fixture is named {name}"
            print(message, file=sys.stderr)
            write_record(out, {"type": "verdict", "status": "error", "message": message})
            return 1, None
        action = info.get(phase)
        if action is None:
            # Prepares and teardowns without a callable have nothing to do; a setup needs one.
            if phase != "setup":
                return 0, None
            message = f"the fixture {name} declares no setup"
            write_record(out, {"type": "verdict", "status": "error", "message": message})
            return 1, None
        context = FixtureContext(settings, fixtures, threads, plugin.config)
        start = time.monotonic()
        try:
            if phase == "setup":
                value = action(context)
                value = "" if value is None else str(value)
            else:
                action(fixtures.get(name), context)
                value = None
        except PHASE_ERRORS as error:  # noqa: BLE001 - every error of the phase is its verdict
            verdict = failed_phase_verdict(error)
            verdict["duration_ms"] = int((time.monotonic() - start) * 1000)
            write_record(out, verdict)
            return 1, None
        if value is not None:
            write_record(out, {"type": "value", "text": value})
        return 0, value


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
    Performs the invocation that the arguments give, or each invocation of a chain whose
    invocations are separated by `;` arguments, in order. Each value that a setup produces is added
    to the later errata-run and errata-fixture invocations as that fixture's `fixture:NAME=VALUE`
    argument, and after an invocation exits non-zero only teardowns run. The result is the exit code
    of the first invocation other than a teardown that exited non-zero, or else that of the first
    teardown that did, or else 0. The pytest arguments precede the first invocation and serve them
    all.
    """
    links = split_chain(argv)
    first = links[0]
    mode_at = next((i for i, a in enumerate(first) if a in MODES), None)
    if mode_at is None:
        print(USAGE, file=sys.stderr)
        return 2
    pytest_args = first[:mode_at]
    links[0] = first[mode_at:]
    failure = None
    teardown_failure = None
    carried = []
    for link in links:
        is_teardown = len(link) >= 4 and link[0] == "errata-fixture" and link[3] == "teardown"
        if (failure is not None or teardown_failure is not None) and not is_teardown:
            continue
        if link and link[0] in ("errata-run", "errata-fixture"):
            link = link + carried
        # Each invocation imports the suite afresh, as a process of its own would.
        modules = set(sys.modules)
        try:
            code, produced = invoke(pytest_args, link)
        finally:
            for name in set(sys.modules) - modules:
                del sys.modules[name]
        if produced is not None:
            carried.append(f"fixture:{produced[0]}={produced[1]}")
        if code != 0:
            if is_teardown:
                teardown_failure = code if teardown_failure is None else teardown_failure
            else:
                failure = code if failure is None else failure
    # The first invocation other than a teardown that failed decides the status, then a teardown.
    if failure is not None:
        return failure
    return teardown_failure if teardown_failure is not None else 0


def invoke(pytest_args, link):
    """
    Performs one invocation, and returns its exit code with the fixture and the value that a setup
    produced.
    """
    mode, rest = (link[0], link[1:]) if link else ("", [])
    if mode == "errata-list" and len(rest) == 1:
        return list_tests(pytest_args, rest[0]), None
    if mode == "errata-run" and len(rest) >= 2:
        return run_test(pytest_args, rest[0], rest[1], rest[2:]), None
    if mode == "errata-fixture" and len(rest) >= 3 and rest[2] in PHASES:
        code, value = run_fixture(pytest_args, rest[0], rest[1], rest[2], rest[3:])
        return code, (rest[1], value) if value is not None else None
    print(USAGE, file=sys.stderr)
    return 2, None


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
