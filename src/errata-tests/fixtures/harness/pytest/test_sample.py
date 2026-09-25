"""
Tests that show the conformance suite how a pytest test can end: passing, failing, with an error in
its setup, parameterized, with an odd parameter id, marked, inside a class, taking settings, and
printing the run's identifier; and tests that use the suite's Errata fixtures.
"""

import os
import time

import pytest


def test_passes():
    """A test that passes."""
    assert 1 + 1 == 2


def test_fails():
    """A test that fails an assertion."""
    value = 3
    assert value == 4, "the value is off"


def test_errors(broken):
    """A test whose fixture fails before it runs."""
    assert broken


@pytest.mark.parametrize("n", [1, 2])
def test_squares(n):
    """A parameterized test."""
    assert n * n >= n


@pytest.mark.parametrize("s", ["x"], ids=["a::b/c"])
def test_odd_id(s):
    """A test whose parameter id holds `::` and `/`."""
    assert s == "x"


@pytest.mark.chatty
def test_marked():
    """A test with a marker."""
    print("chatting")


class TestGroup:
    def test_inside(self):
        """A test inside a class."""
        assert True


@pytest.mark.errata_setting("greeting")
def test_greets(errata_settings):
    """A test that prints the greeting it receives."""
    print(f"received greeting={errata_settings['greeting']}")


def test_run_id():
    """A test that prints the run's identifier."""
    print(f"run id: {os.environ.get('ERRATA_RUN_ID', '')}")


@pytest.mark.errata_setting("needed")
def test_needs_setting():
    """A test that takes a setting without a default."""
    print("ran without its setting")


def stamped_use(name, errata_fixtures):
    """Stamps the file that the fixture's value names as it starts and, a moment later, as it ends."""
    path = errata_fixtures.get("stamped", "")
    if path:
        with open(path, "a", encoding="utf-8") as f:
            f.write(f"start {name}\n")
    time.sleep(0.4)
    if path:
        with open(path, "a", encoding="utf-8") as f:
            f.write(f"end {name}\n")


@pytest.mark.errata_fixture("stamped")
def test_exclusive_a(errata_fixtures):
    """A user of `stamped` alone among its users."""
    stamped_use("test_exclusive_a", errata_fixtures)


@pytest.mark.errata_fixture("stamped")
def test_exclusive_b(errata_fixtures):
    """Another user of `stamped` alone among its users."""
    stamped_use("test_exclusive_b", errata_fixtures)


@pytest.mark.errata_fixture("stamped", exclusive=False)
def test_shared_a(errata_fixtures):
    """A user of `stamped` beside other shared users."""
    stamped_use("test_shared_a", errata_fixtures)


@pytest.mark.errata_fixture("stamped", exclusive=False)
def test_shared_b(errata_fixtures):
    """Another user of `stamped` beside other shared users."""
    stamped_use("test_shared_b", errata_fixtures)


def print_fixtures(errata_fixtures):
    """Prints the fixtures' values that the test received."""
    for name, value in errata_fixtures.items():
        print(f"received fixture:{name}={value}")


@pytest.mark.errata_fixture("setup-fails")
def test_after_setup_failure(errata_fixtures):
    """A user of the fixture whose setup fails."""
    print_fixtures(errata_fixtures)


@pytest.mark.errata_fixture("prepare-fails")
def test_after_prepare_failure_a(errata_fixtures):
    """The first user of the fixture whose first prepare fails."""
    print_fixtures(errata_fixtures)


@pytest.mark.errata_fixture("prepare-fails")
def test_after_prepare_failure_b(errata_fixtures):
    """The second user of the fixture whose first prepare fails."""
    print_fixtures(errata_fixtures)


@pytest.mark.errata_fixture("teardown-fails")
def test_before_teardown_failure(errata_fixtures):
    """A user of the fixture whose teardown fails."""
    print_fixtures(errata_fixtures)


@pytest.mark.errata_fixture("dependent")
def test_uses_dependent(errata_fixtures):
    """A user of the fixture that takes a setting and another fixture."""
    print_fixtures(errata_fixtures)


@pytest.mark.errata_fixture("slow-setup")
def test_after_slow_setup(errata_fixtures):
    """A user of the fixture whose setup sleeps."""
    print_fixtures(errata_fixtures)


@pytest.mark.errata_fixture("threaded")
def test_uses_threaded(errata_fixtures):
    """A user of the fixture that asks for threads."""
    print_fixtures(errata_fixtures)
