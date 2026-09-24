"""
Tests that show the conformance suite how a pytest test can end: passing, failing, with an error in
its setup, parameterized, marked, inside a class, and taking settings.
"""

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


@pytest.mark.errata_setting("needed")
def test_needs_setting():
    """A test that takes a setting without a default."""
    print("ran without its setting")
