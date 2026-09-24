"""
The configuration of a small pytest suite that the conformance suite runs through Verso's pytest
harness. It declares the suite's Errata settings, a fixture whose setup fails, and the suite's own
marker.
"""

import pytest

# The Errata settings that the suite's tests take: a greeting with a default, and a setting without
# one.
errata_settings_decl = {
    "greeting": {"description": "A greeting.", "default": "hello"},
    "needed": {"description": "A setting without a default."},
}


def pytest_configure(config):
    """Registers the suite's marker."""
    config.addinivalue_line("markers", "chatty: a test that talks")


@pytest.fixture
def broken():
    """A fixture whose setup fails."""
    raise RuntimeError("the fixture broke")
