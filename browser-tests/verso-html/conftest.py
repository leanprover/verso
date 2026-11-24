import pytest


@pytest.fixture
def missing_file_allowlist():
    """The site is generated without the source directory, so the images of the test project are
    not copied."""
    return ["/images/test-diagram.png"]
