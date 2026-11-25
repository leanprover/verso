import pytest


# The demo site's theme loads a stylesheet from a CDN. It is answered locally with an empty
# stylesheet, so that page loads don't wait on the network.
@pytest.fixture
def page(page):
    page.route(
        "https://cdn.jsdelivr.net/**",
        lambda route: route.fulfill(status=200, content_type="text/css", body=""),
    )
    return page


# The port of `http://localhost`, from which the demo site's theme loads
# `static/external-script.js`. It is the port of the `server` fixture, which serves the site from
# `127.0.0.1`. `localhost` on the same port is therefore a different origin to the browser that
# reaches the same files, and the site's content security policy must list it.
@pytest.fixture(scope="session")
def external_script_port(request):
    port = request.config.getoption("--port")
    if port is None:
        pytest.fail(
            "The blog tests need --port. Build the demo site with "
            "VERSO_TEST_EXTERNAL_SCRIPT_PORT=PORT and pass the same PORT.",
            pytrace=False,
        )
    return int(port)
