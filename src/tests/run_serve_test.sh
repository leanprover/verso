#!/usr/bin/env bash
# The test of the `verso-serve` development server, as an Errata test executable on Errata's shell
# harness with one test, `serve`. The test serves a small fixture directory on a loopback socket and
# checks status codes and the cache, ETag, and Range headers with curl. It takes the built executable
# as the setting `versoServeExe`, which `errata.toml` binds to the Lake target `verso-serve`.

source "$ERRATA_DIR/harnesses/errata.sh"

# Declares the built executable that the test serves with.
errata_settings() {
  errata_setting_decl versoServeExe "The built verso-serve executable."
}

# Declares the one test.
errata_tests() {
  errata_test serve --path serve --file src/tests/run_serve_test.sh --tags serve \
    --settings versoServeExe \
    --description "verso-serve answers with the expected status codes and cache, ETag, and Range headers."
}

# Runs the test. Each failed check fails the test with a verdict that names the check.
errata_run_test() {
  set -euo pipefail

  local server
  if ! server=$(errata_setting versoServeExe); then
    errata_fail "the test needs the setting versoServeExe"
    exit 1
  fi

  FIXTURE="$(mktemp -d)"
  BANNER="$(mktemp)"
  SERVER_PID=""

  # Stops the server and removes the fixture directory.
  cleanup() {
    if [[ -n "$SERVER_PID" ]]; then
      kill "$SERVER_PID" 2>/dev/null || true
      wait "$SERVER_PID" 2>/dev/null || true
    fi
    rm -rf "$FIXTURE"
    rm -f "$BANNER"
  }
  trap cleanup EXIT

  # Fails the test with the message, which names the failed check.
  fail() {
    echo "  FAILED: $1" >&2
    errata_fail "$1" || true
    exit 1
  }

  printf '<h1>home</h1>' > "$FIXTURE/index.html"
  printf 'body{color:red}' > "$FIXTURE/style.css"
  printf '0123456789abcdef' > "$FIXTURE/data.txt"
  mkdir -p "$FIXTURE/sub"
  printf 'child' > "$FIXTURE/sub/page.html"

  echo "Starting verso-serve (scanning for a free port)..."
  # No fixed port: let the server take the first free one and report it in its banner.
  "$server" --quiet "$FIXTURE" > "$BANNER" 2>/dev/null &
  SERVER_PID=$!

  # Read the chosen port from the startup banner, waiting up to ~10 seconds for it.
  PORT=""
  for _ in $(seq 1 50); do
    PORT="$(sed -nE 's#.*http://127\.0\.0\.1:([0-9]+)/.*#\1#p' "$BANNER" | head -1)"
    [[ -n "$PORT" ]] && break
    sleep 0.2
  done
  [[ -n "$PORT" ]] || fail "server did not report a port"
  echo "  using port ${PORT}"

  BASE="http://127.0.0.1:${PORT}"

  # Wait for the server to accept connections, up to ~10 seconds.
  ready=""
  for _ in $(seq 1 50); do
    if curl -s -o /dev/null "${BASE}/"; then
      ready=1
      break
    fi
    sleep 0.2
  done
  [[ -n "$ready" ]] || fail "server did not become ready"

  # Prints the status code of a request.
  status() { curl -s -o /dev/null -w '%{http_code}' "$@"; }

  echo "  index serves 200"
  [[ "$(status "${BASE}/")" == "200" ]] || fail "GET / was not 200"

  echo "  cache and validators present"
  headers="$(curl -s -D - -o /dev/null "${BASE}/style.css")"
  grep -qi '^Content-Type: text/css' <<<"$headers" || fail "missing css content type"
  grep -qi '^Cache-Control: no-cache' <<<"$headers" || fail "missing Cache-Control: no-cache"
  grep -qi '^ETag:' <<<"$headers" || fail "missing ETag"
  grep -qi '^Last-Modified:' <<<"$headers" || fail "missing Last-Modified"
  grep -qi '^Accept-Ranges: bytes' <<<"$headers" || fail "missing Accept-Ranges"

  echo "  HEAD returns headers without a body"
  head_headers="$(curl -sI "${BASE}/data.txt")"
  grep -qi '^HTTP/1.1 200' <<<"$head_headers" || fail "HEAD was not 200"
  grep -qi '^Content-Length: 16' <<<"$head_headers" || fail "HEAD had missing or wrong Content-Length"
  grep -qi '^Accept-Ranges: bytes' <<<"$head_headers" || fail "HEAD missing Accept-Ranges"

  echo "  conditional request returns 304"
  etag="$(curl -s -D - -o /dev/null "${BASE}/data.txt" | grep -i '^ETag:' | tr -d '\r' | awk '{print $2}')"
  [[ -n "$etag" ]] || fail "no ETag to revalidate with"
  [[ "$(status -H "If-None-Match: ${etag}" "${BASE}/data.txt")" == "304" ]] || fail "If-None-Match was not 304"

  echo "  range request returns 206"
  range_headers="$(curl -s -D - -o /dev/null -H 'Range: bytes=0-3' "${BASE}/data.txt")"
  grep -qi '^HTTP/1.1 206' <<<"$range_headers" || fail "Range did not return 206"
  grep -qi '^Content-Range: bytes 0-3/16' <<<"$range_headers" || fail "missing or wrong Content-Range"

  echo "  directory without slash redirects"
  [[ "$(status "${BASE}/sub")" == "301" ]] || fail "directory was not redirected"

  echo "  missing path returns 404"
  [[ "$(status "${BASE}/nope")" == "404" ]] || fail "missing path was not 404"

  echo "  encoded traversal is refused"
  [[ "$(status "${BASE}/%2e%2e/%2e%2e/etc/passwd")" != "200" ]] || fail "encoded traversal returned 200"

  echo "  symlinked index escaping the root is refused"
  SECRET="$(mktemp)"
  printf 'TOPSECRET' > "$SECRET"
  mkdir -p "$FIXTURE/evil"
  ln -s "$SECRET" "$FIXTURE/evil/index.html"
  evil_code="$(status "${BASE}/evil/")"
  [[ "$evil_code" == "403" || "$evil_code" == "404" ]] || fail "symlinked index escaped the root (got $evil_code)"
  [[ "$(curl -s "${BASE}/evil/")" != *TOPSECRET* ]] || fail "symlinked index leaked a file outside the root"
  rm -f "$SECRET"

  echo "  disallowed method returns 405"
  [[ "$(status -X POST "${BASE}/")" == "405" ]] || fail "POST was not 405"

  echo "All serve tests passed."
}

errata_main "$@"
