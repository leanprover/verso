#!/usr/bin/env bash
set -euo pipefail

# Exercise the `serve` development server against a real loopback socket.
# Builds the executable, serves a small fixture directory, and checks status
# codes and the cache, ETag, and Range headers with curl.

PORT=8731
FIXTURE="$(mktemp -d)"
SERVER_PID=""

cleanup() {
    if [[ -n "$SERVER_PID" ]]; then
        kill "$SERVER_PID" 2>/dev/null || true
        wait "$SERVER_PID" 2>/dev/null || true
    fi
    rm -rf "$FIXTURE"
}
trap cleanup EXIT

fail() {
    echo "  FAILED: $1" >&2
    exit 1
}

echo "Building serve..."
lake build serve

printf '<h1>home</h1>' > "$FIXTURE/index.html"
printf 'body{color:red}' > "$FIXTURE/style.css"
printf '0123456789abcdef' > "$FIXTURE/data.txt"
mkdir -p "$FIXTURE/sub"
printf 'child' > "$FIXTURE/sub/page.html"

echo "Starting serve on port ${PORT}..."
./.lake/build/bin/serve --port "$PORT" --strict-port --quiet "$FIXTURE" &
SERVER_PID=$!

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
