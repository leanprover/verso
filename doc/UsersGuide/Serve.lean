/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import Lean.DocString.Syntax
import VersoManual

open Verso Genre Manual
open Verso.Doc

#doc (Manual) "Development Server" =>
%%%
tag := "serve"
htmlSplit := .never
%%%

Verso includes a small HTTP server for previewing generated HTML on your own machine.
Run it with `lake exe serve`.

The server is for *local development only*.
It offers no HTTPS and no authentication.
Do not use it to serve a real site.

# Running the Server
%%%
tag := "serve-running"
%%%

:::paragraph
With no arguments, the current directory is served at `http://127.0.0.1:8000/`:

```
$ lake exe serve
```

A directory to serve and a port may be given on the command line:

```
$ lake exe serve --port 8000 _out/html
```
:::

If the requested port is already in use, the server scans the following ports for a free one and prints the port it settled on, so several servers started with default settings can run at once.
Pass `--strict-port` to fail instead.

:::paragraph
As requests arrive, each is logged with the active port, the method, the path, and the response status:

```
[8000] GET /index.html 200
[8000] GET /missing 404
```
:::

# Command-Line Options
%%%
tag := "serve-options"
%%%

: `DIR`

  The directory served at `/`, relative to the current directory. Defaults to the current directory.

: `--port PORT`, `-p PORT`

  The port to listen on. Defaults to `8000`.

: `--strict-port`

  Fail if the port is in use instead of trying another.

: `--config FILE`

  Load configuration from `FILE`. Defaults to `./serve.toml` if it exists.

: `--no-listing`

  Disable directory listings.

: `--no-trailing-slash-redirect`

  Serve directories in place instead of redirecting to add a trailing slash.

: `--cors`

  Send permissive cross-origin headers.

: `--quiet`

  Suppress per-request logging.

: `--verbose`, `-v`

  Log additional detail.

: `--help`, `-h`

  Show usage and exit.

Command-line options override values from the configuration file.

# Configuration File
%%%
tag := "serve-config"
%%%

For anything beyond serving a single directory, place a `serve.toml` file next to the project, or point at one with `--config`.
Directories named in the configuration file are resolved relative to the configuration file itself.
Every setting is optional, and an empty file behaves the same as no file.

Every option is described here.
The sections that follow add detail on mounts, redirects, and custom headers.

: `port`

  The port to listen on. Must be a number from `1` to `65535`. Defaults to `8000`.

: `banner`

  A line shown in the startup banner to identify the project. Must be a string. No banner is shown by default.

: `cors`

  Whether to send permissive cross-origin headers and answer `OPTIONS` preflight requests. Must be a boolean. Defaults to `false`.

: `directory_listing`

  Whether to generate an HTML listing for a directory that has no `index.html`. Must be a boolean. Defaults to `true`.

: `trailing_slash_redirect`

  Whether a request for a directory without a trailing slash is redirected to add one. Must be a boolean. Defaults to `true`.

: `follow_symlinks_outside_root`

  Whether a symbolic link may resolve to a target outside every mounted directory. Must be a boolean. Defaults to `false`.

: `[[mounts]]`

  Configures a mount, serving a directory at a URL prefix. The mount with the longest matching prefix wins.

  : `path`

    The URL prefix to serve at. Must be a string that begins with `/`.

  : `dir`

    The directory served under the prefix. Must be a string, resolved relative to the configuration file.

: `[[redirects]]`

  Configures a redirect. Redirects are matched by their path prefix in order. The first match wins.

  : `from`

    The path prefix to match. Must be a string that begins with `/`.

  : `to`

    The location to redirect to. Must be a string. The path beneath the matched prefix is appended to it.

  : `status`

    The redirect status code. Must be one of `301`, `302`, `303`, `307`, or `308`. Defaults to `301`.

: `[[headers]]`

  Configures a header rule, adding response headers to requests whose path begins with its prefix.

  : `path`

    The path prefix the rule applies to. Must be a string that begins with `/`.

  : `set`

    A table mapping header names to the values to set on matching responses.

For example, this configuration serves a built site at `/` with the API reference mounted under `/api`, names the project in the banner, turns off directory listings, redirects an old entry point, and adds a header to everything:

```
port = 4000
banner = "ACME Docs"
directory_listing = false

[[mounts]]
path = "/"
dir = "_out/html"

[[mounts]]
path = "/api"
dir = "_out/api"

[[redirects]]
from = "/index.htm"
to = "/"

[[headers]]
path = "/"
set = { "X-Frame-Options" = "DENY" }
```

## Mounts
%%%
tag := "serve-mounts"
%%%

A mount maps a URL prefix to a directory on disk.
The mount whose prefix matches the most path segments wins, so more specific mounts override more general ones.

```
[[mounts]]
path = "/"
dir = "_out/html"

[[mounts]]
path = "/foo"
dir = "../foo-output"

[[mounts]]
path = "/foo/x"
dir = "../special"
```

With these mounts, `/foo/x/page.html` is served from `../special`, other paths under `/foo` from `../foo-output`, and everything else from `_out/html`.
Two mounts may name the same directory.
If a directory named by a mount does not exist, the server reports an error and exits rather than starting up in a broken state.

:::paragraph
The directory served at `/` is chosen in this order:
 1. If a directory `DIR` is provided as a positional command-line parameter, then it is used.
    If the configuration file includes a mount for `/`, then it is replaced by `DIR`.
 2. If no `DIR` is provided, then the `/` mount from the configuration file is served.
 3. Otherwise, the current directory is served at `/`.
:::

## Redirects
%%%
tag := "serve-redirects"
%%%

Redirect rules are matched against the request path by prefix, in order, and the first match wins.
The path beneath the matched prefix is appended to the target.

```
[[redirects]]
from = "/old"
to = "/new"
status = 301

[[redirects]]
from = "/legacy"
to = "/current"
status = 302
```

## Custom Headers
%%%
tag := "serve-headers"
%%%

Header rules add response headers to requests whose path begins with a prefix.
Later rules override earlier ones for the same header name.

```
[[headers]]
path = "/assets"
set = { "Cache-Control" = "no-cache", "X-Frame-Options" = "DENY" }
```

# Caching
%%%
tag := "serve-caching"
%%%

Every response carries `Cache-Control: no-cache`, which directs the browser to revalidate before reusing a cached copy rather than to skip caching entirely.
Each file response also carries an `ETag` derived from the file's contents and a `Last-Modified` time.

When a browser revalidates with `If-None-Match` or `If-Modified-Since` and the file is unchanged, the server replies `304 Not Modified` with no body.
Because the `ETag` follows the contents, a rebuild that rewrites a file without changing it still revalidates cheaply.

# Other Behavior
%%%
tag := "serve-behavior"
%%%

 * A file's `Content-Type` comes from its extension.
  A file whose extension is unknown is served as `text/plain` when its contents are valid UTF-8 text, so text-like files open in the browser instead of downloading, and as `application/octet-stream` otherwise.
 * Directories are served by their `index.html` when one is present; otherwise a generated listing is shown unless listings are disabled, in which case the request is refused with `403 Forbidden`.
 * A request for a directory without a trailing slash is redirected to add one, so relative links resolve correctly. This can be turned off.
 * `Range` requests are supported, so media files can be sought and large files resumed.
 * Symbolic links are followed only while their target stays within a mounted directory. A link pointing outside every mount is refused, unless `follow_symlinks_outside_root` is set.
 * Only `GET` and `HEAD` are served. Other methods receive `405 Method Not Allowed`. With CORS enabled, `OPTIONS` preflight requests are answered.
