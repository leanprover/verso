/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

open Verso.Genre Manual InlineLean


#doc (Manual) "Verso 4.32.0 (unreleased)" =>
%%%
tag := "release-v4.32.0"
file := "v4.32.0"
%%%

* Added a {ref "feat-serve"}[development server] for previewing generated HTML locally with `lake exe serve` (#876).

# Development Server
%%%
tag := "feat-serve"
%%%

Verso now includes a small HTTP server for previewing generated HTML on your own machine.
Running `lake exe serve` serves the current directory at `http://127.0.0.1:8000/`, and a directory and `--port` may be given on the command line.

The server is meant for local writing and development.
It binds to `127.0.0.1` only and offers no HTTPS or authentication.

Its defaults suit Verso output.
Additionally, a `serve.toml` file configures mounts, redirects, and custom headers for projects that need more than a single directory.
Because the server ships with Verso, previewing a site no longer depends on having another language ecosystem installed.

See the {ref "serve"}[development server documentation] for the full set of options.
