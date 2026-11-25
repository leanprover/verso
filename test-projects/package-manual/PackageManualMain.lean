/-
Copyright (c) 2024-2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import Std.Data.HashMap
import VersoManual
import PackageManual

open Verso Doc
open Verso.Genre Manual

open Std (HashMap)

open PackageManual

open Verso.Output.Html.ContentSecurityPolicy (Host Port Source)

/-
The scripts below each set a marker on `window` that the browser tests in
`browser-tests/package-manual` check. Every generated page carries a content security policy, so a
script whose hash or origin the policy lacks is blocked, its marker stays unset, and the browser
reports a violation.
-/

-- A script file in the site's data directory. With an external script port, every page loads it
-- from `localhost` on that port, which is a different origin from the one that serves the pages
-- in the browser tests. The script runs only because the policy lists that origin as an extra
-- script source.
def externalScript : DataFile where
  filename := "external-script.js"
  contents := "window.versoExternalScript = true;\n".toUTF8

-- `VERSO_TEST_EXTERNAL_SCRIPT_PORT` is the port on `localhost` from which every page loads
-- `external-script.js`. The browser tests set it. Without it, the site doesn't refer to an external
-- origin.
def externalScriptPort : IO (Option Port) := do
  match ← IO.getEnv "VERSO_TEST_EXTERNAL_SCRIPT_PORT" with
  | none | some "" => pure none
  | some text =>
    match text.toNat? with
    | none => throw <| .userError s!"VERSO_TEST_EXTERNAL_SCRIPT_PORT: {text.quote} isn't a number."
    | some n =>
      match Port.ofInt n with
      | .ok port => pure (some port)
      | .error e => throw <| .userError s!"VERSO_TEST_EXTERNAL_SCRIPT_PORT: {e}"

def externalScriptSource (localhost : Host) (port : Port) : Source :=
  { scheme := some .http, host := localhost, port := some port }

def externalScriptUrl (port : Port) : String :=
  s!"http://localhost:{port.number}/-verso-data/{externalScript.filename}"

open Verso.Output.Html in
def config (localhost : Host) (port : Option Port) : Config where
  emitTeX := false
  emitHtmlSingle := .no
  emitHtmlMulti := .immediately
  htmlDepth := 2
  extraJs := {
    -- An ordinary inline script added through `extraJs`.
    ⟨"window.packageManualExtraJs = true;"⟩,
    -- A body with a CRLF and a lone CR. Browsers normalize both to LF before hashing, so this
    -- checks that the policy's hash matches.
    ⟨"window.packageManualCrLf = true;\r\nwindow.packageManualLoneCr = true;\r"⟩,
    -- A body with a NUL character in a string literal. Browsers replace NUL with U+FFFD before
    -- hashing, so this checks that the policy's hash matches.
    ⟨"window.packageManualNul = \"a\x00b\";"⟩,
    -- A body with U+2028 in a string literal, an accented letter, and an emoji. This checks that
    -- non-ASCII text is hashed as UTF-8, including a character that JavaScript treats as a line
    -- terminator outside of string literals.
    ⟨"window.packageManualNonAscii = \"line\u2028separator, café, 🦒\";"⟩
  }
  extraJsFiles := {
    -- A script file added through `extraJsFiles`, which loads from the site's own origin.
    { filename := "package-manual-extra.js"
      contents := ⟨"window.packageManualExtraJsFile = true;\n"⟩
      sourceMap? := none }
  }
  extraHead := #[
    -- An ordinary inline script added through `extraHead`.
    html%{<script>{"window.packageManualExtraHead = true;"}</script>},
    -- A body that is a text node with `&&` and `<`. The printer escapes them, and the browser
    -- runs and hashes the escaped text, so this checks that the policy hashes the printed body.
    -- The characters are in a string literal so that the escaped body is still valid JavaScript.
    html%{<script>{"window.packageManualEscapedText = \"a && b < c\";"}</script>},
    -- A body that is a raw node starting with `<!--`, which JavaScript treats as the start of a
    -- line comment. This checks that the body is hashed exactly as written.
    html%{<script>{Lean.Html.raw "<!-- a comment in HTML syntax\nwindow.packageManualHtmlComment = true;"}</script>},
  ] ++ (port.map fun port => html%{<script src={externalScriptUrl port}></script>}).toArray
  extraContents := #[
    -- A script in inline SVG whose body is a text node with `&&` and `<`. In SVG, the browser
    -- decodes the printer's escapes, so it runs and hashes the original text. This checks that the
    -- policy hashes the decoded body.
    html%{<svg width="0" height="0"><script>{"window.packageManualSvgText = \"a && b < c\";"}</script></svg>},
    -- A script in an SVG `foreignObject`, where the browser parses HTML again. It runs and hashes
    -- the escaped text, as in `extraHead`.
    html%{<svg width="0" height="0"><foreignObject><script>{"window.packageManualForeignObjectText = \"a && b\";"}</script></foreignObject></svg>}
  ]
  extraDataFiles := {externalScript}
  contentSecurityPolicy :=
    { extraScriptSources := (port.map (externalScriptSource localhost)).toArray }

def main (args : List String) : IO UInt32 := do
  let port ← externalScriptPort
  let localhost ← IO.ofExcept (Host.ofString "localhost")
  manualMain (%doc PackageManual) (options := args) (config := { config localhost port with })
