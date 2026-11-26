/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import VersoTutorial
import TutorialExample

open Verso.Genre Tutorial

open Verso.Doc.Concrete in
def content : Tutorials where
  content :=
    (verso (Blog.Page) "Example Tutorial Site"
    ::::
    Here are some examples of the tutorials feature.
    ::::).toPart

  topics := #[
    { title := #[inlines!"Data"],
      titleString := "Data",
      description := #[blocks!"These tutorials describe the use of data in Lean."]
      tutorials := #[
        %doc TutorialExample.Data,
        %doc TutorialExample.HashMap,
        literate_part⟨"." TutorialExample.Lit "Literately-Produced Tutorial" {slug := "literate", summary := inlines!"checks that we can load them", exampleStyle := .inlineLean `Lit} : Tutorial⟩ |>.toPart]
    },
    { title := #[inlines!"Tactics"],
      titleString := "Tactics",
      description := #[]
      tutorials := #[%doc TutorialExample.RCases]
    }

  ]

open Verso.Output.Html.ContentSecurityPolicy (Host Port Source)
open Verso.Genre.Manual (DataFile JS)

/-
The scripts below each set a marker on `window` that the browser tests in
`browser-tests/tutorial` check. Every generated page carries a content security policy, so a script
whose hash or origin the policy lacks is blocked, its marker stays unset, and the browser reports a
violation.
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

-- Tutorial pages don't include `extraHead`, so an inline script loads the external script.
def externalScriptLoader (port : Port) : JS :=
  ⟨"(() => {\n" ++
    "  const script = document.createElement('script');\n" ++
    s!"  script.src = '{externalScriptUrl port}';\n" ++
    "  document.head.append(script);\n" ++
    "})();\n"⟩

def siteConfig (localhost : Host) (port : Option Port) : Config where
  destination := "_out/tut"
  extraJs :=
    -- An ordinary inline script added through `extraJs`.
    ({⟨"window.tutorialExtraJs = true;"⟩} : Std.HashSet JS).insertMany
      (port.map externalScriptLoader).toArray
  extraJsFiles := {
    -- A script file added through `extraJsFiles`, which loads from the site's own origin.
    { filename := "tutorial-extra.js"
      contents := ⟨"window.tutorialExtraJsFile = true;\n"⟩
      sourceMap? := none }
  }
  extraDataFiles := {externalScript}
  contentSecurityPolicy :=
    { extraScriptSources := (port.map (externalScriptSource localhost)).toArray }

def main (args : List String) : IO UInt32 := do
  let port ← externalScriptPort
  let localhost ← IO.ofExcept (Host.ofString "localhost")
  tutorialsMain content args (config := siteConfig localhost port)
