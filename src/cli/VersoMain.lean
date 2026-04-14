/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import Lean.Data.Json
import Lean.Data.NameMap
import Std.Data.HashMap
import Std.Time.DateTime

import MultiVerso

open Lean (Json NameMap)
open Verso.Multi
open Std

/-- The contents of the GitHub Pages workflow template, embedded at compile time. -/
def versoLiteratePagesYml : String :=
  include_str "../../gh-setup/verso-literate-pages.yml"

structure CliConfig where
  configFile : Option System.FilePath := none
  verbose : Bool := false

def CliConfig.logVerbose (msg : String) (config : CliConfig) : IO Unit := do
  if config.verbose then IO.println msg else pure ()

inductive Command where
  | sync
  | setupLiterate

def Command.name : Command → String
  | sync => "sync"
  | setupLiterate => "setup-literate"

def processArgs (args : List String) : Except String (CliConfig × Command) :=
  let rec loop (config : CliConfig) (command : Option Command) : List String → Except String (CliConfig × Command)
    | "sync" :: more =>
      if let some cmd := command then
        throw s!"Unexpected subcommand 'sync': subcommand is already {cmd.name}"
      else loop config (some .sync) more
    | "setup-literate" :: more =>
      if let some cmd := command then
        throw s!"Unexpected subcommand 'setup-literate': subcommand is already {cmd.name}"
      else loop config (some .setupLiterate) more
    | ["--config"] => throw "Missing configuration file after '--config'"
    | "--config" :: cfg :: more =>
      loop {config with configFile := some cfg} command more
    | "-v"::more | "--verbose"::more =>
      loop { config with verbose := true } command more
    | other :: _ =>
      throw s!"Didn't understand {other}"
    | [] =>
      if let some cmd := command then pure (config, cmd)
      else throw "No subcommand specified"
  loop {} none args


/-- Finds the git repository root by running `git rev-parse --show-toplevel`. -/
private def findGitRoot : IO (Option System.FilePath) := do
  let result ← IO.Process.output {
    cmd := "git"
    args := #["rev-parse", "--show-toplevel"]
  }
  if result.exitCode == 0 then
    return some ⟨result.stdout.trimAscii.copy⟩
  else
    return none

/-- Normalizes line endings for comparison by stripping trailing whitespace from each line. -/
private def normalizeNewlines (s : String) : String :=
  s.split "\n" |>.map (·.trimAsciiEnd) |>.fold (init := "") fun acc s =>
    acc ++ s.copy ++ "\n"

private def handleSetupLiterate : IO UInt32 := do
  -- Find git root
  let some gitRoot ← findGitRoot
    | IO.eprintln "Error: Not inside a git repository."
      return 1

  -- Verify lakefile exists at git root
  let hasLakeLean ← (gitRoot / "lakefile.lean").pathExists
  let hasLakeToml ← (gitRoot / "lakefile.toml").pathExists
  unless hasLakeLean || hasLakeToml do
    IO.eprintln s!"Error: No lakefile.lean or lakefile.toml found at {gitRoot}"
    IO.eprintln ""
    IO.eprintln "The git repository root must contain your Lake project."
    IO.eprintln "Please reorganize your repository or set up deployment manually."
    return 1

  let workflowDir := gitRoot / ".github" / "workflows"
  let workflowFile := workflowDir / "verso-literate-pages.yml"

  -- Check for existing file and back it up if different
  let existingContent ← do
    if ← workflowFile.pathExists then
      some <$> IO.FS.readFile workflowFile
    else
      pure none

  if let some existing := existingContent then
    if normalizeNewlines existing == normalizeNewlines versoLiteratePagesYml then
      IO.println s!"'{workflowFile}' is already up to date."
      return 0
    else
      let bakFile := workflowDir / "verso-literate-pages.yml.bak"
      IO.FS.writeFile bakFile existing
      IO.println s!"Saved existing workflow to '{bakFile}'."

  -- Write the workflow
  IO.FS.createDirAll workflowDir
  IO.FS.writeFile workflowFile versoLiteratePagesYml

  -- Stage the file
  let gitAddResult ← IO.Process.output {
    cmd := "git"
    args := #["add", workflowFile.toString]
  }
  if gitAddResult.exitCode != 0 then
    IO.eprintln s!"warning: git add failed: {gitAddResult.stderr}"

  if existingContent.isSome then
    IO.println s!"Updated and staged '{workflowFile}'."
    IO.println "Check the .bak file to merge any customizations you had."
  else
    IO.println s!"Created and staged '{workflowFile}'."

  IO.println ""
  IO.println "Next steps:"
  IO.println "  1. Go to your repository's Settings → Pages → Source"
  IO.println "     and select 'GitHub Actions'."
  IO.println "  2. Commit and push the staged workflow file."
  IO.println "  3. Ensure lake-manifest.json is committed to your repository."
  return 0

def handle (cliConfig : CliConfig) : Command → IO UInt32
  | .sync => do
    discard <| updateRemotes true cliConfig.configFile cliConfig.logVerbose
    return 0
  | .setupLiterate => handleSetupLiterate


def main (args : List String) : IO UInt32 := do
  match processArgs args with
  | .error e =>
    IO.eprintln e
    return 1
  | .ok (config, cmd) =>
    handle config cmd
