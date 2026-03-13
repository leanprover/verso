/-
Copyright (c) 2025-2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import Lake.Toml

/-! # Doc Source Configuration

Parsing and code generation for `doc-sources.toml`, which declares which packages' documentation
should be built by the `docSource` Lake package facet.

The `[[require]]` entries use the same field names as `lakefile.toml`.
-/

namespace Verso.Genre.Manual.DocSource

open Lake.Toml

/-- Dependency entry from `doc-sources.toml`, mirroring `[[require]]` in `lakefile.toml`. -/
structure Require where
  /-- The package name (must match the name declared in its lakefile). -/
  name : String
  /-- Git repository URL. -/
  git : Option String := none
  /-- Git revision (branch, tag, or commit hash). -/
  rev : Option String := none
  /-- Local filesystem path (relative to the project root). -/
  path : Option System.FilePath := none
  /-- Subdirectory within the repository. -/
  subDir : Option String := none
deriving Repr, BEq, Inhabited

/-- Parsed contents of a `doc-sources.toml` file. -/
structure Config where
  /-- Package dependencies whose documentation should be built. -/
  require : Array Require := #[]
  /--
  Which library targets to document. Defaults to default library targets of all required
  packages.
  -/
  libraries : Array String := #[]
  /-- Shell commands to run in the managed workspace before building (e.g., `lake exe cache get`). -/
  setup : Array String := #[]
deriving Repr, BEq, Inhabited

/-- Extracts a `String` from a TOML `Value`, or `none` if it's not a string. -/
private def tomlString? : Value → Option String
  | .string _ s => some s
  | _ => none

/--
Extracts an `Array String` from a TOML array of strings. Non-string elements are silently
skipped.
-/
private def tomlStringArray? : Value → Option (Array String)
  | .array _ vs => some <| vs.filterMap tomlString?
  | _ => none

/-- Parses a single `[[require]]` entry from a TOML table value. -/
def Require.ofToml (v : Value) : Except String Require := do
  match v with
  | .table' _ t =>
    let name ← match t.find? `name with
      | some v => match tomlString? v with
        | some s => pure s
        | none => throw "[[require]] entry 'name' field must be a string"
      | none => throw "[[require]] entry is missing the required 'name' field"
    let git := t.find? `git >>= tomlString?
    let rev := t.find? `rev >>= tomlString?
    let path := t.find? `path >>= tomlString? |>.map System.FilePath.mk
    let subDir := t.find? `subDir >>= tomlString?
    pure { name, git, rev, path, subDir }
  | _ => throw "[[require]] entry must be a table"

/-- Parses a `Config` from a TOML `Table`. -/
def Config.ofToml (table : Table) : Except String Config := do
  let require ← match table.find? `require with
    | some (.array _ vs) => vs.mapM Require.ofToml
    | some _ => throw "'require' must be an array of tables ([[require]])"
    | none => pure #[]
  let libraries := match table.find? `libraries with
    | some v => tomlStringArray? v |>.getD #[]
    | none => #[]
  let setup := match table.find? `setup with
    | some v => tomlStringArray? v |>.getD #[]
    | none => #[]
  pure { require, libraries, setup }

/-- Loads and parses a `doc-sources.toml` file. -/
def Config.load (filePath : System.FilePath) : IO Config := do
  let input ← IO.FS.readFile filePath
  let ictx := Lean.Parser.mkInputContext input filePath.toString
  match (← Lake.Toml.loadToml ictx |>.toBaseIO) with
  | .ok table =>
    match Config.ofToml table with
    | .ok config => pure config
    | .error e => throw <| .userError s!"Error parsing {filePath}: {e}"
  | .error msgs =>
    let msgStrs ← msgs.toList.mapM fun msg => msg.data.toString
    throw <| .userError s!"Error parsing {filePath}:\n{"\n".intercalate msgStrs}"

/--
Splits a command string into an executable name and arguments, respecting single and double
quotes. Backslash escapes the next character inside double quotes. Unmatched quotes are
treated as if closed at the end of the string.
-/
def splitCommand (cmd : String) : Option (String × Array String) := do
  let mut args : Array String := #[]
  let mut cur : String := ""
  -- Track whether the current word contains any content (including empty quotes)
  let mut inWord := false
  let mut i := 0
  let chars := cmd.toList
  while i < chars.length do
    let c := chars[i]!
    if c == '\'' then
      -- Single-quoted: everything up to closing ' is literal
      inWord := true
      i := i + 1
      while i < chars.length && chars[i]! != '\'' do
        cur := cur.push chars[i]!
        i := i + 1
      -- skip closing quote (or end of string)
      i := i + 1
    else if c == '"' then
      -- Double-quoted: backslash escapes the next character
      inWord := true
      i := i + 1
      while i < chars.length && chars[i]! != '"' do
        if chars[i]! == '\\' && i + 1 < chars.length then
          i := i + 1
          cur := cur.push chars[i]!
        else
          cur := cur.push chars[i]!
        i := i + 1
      -- skip closing quote (or end of string)
      i := i + 1
    else if c == ' ' || c == '\t' then
      if inWord then
        args := args.push cur
        cur := ""
        inWord := false
      i := i + 1
    else
      cur := cur.push c
      inWord := true
      i := i + 1
  if inWord then
    args := args.push cur
  match args.toList with
  | [] => none
  | exe :: rest => some (exe, rest.toArray)

/-- Generates a `require` declaration in lakefile.lean syntax for a single dependency. -/
def Require.toLakefileEntry (r : Require) (projectDir : System.FilePath) : String :=
  let name := s!"require «{r.name}»"
  match r.git, r.path with
  | some url, _ =>
    -- Resolve relative git URLs against the project root, since the generated
    -- lakefile lives in the managed workspace, not the project root.
    let absUrl := if System.FilePath.isAbsolute ⟨url⟩ || (url.splitOn "://").length > 1 then url
                  else (projectDir / url).toString
    let revPart := r.rev.map (s!" @ \"{·}\"") |>.getD ""
    let subDirPart := r.subDir.map (s!" / \"{·}\"") |>.getD ""
    s!"{name} from git\n  \"{absUrl}\"{revPart}{subDirPart}\n"
  | _, some path =>
    -- Resolve relative paths against the project root to produce absolute paths,
    -- since the generated lakefile lives in the managed workspace, not the project root.
    let absPath := if path.isAbsolute then path else projectDir / path
    s!"{name} from \"{absPath}\"\n"
  | none, none =>
    -- No source specified — Lake will look it up in the registry
    s!"{name}\n"

/--
Generates a complete `lakefile.lean` for the managed doc-gen workspace.

`config` is the parsed `doc-sources.toml` (or `none` for a core-only build).
`docgen4Dir` is the absolute path to the doc-gen4 package checkout.
`projectDir` is the absolute path to the user's project root.
-/
def generateLakefile (config : Option Config)
    (docgen4Dir : System.FilePath) (projectDir : System.FilePath) : String :=
  let header := "import Lake\nopen Lake DSL\n\npackage «docgen-workspace»\n\n"
  let docgenReq := s!"require «doc-gen4» from git\n  \"{docgen4Dir}\"\n\n"
  let userReqs := match config with
    | some cfg => cfg.require.map (·.toLakefileEntry projectDir) |>.toList |> String.join
    | none => ""
  header ++ docgenReq ++ userReqs

end Verso.Genre.Manual.DocSource
