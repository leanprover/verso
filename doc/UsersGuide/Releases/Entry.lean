/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module

public import VersoManual

set_option doc.verso true

namespace UsersGuide.Releases

open Verso Doc Genre
open Lean (ToJson FromJson)

/--
A Verso version number.

Verso's versions track Lean's: every {lit}`vX` Git tag of Verso has {lit}`leanprover/lean4:vX` in its
{lit}`lean-toolchain` file.
-/
public structure Version where
  major : Nat
  minor : Nat
  patch : Nat
deriving BEq, Hashable, Repr, DecidableEq, Ord, ToJson, FromJson

public instance : ToString Version where
  toString v := s!"{v.major}.{v.minor}.{v.patch}"

/--
The release that a {lit}`lean-toolchain` file names, when it names one.

A release candidate, nightly, or PR snapshot names no release. The version number reported by such a
toolchain is that of the _upcoming_ release.
-/
public meta def stableToolchainVersion? (toolchain : String) : Option Version := do
  let named : String := (toolchain.trimAscii.copy.splitOn ":").getLast!
  let name := if named.startsWith "v" then (named.drop 1).copy else named
  match (name.splitOn "." : List String) with
  | [major, minor, patch] =>
    pure ⟨← major.toNat?, ← minor.toNat?, ← patch.toNat?⟩
  | _ => Option.none

/--
The version under development with the given {lit}`lean-toolchain` and Lean version.

A toolchain that names a release means that version of Verso has been tagged, so the next minor
version is under development. Every other toolchain is preparing the version it reports, which is
where the release candidates and the nightlies land.
-/
public meta def Version.inDevelopmentFor (toolchain : String) (major minor patch : Nat) : Version :=
  match stableToolchainVersion? toolchain with
  | some released => ⟨released.major, released.minor + 1, 0⟩
  | Option.none => ⟨major, minor, patch⟩

/-- Finds the {lit}`lean-toolchain` that governs a directory. -/
public meta partial def findToolchainFile (dir : System.FilePath) : IO System.FilePath := do
  let candidate := dir / "lean-toolchain"
  if ← candidate.pathExists then return candidate
  match dir.parent with
  | some parent => findToolchainFile parent
  | Option.none =>
    throw <| IO.userError "Couldn't find a `lean-toolchain` file above this directory."

/-- The version of Verso that this checkout is developing towards. -/
public meta def Version.inDevelopment : IO Version := do
  let toolchain ← IO.FS.readFile (← findToolchainFile (← IO.currentDir))
  return Version.inDevelopmentFor toolchain
    Lean.version.major Lean.version.minor Lean.version.patch

#guard Version.inDevelopmentFor "leanprover/lean4:v4.33.0\n" 4 33 0 == ⟨4, 34, 0⟩
#guard Version.inDevelopmentFor "leanprover/lean4:v4.33.0-rc1" 4 33 0 == ⟨4, 33, 0⟩
#guard Version.inDevelopmentFor "leanprover/lean4:v4.32.1" 4 32 1 == ⟨4, 33, 0⟩
-- The leading `v` is optional, and a bare version names a release too.
#guard Version.inDevelopmentFor "leanprover/lean4:4.33.0" 4 33 0 == ⟨4, 34, 0⟩
#guard Version.inDevelopmentFor "4.33.0\n" 4 33 0 == ⟨4, 34, 0⟩
#guard Version.inDevelopmentFor "leanprover/lean4:4.33.0-rc1" 4 33 0 == ⟨4, 33, 0⟩
#guard Version.inDevelopmentFor "leanprover/lean4:nightly-2026-08-09" 4 34 0 == ⟨4, 34, 0⟩
#guard Version.inDevelopmentFor "leanprover/lean4-nightly:nightly-2026-08-09" 4 34 0 == ⟨4, 34, 0⟩
-- A Lean PR build names no release either, so an adaptation branch gets the version that the
-- build it is adapting to reports.
#guard Version.inDevelopmentFor "leanprover/lean4-pr-releases:pr-release-1234" 4 34 0 == ⟨4, 34, 0⟩
#guard Version.inDevelopmentFor "leanprover/lean4:pr-release-1234" 4 34 0 == ⟨4, 34, 0⟩
-- A locally linked toolchain names no release either.
#guard Version.inDevelopmentFor "lean4" 4 34 0 == ⟨4, 34, 0⟩

/--
Metadata that allows release note entries to be sorted correctly.

The entry's prose is an ordinary {name}`Manual` document. These metadata are declared alongside it
by the {lit}`release_note` command.
-/
public structure EntryMetadata where
  /-- The version of Verso that the entry describes. -/
  version : Version
  /-- Whether the entry describes a breaking change. -/
  breaking : Bool
  /-- The entry's permanent name, used for cross-references and shared links. -/
  tag : String
  /-- The pull request(s) that made the change. -/
  prs : List Nat
deriving BEq, Hashable, Repr, ToJson, FromJson

/-- The name under which the module {name}`mod` declares its {name}`EntryMetadata`. -/
public meta def entryMetadataName (mod : Lean.Name) : Lean.Name := mod ++ `releaseNoteMetadata

open Lean.Parser Term in
public meta def releaseNoteFields :=
  structInstFields (sepByIndent Term.structInstField "; " (allowTrailingSep := true))

/--
Declares what release note entry this module is. Every module under
{lit}`UsersGuide.Releases.Entries` states this once, alongside its {lit}`#doc`.

```
release_note
  version := ⟨4, 34, 0⟩
  breaking := false
  tag := "feat-serve"
  prs := [876]
```
-/
syntax "release_note" ppIndent(releaseNoteFields) : command

open Lean Elab Command in
elab_rules : command
  | `(release_note $fields;*) => do
    let name := mkIdent (`_root_ ++ entryMetadataName (← getEnv).mainModule)
    elabCommand <| ← `(/-- What release note entry this module is. -/
      public def $name : EntryMetadata where $fields;*)

end UsersGuide.Releases
