/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import UsersGuide.Releases

set_option doc.verso true

/-!
Checks the manual's release note entries.

Run with {lit}`lake lean scripts/release_notes.lean`. The checks happen while this file is
elaborated, so a failure is a Lean error and {lit}`lean` exits nonzero.
-/

open Lean UsersGuide.Releases

/-- The directory that holds release note entries. -/
def entriesDir : System.FilePath := "doc" / "UsersGuide" / "Releases" / "Entries"

/--
The file that defines an entry module.

Entry modules may sit in subdirectories, so every component below {name}`entriesNamespace` becomes
a path component.
-/
def entryFile (mod : Name) : System.FilePath :=
  let components := mod.components.drop entriesNamespace.components.length
  let path := components.foldl (init := entriesDir) fun dir c => dir / c.toString
  path.addExtension "lean"

/-- The module that a release note entry file defines. -/
def entryModule (file : System.FilePath) : Name :=
  let rel : String := file.toString.drop (entriesDir.toString.length + 1) |>.copy
  let rel : String := if rel.endsWith ".lean" then (rel.dropEnd 5).copy else rel
  (rel.splitOn "/").foldl (init := entriesNamespace) fun mod c => mod ++ c.toName

/-- Every release note entry file on disk, including those in subdirectories. -/
partial def entryFiles (dir : System.FilePath := entriesDir) : IO (Array System.FilePath) := do
  let mut files := #[]
  for entry in ← dir.readDir do
    if ← entry.path.isDir then
      files := files ++ (← entryFiles entry.path)
    else if entry.path.extension == some "lean" then
      files := files.push entry.path
  return files.qsort (·.toString < ·.toString)

/--
The commit that the current branch is being compared against.

{lit}`RELEASE_NOTES_BASE` names it directly. A checkout that holds only {lit}`HEAD` and its
parents is enough to satisfy this path, which is how CI runs.

Otherwise the base is the merge base with {lit}`origin/main`, so that running the script in a
local clone takes no setup. Reaching the common ancestor needs history back to it.
-/
def baseCommit : IO String := do
  if let some base ← IO.getEnv "RELEASE_NOTES_BASE" then
    if !base.trimAscii.isEmpty then
      return base.trimAscii.copy
  let out ← IO.Process.output {
    cmd := "git", args := #["merge-base", "origin/main", "HEAD"]
  }
  if out.exitCode != 0 then
    throw <| IO.userError <|
      "Couldn't determine the base commit with `git merge-base origin/main HEAD`. " ++
      s!"Set RELEASE_NOTES_BASE to a commit to compare against.\n{out.stderr}"
  return out.stdout.trimAscii.copy

private def git (args : Array String) (what : String) : IO String := do
  let out ← IO.Process.output { cmd := "git", args }
  if out.exitCode != 0 then
    throw <| IO.userError s!"Couldn't {what}.\n{out.stderr}"
  return out.stdout

/--
The release note entry files this branch adds or changes since the base commit, paired with
whether the file is new.
-/
def changedEntryFiles (base : String) : IO (Array (System.FilePath × Bool)) := do
  let out ← git
    #["diff", "--diff-filter=AMR", "--name-status", base, "HEAD", "--", entriesDir.toString]
    s!"list the entry files changed since {base}"
  return out.splitOn "\n" |>.filterMap (fun line =>
      match line.trimAscii.copy.splitOn "\t" with
      | status :: rest =>
        -- A rename reports the old path and the new one; the new one is what exists now.
        match rest.getLast? with
        | some path =>
          if path.isEmpty then none else some (System.FilePath.mk path, status.startsWith "A")
        | none => none
      | [] => none)
    |>.toArray

/-- A list of pull request numbers as it is written in an entry. -/
def prsText (prs : List Nat) : String :=
  "[" ++ String.intercalate ", " (prs.map toString) ++ "]"

/--
The reason a `No-Changelog:` line gives, if the text has one. The line may sit anywhere in the
text.
-/
def noChangelogReason (text : String) : Option String :=
  text.splitOn "\n" |>.findSome? fun line =>
    let line : String := line.trimAscii.copy
    if line.startsWith "No-Changelog:" then
      some ((line.drop "No-Changelog:".length).trimAscii.copy)
    else none

/--
The reason given for waiving the rules about an entry's version and pull requests, if one is
given.

A pull request is squashed into a commit whose message is its description, so the description is
what is read while the pull request is open, and the commit messages once it has landed.
-/
def versionOverride (base : String) (pr : Option Nat) : IO (Option String) := do
  if pr.isSome then
    return noChangelogReason <| (← IO.getEnv "RELEASE_NOTES_DESCRIPTION").getD ""
  else
    return noChangelogReason <|
      ← git #["log", "--format=%B", s!"{base}..HEAD"] "read the commit messages"

run_cmd Elab.Command.liftTermElabM do
  let mut problems : Array MessageData := #[]

  let declared := entries.map fun (mod, metadata, _) => (entryFile mod, mod, metadata)

  -- Every entry file on disk must be imported by `UsersGuide.Releases.Entries`, and thus be
  -- discovered by `release_notes_chapter`.
  let known := declared.map (·.1.toString)
  for file in ← entryFiles do
    unless known.contains file.toString do
      problems := problems.push m!"\
        {file} is not part of the release notes.\n\
        Add `public import {entryModule file}` to \
        doc/UsersGuide/Releases/Entries.lean."

  -- Every entry this branch adds or changes describes the version under development, and a new
  -- one names the pull request that adds it. A change that belongs in no release note takes the
  -- `no-changelog` label instead.
  let inDevelopment ← Version.inDevelopment
  let pr ← (← IO.getEnv "RELEASE_NOTES_PR").bindM fun s => pure s.trimAscii.toNat?
  if pr.isNone then
    logInfo "RELEASE_NOTES_PR names no pull request, as on a merge queue or a push, so entries \
      are not checked for naming one. Their versions are checked as usual."
  let base ← baseCommit
  let override? ← versionOverride base pr
  if let some reason := override? then
    logInfo m!"Waiving the rules about an entry's version and pull requests: {reason}"
  for (file, isNew) in ← changedEntryFiles base do
    let some (_, _, metadata) := declared.find? (·.1.toString == file.toString)
      | continue
    if let some pr := pr then
      if isNew && override?.isNone then
        unless metadata.prs.contains pr do
          let named :=
            match metadata.prs with
            | [] => m!"names no pull requests"
            | [one] => m!"names only pull request #{one}"
            | many => m!"names pull requests {prsText many}"
          problems := problems.push m!"\
            {file} {named}, leaving out this one, #{pr}.\n\
            Change its metadata to `prs := {prsText (metadata.prs ++ [pr])}`, or say why the change needs \
            no release note with a `No-Changelog:` line in the pull request description."
    unless override?.isSome || metadata.version == inDevelopment do
      problems := problems.push m!"\
        {file} describes Verso {metadata.version}, but Verso {inDevelopment} is under development.\n\
        Change its metadata to `version := ⟨{inDevelopment.major}, {inDevelopment.minor}, \
        {inDevelopment.patch}⟩`, or say why the change needs no release note with a \
        `No-Changelog:` line in the pull request description."

  unless problems.isEmpty do
    throwError MessageData.joinSep problems.toList "\n\n"
