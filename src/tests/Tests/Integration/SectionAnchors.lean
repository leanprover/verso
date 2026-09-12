/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Emilio J. Gallego Arias
-/
module
public import Verso
public import VersoManual
public meta import Verso
public meta import VersoManual

namespace Verso.Integration.SectionAnchors

open Lean Verso Genre Manual

#docs (Manual) doc "Section Anchors" :=
:::::::
%%%
tag := "manual-root"
%%%

See {ref "tagged-chapter"}[the chapter] and {ref "nested-section"}[its section].

# Tagged Chapter
%%%
tag := "tagged-chapter"
%%%

Return to {ref "manual-root"}[the title page].

## Nested Section
%%%
tag := "nested-section"
%%%

This section stays on its chapter's page.

# Automatic Chapter

This chapter gets an automatically generated tag.
:::::::

/-- Every exported section target must occur exactly once in the page named by its cross-reference. -/
private def checkAnchors : IO Unit := IO.FS.withTempDir fun destination => do
  let cfg : RenderConfig := { destination, htmlDepth := 1, features := {} }
  let exitCode ← withLogger fun logger => do
    let (part, state) ← (traverseHtmlMulti cfg doc.toPart).run extension_impls% |>.run logger
    emitXrefsJson (destination / "html-multi") state
    (emitHtmlMulti cfg part state).run extension_impls% |>.run logger
  unless exitCode == 0 do
    throw <| IO.userError "Section anchor document generation logged errors"
  let site := destination / "html-multi"
  let xrefs ← IO.ofExcept <| Json.parse (← IO.FS.readFile (site / "xref.json"))
  let sections ← IO.ofExcept <| xrefs.getObjVal? "Verso.Genre.Manual.section"
  let contents ← IO.ofExcept <| sections.getObjVal? "contents"
  let entries ← IO.ofExcept contents.getObj?
  unless entries.size == 4 do
    throw <| IO.userError s!"Expected four section targets, got {entries.size}"
  for tag in ["manual-root", "tagged-chapter", "nested-section"] do
    discard <| IO.ofExcept <| contents.getObjVal? tag
  for (tag, targets) in entries.toArray do
    let targets ← IO.ofExcept targets.getArr?
    unless targets.size == 1 do
      throw <| IO.userError s!"Expected one destination for {tag}"
    let target := targets[0]!
    let address ← IO.ofExcept <| target.getObjValAs? String "address"
    let id ← IO.ofExcept <| target.getObjValAs? String "id"
    let page := (address.splitOn "/").filter (!·.isEmpty) |>.foldl (· / ·) site
    let html ← IO.FS.readFile (page / "index.html")
    let count := (html.splitOn s!" id=\"{id}\"").length - 1
    unless count == 1 do
      throw <| IO.userError s!"{tag}: expected exactly one id=\"{id}\" in {address}, got {count}"

/-- info: All section cross-references have unique HTML targets. -/
#guard_msgs in
#eval do
  checkAnchors
  IO.println "All section cross-references have unique HTML targets."

end Verso.Integration.SectionAnchors
