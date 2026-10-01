/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module

public import UsersGuide.Releases.Entry

open Verso.Genre Manual InlineLean UsersGuide.Releases

release_note
  version := ⟨4, 35, 0⟩
  breaking := true
  tag := "link-footnote-resolution"
  prs := [1014]

#doc (Manual) "Link and Footnote Label Resolution" =>

Both footnotes and links with labels instead of URLs (e.g. `see [link][somewhere]`) are now internally resolved through Verso's document reconstruction data instead of by generating class instances for each label.
Go-to-definition and document highlights for labels now work before elaboration is complete.
Footnote contents can now use labels that are defined later.
This is a breaking change for code that defines or looks up labels: the type classes `HasLink` and `HasNote` are gone, {name}`Verso.Doc.DocReconstruction` takes the genre as a parameter, and several functions and fields are renamed or removed.

This fixes issues with Lean files that contain multiple documents and improves error messages.
Furthermore, more roles now work inside footnotes.

There are {ref "link-footnote-resolution"}[breaking changes]:

* {name}`Verso.Doc.DocReconstruction` takes the genre as a parameter.
* {name}`Verso.Doc.Elab.DocRefInfo` describes a single definition or use.
* {name}`Verso.Doc.Elab.DocDef` has the required fields `fileName` and `position`.
* Removed: the type classes `HasLink` and `HasNote`, `DocRefInfo.syntax`, `Verso.Doc.Elab.internalRefs` and `Verso.Doc.Concrete.saveRefs`.
* Renamed to `labelStx`: the field `defSite` of {name}`Verso.Doc.Elab.DocDef`, and the `refName` parameter of {name}`Verso.Doc.Elab.PartElabM.addLinkDef`, {name}`Verso.Doc.Elab.DocElabM.addLinkRef`, {name}`Verso.Doc.Elab.PartElabM.addFootnoteDef` and {name}`Verso.Doc.Elab.DocElabM.addFootnoteRef`.
* {name}`Verso.Doc.Elab.DocElabM.addLinkRef` and {name}`Verso.Doc.Elab.DocElabM.addFootnoteRef` report an error for text elaborated outside a document, such as the title of a literate module in a manual. Before, they failed with an instance error.
