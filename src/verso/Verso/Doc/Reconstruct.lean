/-
Copyright (c) 2023-2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Rob Simmons
-/

module
public import SubVerso.Highlighting
public import Verso.Doc

set_option doc.verso true
set_option pp.rawOnError true

namespace Verso.Doc
open Lean

public structure DocReconstruction where
  highlightDeduplication : SubVerso.Highlighting.Export

/--
The result type of values created by Verso's {lit}`#doc` and {lit}`#docs` commands. A value of type
{name}`DocThunk` represents a partially-serialized document of type {lean}`Part` that can be turned
into a value by invoking the `DocThunk.force` method. The internal structure of a {name}`DocThunk`
should not be relied upon.
-/
public inductive DocThunk (genre : Genre) where
  /--
  A partially-serialized document. If the {name}`replacementMetadata?` is non-{name}`none`, the
  value will replace the outermost {name}`Part.metadata` field of the reconstructed document.
  -/
  | serialized
      (construct : DocReconstruction → Part genre)
      (docReconstructionData : String := "{}")
      (replacementMetadata? : Option (Option genre.PartMetadata))

  /--
  For pathways that build {lean}`Part` values directly, there is no value in, or need for, a
  serialization phase.
  -/
  | value (part : Part genre)

instance : Inhabited (DocThunk genre) where
  default := .value default

/--
Replaces the top-level metadata in a {name}`DocThunk` without forcing the thunk.
-/
public def DocThunk.withMetadata (metadata? : Option genre.PartMetadata)  : DocThunk genre → DocThunk genre
  | .serialized construct docReconstStr _ =>
    .serialized construct docReconstStr (.some metadata?)
  | .value part =>
    .value { part with metadata := metadata? }

/--
A {name}`DocThunk` represents a potentially-not-fully-evaluated {name}`Part`. Calling
{name}`DocThunk.force` forces evaluation of the {name}`DocThunk` to a {name}`Part`.
-/
public def DocThunk.force: DocThunk genre → Part genre
  | .serialized construct highlight metadata? =>
    match Json.parse highlight with
    | .error e => panic! s!"Failed to parse DocThunk's Export data as JSON: {e}"
    | .ok json =>
      let part :=
        if let .ok highlightJson := json.getObjVal? "highlight" then
          match SubVerso.Highlighting.Export.fromJson? highlightJson with
          | .error e => panic! s!"Failed to deserialize Export data from parsed JSON: {e}"
          | .ok table => construct ⟨table⟩
        else construct ⟨{}⟩
      match metadata? with
      | .none => part
      | .some replacement => { part with metadata := replacement }
  | .value part => part

@[deprecated DocThunk (since := "2025-12-28")]
public def VersoDoc : Genre → Type := DocThunk

@[deprecated DocThunk.force (since := "2025-12-28")]
public def VersoDoc.force : DocThunk genre → Part genre := DocThunk.force

@[deprecated DocThunk.force (since := "2025-12-28")]
public def VersoDoc.toPart : DocThunk genre → Part genre := DocThunk.force

@[deprecated DocThunk.force (since := "2025-12-28")]
public def DocThunk.toPart : DocThunk genre → Part genre := DocThunk.force
