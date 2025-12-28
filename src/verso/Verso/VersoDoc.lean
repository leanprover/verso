/-
Copyright (c) 2023-2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Rob Simmons
-/
module
public import Verso.Doc
public import SubVerso.Highlighting
import Verso.Finished

set_option doc.verso true
set_option pp.rawOnError true

namespace Verso.Doc
open Lean

/--
Deserializing a partially-serialized document syntax is done with access to a structure that fills
in the parts of the document structure that weren't serialized.
-/
public structure DeserializeAux (genre : Genre) : Type where
  inlines : Array (Inline genre)
  blocks : Array (Block genre)
  partMetadata : Array genre.PartMetadata
  /-- Sorted by {name}`Name.quickLt` -/
  docs : Array (Name × Part genre)
deriving Inhabited


/--
Transform a previously-serialized {name (full := Elab.FinishedPart)}`FinishedPart` into a
{name}`Part`.
-/
public partial def Part.deserialize : Json → ReaderM (DeserializeAux genre) (Part genre)
  | name@(.str _) => do
    let .ok id := FromJson.fromJson? name
      | panic! "Failed to deserialize as id `{name}`"
    let .some (_, part) := (← read).docs.binSearch (id, default) (fun (a, _) (b, _) => Name.quickLt a b)
      | panic! "Failed to find id `{id}`"
    return part
  | .obj o => do
    let aux ← read
    let titleArr := match o.get! "title" |>.getArr? with
      | .ok arr => arr
      | .error e => panic! s!"ill-formed JSON part serialization (title) {e}"
    let title := titleArr.map (match ·.getNat? with
      | .ok n => match aux.inlines[n]? with
        | .some t => t
        | .none => panic! s!"out of bound inline: {n} vs {aux.inlines.size}"
      | .error e => panic! s!"Ill-formed JSON part serialization (title) {e}")
    let titleString := match o.get! "titleString" |>.getStr? with
      | .ok str => str
      | .error e => panic! panic! s!"Ill-formed JSON part serialization (titleString) {e}"
    let metadata := match o.get! "metadata" with
      | .null => .none
      | .arr #[.num (n : Nat)] =>
        match (aux.partMetadata[n]?) with
          | .some s => .some s
          | .none => panic! s!"Ill-formed JSON part serialization (metadata) {n}"
      | json => panic! s!"Ill-formed JSON part serialization (metadata) {json}"
    let contentArr := match o.get! "content" |>.getArr? with
      | .ok arr => arr
      | .error e => panic! s!"Ill-formed JSON part serialization (content) {e}"
    let content := contentArr.map (match ·.getNat? with
      | .ok n => match aux.blocks[n]? with
        | .some t => t
        | .none => panic! s!"out of bound block: {n} vs {aux.blocks.size}"
      | .error e => panic! s!"Ill-formed JSON part serialization (content) {e}")
    let subPartsArr := match o.get! "subParts" |>.getArr? with
      | .ok arr => arr
      | .error e => panic! s!"Ill-formed JSON part serialization (subParts) {e}"
    let subParts ← subPartsArr.mapM deserialize
    return Part.mk title titleString metadata content subParts
  | json => panic s!"Ill-formed JSON part serialization {json}"

public structure DocReconstruction where
  highlightDeduplication : SubVerso.Highlighting.Export

/--
The result type of values created by Verso's {lit}`#doc` and {lit}`#docs` commands. A value of type
{lean}`DocThunk` represents a partially-serialized value of type {lean}`Part` that can be turned
into a value by invoking the `DocThunk.force` method. The actual structure of a {lean}`DocThunk`
should not be relied on.
-/
public inductive DocThunk (genre : Genre) where
  | serialized
      (aux : DocReconstruction → DeserializeAux genre)
      (doc : String)
      (docReconstructionData : String := "{}")
      (replacementMetadata? : Option (Option genre.PartMetadata) := .none)
  | value (part : Part genre)

instance : Inhabited (DocThunk genre) where
  default := DocThunk.value default

/--
Replace the top-level metadata in a {name}`DocThunk` without forcing the thunk.
-/
public def DocThunk.withMetadata (metadata? : Option genre.PartMetadata) : DocThunk genre → DocThunk genre
  | .serialized aux doc docReconstStr _replacementMetadata? =>
    .serialized aux doc docReconstStr (.some metadata?)
  | .value part =>
    .value { part with metadata := metadata? }

/--
A {lean}`DocThunk` represents a potentially-not-fully-evaluated {lean}`Part`. Calling
{lean}`DocThunk.force` forces evaluation of the {lean}`DocThunk` to a {lean}`Part`.
-/
public def DocThunk.force: DocThunk genre → Part genre
  | .serialized auxFn docStr highlight replacementMetadata? =>
    match (Json.parse highlight, Json.parse docStr) with
    | (.error e, _) => panic! s!"Failed to parse VersoDoc's Export data as JSON: {e}"
    | (_, .error e) => panic! s!"Failed to parse doc data as JSON: {e}"
    | (.ok reconJson, .ok docJson) =>
      if let .ok highlightJson := reconJson.getObjVal? "highlight" then
        match SubVerso.Highlighting.Export.fromJson? highlightJson with
        | .error e => panic! s!"Failed to deserialize Export data from parsed JSON: {e}"
        | .ok table =>
          let aux := auxFn ⟨table⟩
          let part := Id.run <| ReaderT.run (Part.deserialize docJson) aux
          match replacementMetadata? with
          | .none => part
          | .some replacementMetadata => { part with metadata := replacementMetadata }
      else
        Id.run <| ReaderT.run (Part.deserialize docJson) (auxFn ⟨{}⟩)
  | .value part => part
