/-
Copyright (c) 2023-2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Rob Simmons
-/
module
import Verso.Doc

public import Lean.Data.Json.Basic
public import Lean.Data.NameMap.Basic
import Lean.Log

set_option doc.verso true
set_option pp.rawOnError true

namespace Verso.Doc.Elab
open Lean

/--
When elaborating document structures, we are building an internal
representation ({lit}`IR`) relative to an unspecified {name}`Genre` that must
be consistent for the entire elaborated structure once that structure is
serialized and deserialized.
-/
opaque genre : Genre

/--
Partially-serializable document structures can potentially "bottom out" as non-serializable data,
represented as a {name}`Term` that, if elaborated and evaluated, represents part of a document.

When serializing a partially-serializable document, these non-serializable segments are stored in
a {name}`SerializableAux` data structure, and the serializable data contains an index into this
data structure.

To de-serialize the document, the terms in the data structure must be elaborated and evaluated to
document data of the appropriate genre.
-/
public structure SerializableAux where
  /-- Syntax denoting values of type {lean}`Verso.Doc.Inline genre` for some implicit {name}`genre`. -/
  inlines : Array Term := #[]
  /-- Syntax denoting values of type {lean}`Verso.Doc.Block genre` for some implicit {name}`genre`. -/
  blocks : Array Term := #[]
  /-- Syntax denoting values of type {lean}`genre.PartMetadata` for some implicit {name}`genre`. -/
  partMetadata : Array Term := #[]
  /-- Other modules referenced in this document by name -/
  docs : NameSet := {}

/--
A {name}`FinishedPart` is the result of elaborating a document's part structure.
-/
public inductive FinishedPart where
  | mk (titleSyntax : Syntax)
       (expandedTitle : Array Term)
       (titlePreview : String)
       (metadata : Option Term)
       (blocks : Array Term)
       (subParts : Array FinishedPart)
       (endPos : String.Pos.Raw)
    /-- A name representing a Part-structured document in another module -/
  | included (name : Ident)
deriving Repr, BEq

/--
Transform a {name}`FinishedPart` into {name}`Json`, extracting any non-serializable data in the
{name}`SerializableAux` data structure.
-/
public partial def FinishedPart.serialize [Monad m] [MonadRef m] [MonadQuotation m] : FinishedPart → StateT SerializableAux m Json
  | .mk _titleSyntax title titlePreview metadata blocks subParts _endPos => do
    let aux ← get
    let titleJson := title.mapIdx (fun n _ => .num <| n + aux.inlines.size)
    let contentJson := blocks.mapIdx (fun n _ => .num <| n + aux.blocks.size)
    set ({ aux with
      inlines := aux.inlines ++ title
      blocks := aux.blocks ++ blocks })

    let aux ← get
    let metadataJson ← match metadata with
      | .none => pure Json.null
      | .some s =>
        let n := aux.partMetadata.size
        set { aux with partMetadata := aux.partMetadata.push s }
        pure <| Json.arr #[.num n]

    let subPartsJson ← subParts.mapM serialize

    return .mkObj [
      ("title", .arr titleJson),
      ("titleString", .str titlePreview),
      ("metadata", metadataJson),
      ("content", .arr contentJson),
      ("subParts", .arr subPartsJson),
    ]

  | .included name => do
    modify (fun aux => { aux with docs := aux.docs.insert name.getId })
    -- NB: deserialization depends on the implementation-defined behavior
    -- that this will be a string
    return ToJson.toJson name.getId
