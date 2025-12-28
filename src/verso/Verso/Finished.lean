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

public inductive FinishedPart where
  | mk (titleSyntax : Syntax)
       (expandedTitle : Array Term)
       (titlePreview : String)
       (metadata : Option Term)
       (blocks : Array Term)
       (subParts : Array FinishedPart)
       (endPos : String.Pos.Raw)
    /-- A name representing an external module document -/
  | included (name : Ident)
deriving Repr, BEq

/--
Partially-serializable document structures "bottom out" at syntax nodes, which
we don't directly serialize. Instead, when we are serializing a
partially-serializable data structure and reach a syntax node, we store the
syntax node in a {name}`SerializableAux` table and serialize an index into the table.
-/
public structure SerializableAux where
  /-- Syntax denoting values of type {lean}`Verso.Doc.Inline genre` for some implicit {name}`genre`. -/
  inlines : Array Term := #[]
  /-- Syntax denoting values of type {lean}`Verso.Doc.Block genre` for some implicit {name}`genre`. -/
  blocks : Array Term := #[]
  /-- Syntax denoting values of type {lean}`genre.PartMetadata` for some implicit {name}`genre`. -/
  partMetadata : Array Term := #[]
  /-- Other modules -/
  docs : NameSet := {}


public partial def FinishedPart.serialize [Monad m] [MonadRef m] [MonadQuotation m] : FinishedPart → StateT SerializableAux m Lean.Json
  | .mk _titleSyntax title titlePreview metadata blocks subParts _endPos => do
    let aux ← get

    let titleJson := title.mapIdx (fun n _ => .num <| n + aux.inlines.size)

    let metadataJson ← match metadata with
      | .none => pure Json.null
      | .some s =>
        let n := aux.partMetadata.size
        set { aux with partMetadata := aux.partMetadata.push s }
        pure <| Json.arr #[.num n]

    let contentJson := blocks.mapIdx (fun n _ => .num <| n + aux.blocks.size)

    set ({ aux with
      inlines := aux.inlines ++ title
      blocks := aux.blocks ++ blocks })

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
