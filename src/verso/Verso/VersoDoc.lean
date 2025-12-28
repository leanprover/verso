module
public import Verso.Doc
public import SubVerso.Highlighting

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

public structure DocReconstruction where
  highlightDeduplication : SubVerso.Highlighting.Export

/--
The result type of values created by Verso's {lit}`#doc` and {lit}`#docs` commands. A value of type
{lean}`VersoDoc` represents a not-fully-evaluated document of type {lean}`Part` that can be turned
into a value by invoking the `VersoDoc.toPart` method. The actual structure of a {lean}`VersoDoc`
should not be relied on.
-/
public inductive VersoDoc (genre : Genre) where
  | serialized
      (aux : DocReconstruction → DeserializeAux genre)
      (doc : String)
      (docReconstructionData : String := "{}")
      (replacementMetadata? : Option (Option genre.PartMetadata) := .none)
  | literal (part : Part genre)

instance : Inhabited (VersoDoc genre) where
  default := VersoDoc.serialized (fun _ => Inhabited.default) "invalid" "{}" .none

/--
Replace the top-level metadata in a VersoDoc.
-/
public def VersoDoc.withMetadata (metadata? : Option genre.PartMetadata) : VersoDoc genre → VersoDoc genre
  | .serialized aux doc docReconstStr _replacementMetadata? =>
    .serialized aux doc docReconstStr (.some metadata?)
  | .literal part =>
    .literal { part with metadata := metadata? }

def _root_.Lean.Json.getArr! (json : Json) : Array Json :=
  match json.getArr? with
    | .ok arr => arr
    | .error e => panic s!"getArr! {e}"

def _root_.Lean.Json.getStr! (json : Json) : String :=
  match json.getStr? with
    | .ok arr => arr
    | .error e => panic s!"getStr! {e}"

public partial def Part.deserialize : Json → ReaderM (DeserializeAux genre) (Part genre)
  | name@(.str _) => do
    let .ok id := FromJson.fromJson? name
      | panic! "Failed to deserialize as id `{name}`"
    let .some (_, part) := (← read).docs.binSearch (id, default) (fun (a, _) (b, _) => Name.quickLt a b)
      | panic! "Failed to find id `{id}`"
    return part
  | .obj o => do
    let aux ← read
    let title := o.get! "title" |>.getArr! |>.map (match ·.getNat? with
      | .ok n => match aux.inlines[n]? with
        | .some t => t
        | .none => panic! s!"out of bound inline: {n} vs {aux.inlines.size}"
      | .error e => panic! s!"Ill-formed JSON part serialization (title) {e}")
    let titleString := o.get! "titleString" |>.getStr!
    let metadata := match o.get! "metadata" with
      | .null => .none
      | .arr #[.num (n : Nat)] =>
        match (aux.partMetadata[n]?) with
          | .some s => .some s
          | .none => panic s!"Ill-formed JSON part serialization (metadata) {n}"
      | json => panic! s!"Ill-formed JSON part serialization (metadata) {json}"
    let content := o.get! "content" |>.getArr! |>.map (match ·.getNat? with
      | .ok n => match aux.blocks[n]? with
        | .some t => t
        | .none => panic! s!"out of bound block: {n} vs {aux.blocks.size}"
      | .error e => panic! s!"Ill-formed JSON part serialization (content) {e}")
    let subParts ← o.get! "subParts" |>.getArr! |>.mapM deserialize
    return Part.mk title titleString metadata content subParts
  | json => panic s!"Ill-formed JSON part serialization {json}"

/--
A {lean}`VersoDoc` represents a potentially-not-fully-evaluated {lean}`Part`. Calling {lean}`VersoDoc.toPart` forces
evaluation of the {lean}`VersoDoc` to a {lean}`Part`.
-/
public def VersoDoc.toPart: VersoDoc genre → Part genre
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
  | .literal part => part
