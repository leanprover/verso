/-
Copyright (c) 2023-2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen, Rob Simmons
-/
module
public import Verso.Doc
import Verso.VersoDoc
public import Verso.Finished

open Lean

open Std (HashMap HashSet)

set_option doc.verso true

namespace Verso.Doc.Elab

public inductive TOC where
  | mk (title : String) (titleSyntax : Syntax) (endPos : String.Pos.Raw) (children : Array TOC)
  | included (name : Ident)
deriving Repr, TypeName, Inhabited

/--
From a finished part, constructs syntax that denotes its {lean}`Part` value.
-/
public partial def FinishedPart.toSyntax [Monad m] [MonadQuotation m]
    (genre : TSyntax `term)
    : FinishedPart → m Term
  | .mk _titleStx titleInlines titleString metadata blocks subParts _endPos => do
    let subStx ← subParts.mapM (toSyntax genre)
    let metaStx ←
      match metadata with
      | none => `(none)
      | some stx => `(some $stx)
    -- Adding type annotations works around a limitation in list and array elaboration, where intermediate
    -- let bindings introduced by "chunking" the elaboration may fail to infer types
    let typedBlocks ← blocks.mapM fun b => `(($b : Block $genre))
    ``(Part.mk #[$titleInlines,*] $(quote titleString) $metaStx #[$typedBlocks,*] #[$subStx,*])
  | .included name => ``(DocThunk.force $name)

public partial def FinishedPart.toTOC : FinishedPart → TOC
  | .mk titleStx _titleInlines titleString _metadata _blocks subParts endPos =>
    .mk titleString titleStx endPos (subParts.map toTOC)
  | .included name => .included name


/--
Information describing a part still under construction.

During elaboration, the current position in the document is
represented by a stack of these frames, with each frame representing a
layer of document section nesting. As the Verso document elaborator
encounters new headers, stack frames are pushed and popped as
indicated by the header's level.
-/
public structure PartFrame where
  titleSyntax : Syntax
  expandedTitle : Option (String × Array (TSyntax `term)) := none
  metadata : Option (TSyntax `term)
  blocks : Array (TSyntax `term)
  /--
  The sibling parts at the same nesting level as the part represented by this frame. These siblings
  are earlier in the document and have the same parent.
  -/
  priorParts : Array FinishedPart
deriving Repr, Inhabited

/-- Turn an previously active {name}`PartFrame` into a {name}`FinishedPart`. -/
public def PartFrame.close (fr : PartFrame) (endPos : String.Pos.Raw) : FinishedPart :=
  let (titlePreview, titleInlines) := fr.expandedTitle.getD ("<anonymous>", #[])
  .mk fr.titleSyntax titleInlines titlePreview fr.metadata fr.blocks fr.priorParts endPos


/-- References that must be local to the current blob of concrete document syntax -/
public structure DocDef (α : Type) where
  defSite : TSyntax `str
  val : α
deriving Repr

public structure DocUses where
  useSites : Array Syntax := {}
deriving Repr

public def DocUses.add (uses : DocUses) (loc : Syntax) : DocUses := {uses with useSites := uses.useSites.push loc}


/--
Information available while constructing a part. It extends {name}`PartFrame`
because that data represents the current frame. The field
{name (full := PartContext.parents)}`parents` represents other parts above
us in the hierarchy that are still being built.
-/
public structure PartContext extends PartFrame where
  parents : Array PartFrame
deriving Repr, Inhabited

/--
The current nesting level is the number of frames in the stack of parent
parts being built.
-/
public def PartContext.level (ctxt : PartContext) : Nat := ctxt.parents.size

/--
Closes the current part. The resulting {name}`FinishedPart` is appended to
{name (full := PartFrame.priorParts)}`priorParts`, and
the top of the stack of our parents becomes the current frame. Returns
{name}`none` if there are no parents.
-/
public def PartContext.close (ctxt : PartContext) (endPos : String.Pos.Raw) : Option PartContext := do
  let fr ← ctxt.parents.back?
  pure {
    parents := ctxt.parents.pop,
    blocks := fr.blocks,
    titleSyntax := fr.titleSyntax,
    expandedTitle := fr.expandedTitle,
    metadata := fr.metadata
    priorParts := fr.priorParts.push <| ctxt.toPartFrame.close endPos
  }

/--
Makes the frame {name}`fr` the current frame. The former current frame is saved to the stack.
-/
public def PartContext.push (ctxt : PartContext) (fr : PartFrame) : PartContext := ⟨fr, ctxt.parents.push ctxt.toPartFrame⟩


/-- Custom info tree data to save footnote and reflink cross-references -/
public structure DocRefInfo where
  defSite : Option Syntax
  useSites : Array Syntax
deriving TypeName, Repr

public def DocRefInfo.syntax (dri : DocRefInfo) : Array Syntax :=
  (dri.defSite.map (#[·])|>.getD #[]) ++ dri.useSites

public def internalRefs (defs : HashMap String (DocDef α)) (refs : HashMap String DocUses) : Array DocRefInfo := Id.run do
  let keys : HashSet String := defs.fold (fun soFar k _ => HashSet.insert soFar k) <| refs.fold (fun soFar k _ => soFar.insert k) {}
  let mut refInfo := #[]
  for k in keys do
    refInfo := refInfo.push {
      defSite := defs[k]? |>.map (·.defSite),
      useSites := refs[k]? |>.map (·.useSites) |>.getD #[]
    }
  refInfo

/-- Custom info tree data to save the locations and identities of lists -/
public structure DocListInfo where
  bullets : Array Syntax
  items : Array Syntax
deriving Repr, TypeName
