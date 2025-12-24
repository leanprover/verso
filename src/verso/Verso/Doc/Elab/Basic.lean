/-
Copyright (c) 2023-2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen, Rob Simmons
-/
module
public import Verso.Doc
meta import Verso.Doc

open Lean

open Std (HashMap HashSet)

set_option doc.verso true

namespace Verso.Doc.Elab

public inductive TOC where
  | mk (title : String) (titleSyntax : Array Term) (children : Array TOC)
  | included (name : Ident)
deriving Repr, TypeName, Inhabited

public partial def partToTOC : IR.Part → TOC
  | .mk titleInlines titleString _metadata _blocks subParts =>
    .mk titleString titleInlines (subParts.map partToTOC)
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
  priorParts : Array IR.Part
deriving Repr, Inhabited

/-- Turn an previously active {name}`PartFrame` into a {name}`IR.Part`. -/
public def PartFrame.close (fr : PartFrame) : IR.Part :=
  let (titlePreview, titleInlines) := fr.expandedTitle.getD ("<anonymous>", #[])
  .mk titleInlines titlePreview fr.metadata fr.blocks fr.priorParts


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
Closes the current part. The resulting {name}`IR.Part` is appended to
{name (full := PartFrame.priorParts)}`priorParts`, and
the top of the stack of our parents becomes the current frame. Returns
{name}`none` if there are no parents.
-/
public def PartContext.close (ctxt : PartContext) : Option PartContext := do
  let fr ← ctxt.parents.back?
  pure {
    parents := ctxt.parents.pop,
    blocks := fr.blocks,
    titleSyntax := fr.titleSyntax,
    expandedTitle := fr.expandedTitle,
    metadata := fr.metadata
    priorParts := fr.priorParts.push <| ctxt.toPartFrame.close
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
