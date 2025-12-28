/-
Copyright (c) 2023-2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen, Rob Simmons
-/
module
public import Verso.Doc
import Verso.Doc.Reconstruct

open Lean

open Std (HashMap HashSet)

set_option doc.verso true

namespace Verso.Doc.Elab

public inductive TOC where
  | mk (title : String) (titleSyntax : Syntax) (endPos : String.Pos.Raw) (children : Array TOC)
  | included (name : Ident)
deriving Repr, TypeName, Inhabited

/- Elaboration targets -/
namespace Target
/--
The result of elaborating an inline component of a document
-/
public abbrev Inline := Term

variable (genre : Genre) in
public section
/--
The result of elaborating a document block. Concretely denotes a {lean}`Doc.Block genre` for some
unspecified {name}`genre`.
-/
public inductive Block where
  | para (contents : Array Inline)
  | code (content : String)
  | ul (items : Array (Array Block))
  | ol (start : Int) (items : Array (Array Block))
  | dl (items : Array ((Array Inline) × (Array Block)))
  | blockquote (items : Array Block)
  | concat (content : Array Block)
  | other (container : Term) (content : Array Block)
  | stx (stx : Term)
deriving Repr, BEq

end

mutual
public partial def ListItem.toTerm [Monad m] [MonadRef m] [MonadQuotation m] (genre : Term) : Array Target.Block → m Term
  | contents => do ``(Doc.ListItem.mk #[$(← contents.mapM (Target.Block.toTerm genre)),*])

public partial def DescItem.toTerm [Monad m] [MonadRef m] [MonadQuotation m] (genre : Term) : Array Inline × Array Block → m Term
  | (term, desc) => do ``(Doc.DescItem.mk #[$term,*] #[$(← desc.mapM (Block.toTerm genre)),*])

public partial def Block.toTerm [Monad m] [MonadRef m] [MonadQuotation m] (genre : Term) : Block → m Term
  | .para contents => ``(Doc.Block.para (genre := $(genre)) #[$contents,*])
  | .code contents => ``(Doc.Block.code (genre := $(genre)) $(quote contents))
  | .ul contents => do ``(Doc.Block.ul (genre := $(genre)) #[$(← contents.mapM (ListItem.toTerm genre)),*])
  | .ol start contents => do ``(Doc.Block.ol (genre := $(genre)) $(← quoteInt start) #[$(← contents.mapM (ListItem.toTerm genre)),*])
  | .dl contents => do ``(Doc.Block.dl (genre := $(genre)) #[$(← contents.mapM (DescItem.toTerm genre)),*])
  | .blockquote contents => do ``(Doc.Block.blockquote (genre := $(genre)) #[$(← contents.mapM (Block.toTerm genre)),*])
  | .concat content => do ``(Doc.Block.concat (genre := $(genre)) #[$(← content.mapM (Block.toTerm genre)),*])
  | .other container content => do ``(Doc.Block.other (genre := $(genre)) $container #[$(← content.mapM (Block.toTerm genre)),*])
  | .stx stx => pure stx
where
  quoteInt : Int → m Term
  | .ofNat n => ``(Int.ofNat $(quote n))
  | .negSucc n => ``(Int.negSucc $(quote n))
end

end Target

variable (genre : Genre) in
/--
The result of elaborating a document part. Concretely denotes a {lean}`Doc.Part genre` for some
unspecified {name}`genre`.
-/
public inductive FinishedPart where
  | mk (titleSyntax : Syntax) (expandedTitle : Array Target.Inline) (titlePreview : String) (metadata : Option Term) (blocks : Array Target.Block) (subParts : Array FinishedPart) (endPos : String.Pos.Raw)
    /-- A name representing a value of type {lean}`DocThunk` -/
  | included (name : Ident)
deriving Repr, BEq

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
    let typedBlocks ← blocks.mapM fun b => do ``(($(← b.toTerm genre) : Doc.Block $genre))
    ``(Doc.Part.mk #[$titleInlines,*] $(quote titleString) $metaStx #[$typedBlocks,*] #[$subStx,*])
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
  expandedTitle : Option (String × Array Target.Inline) := none
  metadata : Option Term
  blocks : Array Target.Block
  /--
  The sibling parts at the same nesting level as the part represented by this frame. These siblings
  are earlier in the document and have the same parent.
  -/
  priorParts : Array FinishedPart
deriving Repr, Inhabited

/-- Turn an previously active {name}`PartFrame` into a {name}`Part`. -/
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
