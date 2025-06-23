/-
Copyright (c) 2023-2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import Std.Data.HashMap
import Std.Data.HashSet

import Lean.Elab.DeclUtil

import Verso.Doc
import Verso.Doc.Elab.ExpanderAttribute
import Verso.Doc.Elab.InlineString
import Verso.Hover
import Verso.SyntaxUtils
import Verso.Syntax

namespace Verso.Doc.Elab

open Lean
open Lean.Elab
open Std (HashMap HashSet)
open Verso.SyntaxUtils

initialize registerTraceClass `Elab.Verso
initialize registerTraceClass `Elab.Verso.part
initialize registerTraceClass `Elab.Verso.block

class HasLink (name : String) (doc : Name) where
  url : String

class HasNote (name : String) (doc : Name) (genre : Genre) where
  contents : Array (Inline genre)


-- For use in IDE features and previews and such
@[inline_to_string Verso.Syntax.text]
def _root_.Verso.Syntax.text.inline_to_string : InlineToString
  | _, `(inline| $s:str) => some s.getString
  | _, _ => none

@[inline_to_string Verso.Syntax.linebreak]
def _root_.Verso.Syntax.linebreak.inline_to_string : InlineToString
  | _, `(inline|line! $_) => some " "
  | _, _ => none

@[inline_to_string Verso.Syntax.emph]
def _root_.Verso.Syntax.emph.inline_to_string : InlineToString
  | env, `(inline| _[ $args* ]) =>
    some <| String.intercalate " " (Array.map (inlineToString env) args).toList
  | _, _ => none

@[inline_to_string Verso.Syntax.bold]
def _root_.Verso.Syntax.bold.inline_to_string : InlineToString
  | env, `(inline| *[ $args* ]) =>
    some <| String.intercalate " " (Array.map (inlineToString env) args).toList
  | _, _ => none

@[inline_to_string Verso.Syntax.code]
def _root_.Verso.Syntax.code.inline_to_string : InlineToString
  | _, `(inline| code( $str )) =>
    some str.getString
  | _, _ => none

@[inline_to_string Verso.Syntax.role]
def _root_.Verso.Syntax.role.inline_to_string : InlineToString
  | env, `(inline| role{ $_ $_* }[ $body* ]) =>
    String.join (body.toList.map (inlineToString env <| ·.raw))
  | _, _ => none

@[inline_to_string null]
def nullInline_to_string : InlineToString
  | env, .node _ _ contents =>
    return String.join <| contents.toList.map (inlineToString env)
  | _, _ => none


def inlinesToString (env : Environment) (inlines : Array Syntax)  : String :=
  String.intercalate " " (inlines.map (inlineToString env)).toList

def inlineSyntaxToString (env : Environment) (inlines : Syntax) : String :=
    if let `<low| ~(.node _ _ args)> := inlines then
      inlinesToString env args
    else
      dbg_trace "didn't understand inline sequence {inlines} for string"
      "<missing>"

def headerStxToString (env : Environment) : Syntax → String
  | `(block|header($_){$inlines*}) => inlinesToString env inlines
  | headerStx => dbg_trace "didn't understand {headerStx} for string"
    "<missing>"

/-- Parameters that have dynamic extent with respect to Verso elaboration. -/
structure DocElabParameters where
  parameters : NameMap Dynamic := {}

structure DocElabContext where
  genreSyntax : Syntax
  genre : Expr
  parameters : DocElabParameters := {}

section
variable [Monad m] [MonadError m] [MonadReaderOf DocElabContext m] [MonadWithReaderOf DocElabContext m] [TypeName α]

def withModifiedParameter  (x : Name) (f : α → α) (act : m β) : m β := do
  let ⟨params⟩ := (← read).parameters
  if let some v := params.find? x then
    if let some v := v.get? α then
      withReader ({ · with parameters := ⟨params.insert x (.mk (f  v))⟩ }) act
    else throwError m!"Internal error: expected a {TypeName.typeName α} for {x}, but got a {v.typeName}"
  else throwError m!"Internal error: no value for parameter {x} of type {TypeName.typeName α}"

def withParameter (x : Name) (value : α) (act : m β) : m β := do
  let ⟨params⟩ := (← read).parameters
  if let some v := params.find? x then
    if v.typeName ≠ TypeName.typeName α then
      throwError m!"Internal error: expected a {TypeName.typeName α} for {x}, but a {v.typeName} was already present."
  withReader ({ · with parameters := ⟨params.insert x (.mk value)⟩ }) act

def parameterValue! (x : Name) : m α := do
  let ⟨params⟩ := (← read).parameters
  if let some v := params.find? x then
    if let some v := v.get? α then
      return v
    else
      throwError m!"Internal error: expected a {TypeName.typeName α} for {x}, but found a {v.typeName}."
  else
    throwError m!"Internal error: no value for {x}. Expected a {TypeName.typeName α} but no value was present."

def parameterValue? (x : Name) : m (Option α) := do
  let ⟨params⟩ := (← read).parameters
  if let some v := params.find? x then
    if let some v := v.get? α then
      return (some v)
    else
      throwError m!"Internal error: expected a {TypeName.typeName α} for {x}, but found a {v.typeName}."
  else
    return none

end

/-- References that must be local to the current blob of concrete document syntax -/
structure DocDef (α : Type) where
  defSite : TSyntax `str
  val : α

structure DocUses where
  useSites : Array Syntax := {}

def DocUses.add (uses : DocUses) (loc : Syntax) : DocUses := {uses with useSites := uses.useSites.push loc}

structure DocElabM.State where
  linkRefs : HashMap String DocUses := {}
  footnoteRefs : HashMap String DocUses := {}
deriving Inhabited

/-- Custom info tree data to save footnote and reflink cross-references -/
structure DocRefInfo where
  defSite : Option Syntax
  useSites : Array Syntax
deriving TypeName, Repr

def DocRefInfo.syntax (dri : DocRefInfo) : Array Syntax :=
  (dri.defSite.map (#[·])|>.getD #[]) ++ dri.useSites

def internalRefs (defs : HashMap String (DocDef α)) (refs : HashMap String DocUses) : Array DocRefInfo := Id.run do
  let keys : HashSet String := defs.fold (fun soFar k _ => HashSet.insert soFar k) <| refs.fold (fun soFar k _ => soFar.insert k) {}
  let mut refInfo := #[]
  for k in keys do
    refInfo := refInfo.push ⟨defs[k]? |>.map (·.defSite), refs[k]? |>.map (·.useSites) |>.getD #[]⟩
  refInfo


inductive TOC where
  | mk (title : String) (titleSyntax : Syntax) (endPos : String.Pos) (children : Array TOC)
  | included (name : Ident)
deriving Repr, TypeName, Inhabited

structure TocFrame where
  ptr : Nat
  title : String
  titleSyntax : Syntax
  priorChildren : Array TOC
deriving Repr, Inhabited

def TocFrame.close (frame : TocFrame) (endPos : String.Pos) : TOC :=
  .mk frame.title frame.titleSyntax endPos frame.priorChildren

def TocFrame.wrap (frame : TocFrame) (item : TOC) (endPos : String.Pos) : TOC :=
  .mk frame.title frame.titleSyntax endPos (frame.priorChildren.push item)

def TocFrame.addChild (frame : TocFrame) (item : TOC) : TocFrame :=
  {frame with priorChildren := priorChildren frame |>.push item}

partial def TocFrame.closeAll (stack : Array TocFrame) (endPos : String.Pos) : Option TOC :=
  let rec aux (stk : Array TocFrame) (toc : TOC) :=
    if let some fr := stack.back? then
      aux stk.pop (fr.wrap toc endPos)
    else toc
  if let some fr := stack.back? then
    some (aux stack.pop <| fr.close endPos)
  else none


def TocFrame.wrapAll (stack : Array TocFrame) (item : TOC) (endPos : String.Pos) : TOC :=
  let rec aux (i : Nat) (item : TOC) (endPos : String.Pos) : TOC :=
    match i with
    | 0 => item
    | i' + 1 =>
      if let some fr := stack[i]? then
        aux i' (fr.wrap item endPos) endPos
      else item
  aux (stack.size - 1) item endPos

inductive FinishedPart where
  | mk (titleSyntax : Syntax) (expandedTitle : Array (TSyntax `term)) (titlePreview : String) (metadata : Option (TSyntax `term)) (blocks : Array (TSyntax `term)) (subParts : Array FinishedPart) (endPos : String.Pos)
  | included (name : Ident)
deriving Repr, BEq

private def linkRefName [Monad m] [MonadQuotation m] (docName : Name) (ref : TSyntax `str) : m Term := do
  ``(HasLink.url $(quote ref.getString) $(quote docName) (self := _))

private def footnoteRefName [Monad m] [MonadQuotation m] (genre : Term) (docName : Name) (ref : TSyntax `str) : m Term :=
  ``(HasNote.contents $(quote ref.getString) $(quote docName) (genre := $genre) (self := _))


open Lean.Parser.Term in
partial def FinishedPart.toSyntax [Monad m] [MonadQuotation m] [MonadEnv m]
    (genre : TSyntax `term)
    : FinishedPart → m (TSyntax `term)
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
  | .included name => pure name

structure ToSyntaxState where
  gensymCounter : Nat := 0

open Command

partial def FinishedPart.toSyntax' [Monad m] [MonadQuotation m] [MonadLiftT CommandElabM m] [MonadEnv m]
    (genre : TSyntax `term)
    (finishedPart : FinishedPart) : m (TSyntax `term) := do
  let rootName ← currentDocName
  let HelperM := ReaderT Name (StateT ToSyntaxState m)

  let rec gensym (src : Syntax) (hint := "gensym") : HelperM (TSyntax `ident) := do
    let x ←
      modifyGet fun (st : ToSyntaxState) =>
        let n : Name := .str rootName s!"{hint}{st.gensymCounter}"
        (mkIdentFrom src n, {st with gensymCounter := st.gensymCounter + 1})
    if (← getEnv).contains x.getId then
      gensym src (hint := hint)
    else pure x

  let rec helper : FinishedPart → HelperM (TSyntax `term)
      | .mk titleStx titleInlines titleString metadata blocks subParts _endPos => do
        let partName ← gensym titleStx (hint := titleString)
        let subStx ← subParts.mapM helper
        let mut blockNames := #[]
        for b in blocks do
          let n ← gensym b
          withRef genre <|
            elabCommand (← `(def $n : Block $genre := $b))
          blockNames := blockNames.push n
        let metaStx ←
          match metadata with
          | none => `(none)
          | some stx => `(some $stx)
        elabCommand (← `(def $partName : Part $genre := Part.mk #[$[$titleInlines],*] $(quote titleString) $metaStx #[$blockNames,*] #[$[$subStx],*]))
        pure partName
      | .included name => pure name
  StateT.run' (ReaderT.run (helper finishedPart) rootName) {}

partial def FinishedPart.toTOC : FinishedPart → TOC
  | .mk titleStx _titleInlines titleString _metadata _blocks subParts endPos =>
    .mk titleString titleStx endPos (subParts.map toTOC)
  | .included name => .included name

structure PartFrame where
  titleSyntax : Syntax
  expandedTitle : Option (String × Array (TSyntax `term)) := none
  metadata : Option (TSyntax `term)
  blocks : Array (TSyntax `term)
  priorParts : Array FinishedPart
deriving Repr, Inhabited

def PartFrame.close (fr : PartFrame) (endPos : String.Pos) : FinishedPart :=
  let (titlePreview, titleInlines) := fr.expandedTitle.getD ("<anonymous>", #[])
  .mk fr.titleSyntax titleInlines titlePreview fr.metadata fr.blocks fr.priorParts endPos

structure PartContext extends PartFrame where
  parents : Array PartFrame
deriving Repr, Inhabited

def PartContext.level (ctxt : PartContext) : Nat := ctxt.parents.size
def PartContext.close (ctxt : PartContext) (endPos : String.Pos) : Option PartContext := do
  let fr ← ctxt.parents.back?
  pure {
    parents := ctxt.parents.pop,
    blocks := fr.blocks,
    titleSyntax := fr.titleSyntax,
    expandedTitle := fr.expandedTitle,
    metadata := fr.metadata
    priorParts := fr.priorParts.push <| ctxt.toPartFrame.close endPos
  }

def PartContext.push (ctxt : PartContext) (fr : PartFrame) : PartContext := ⟨fr, ctxt.parents.push ctxt.toPartFrame⟩

structure PartElabM.State where
  partContext : PartContext
  linkDefs : HashMap String (DocDef String) := {}
  footnoteDefs : HashMap String (DocDef (Array (TSyntax `term))) := {}
deriving Inhabited

def PartElabM.State.init (title : Syntax) (expandedTitle : Option (String × Array (TSyntax `term)) := none) : PartElabM.State where
  partContext := {titleSyntax := title, expandedTitle, metadata := none, blocks := #[], priorParts := #[], parents := #[]}

def PartElabM (α : Type) : Type := ReaderT DocElabContext (StateT DocElabM.State (StateT PartElabM.State TermElabM)) α

def PartElabM.run (genreSyntax : Syntax) (genre : Expr)
    (st : DocElabM.State) (st' : PartElabM.State)
    (act : PartElabM α)
    (params : DocElabParameters := {}) : TermElabM (α × DocElabM.State × PartElabM.State) := do
  let ((res, st), st') ← act ⟨genreSyntax, genre, params⟩ st st'
  pure (res, st, st')

instance : Alternative PartElabM := inferInstanceAs <| Alternative (ReaderT DocElabContext (StateT DocElabM.State (StateT PartElabM.State TermElabM)))

instance : MonadRef PartElabM := inferInstanceAs <| MonadRef (ReaderT DocElabContext (StateT DocElabM.State (StateT PartElabM.State TermElabM)))

instance : MonadAlwaysExcept Exception PartElabM := inferInstanceAs <| MonadAlwaysExcept Exception (ReaderT DocElabContext (StateT DocElabM.State (StateT PartElabM.State TermElabM)))

instance : AddErrorMessageContext PartElabM := inferInstanceAs <| AddErrorMessageContext (ReaderT DocElabContext (StateT DocElabM.State (StateT PartElabM.State TermElabM)))

instance : MonadQuotation PartElabM := inferInstanceAs <| MonadQuotation (ReaderT DocElabContext (StateT DocElabM.State (StateT PartElabM.State TermElabM)))

instance : Monad PartElabM := inferInstanceAs <| Monad (ReaderT DocElabContext (StateT DocElabM.State (StateT PartElabM.State TermElabM)))

instance : MonadLift TermElabM PartElabM where
  monadLift act := fun _ st st' => do return ((← Term.withDeclName (← currentDocName) act, st), st')

instance : MonadExceptOf Exception PartElabM := inferInstanceAs <| MonadExceptOf Exception (ReaderT DocElabContext (StateT DocElabM.State (StateT PartElabM.State TermElabM)))

instance : MonadStateOf DocElabM.State PartElabM := inferInstanceAs <| MonadStateOf DocElabM.State (ReaderT DocElabContext (StateT DocElabM.State (StateT PartElabM.State TermElabM)))

instance : MonadStateOf PartElabM.State PartElabM := inferInstanceAs <| MonadStateOf PartElabM.State (ReaderT DocElabContext (StateT DocElabM.State (StateT PartElabM.State TermElabM)))

instance : MonadFinally PartElabM := inferInstanceAs <| MonadFinally (ReaderT DocElabContext (StateT DocElabM.State (StateT PartElabM.State TermElabM)))

instance : MonadRef PartElabM := inferInstanceAs <| MonadRef (ReaderT DocElabContext (StateT DocElabM.State (StateT PartElabM.State TermElabM)))

instance : MonadWithReaderOf Core.Context PartElabM := inferInstanceAs <| MonadWithReaderOf Core.Context (ReaderT DocElabContext (StateT DocElabM.State (StateT PartElabM.State TermElabM)))

instance : MonadWithReaderOf Term.Context PartElabM := inferInstanceAs <| MonadWithReaderOf Term.Context (ReaderT DocElabContext (StateT DocElabM.State (StateT PartElabM.State TermElabM)))

instance : MonadReaderOf DocElabContext PartElabM := inferInstanceAs <| MonadReaderOf DocElabContext (ReaderT DocElabContext (StateT DocElabM.State (StateT PartElabM.State TermElabM)))

def PartElabM.withFileMap (fileMap : FileMap) (act : PartElabM α) : PartElabM α :=
  fun ρ ρ' σ ctxt σ' mctxt rw cctxt => act ρ ρ' σ ctxt σ' mctxt rw {cctxt with fileMap := fileMap}

def DocElabM (α : Type) : Type := ReaderT DocElabContext (ReaderT PartElabM.State (StateT DocElabM.State TermElabM)) α

def DocElabM.run (genreSyntax : Syntax) (genre : Expr)
    (st : DocElabM.State) (st' : PartElabM.State)
    (act : DocElabM α)
    (params : DocElabParameters := {}) : TermElabM (α × DocElabM.State) := do
  StateT.run (act ⟨genreSyntax, genre, params⟩ st') st

instance : Inhabited (DocElabM α) := ⟨fun _ _ _ => default⟩

instance : AddErrorMessageContext DocElabM := inferInstanceAs <| AddErrorMessageContext (ReaderT DocElabContext (ReaderT PartElabM.State (StateT DocElabM.State TermElabM)))

instance [MonadWithReaderOf ρ TermElabM] : MonadWithReaderOf ρ DocElabM :=
  inferInstanceAs <| MonadWithReaderOf ρ (ReaderT DocElabContext (ReaderT PartElabM.State (StateT DocElabM.State TermElabM)))

instance : MonadLift TermElabM DocElabM where
  monadLift act := fun _ _ st' => do return (← Term.withDeclName (← currentDocName) act, st')

instance : MonadLift IO DocElabM where
  monadLift act := fun _ _ st' => do return (← act, st')

instance : Alternative DocElabM := inferInstanceAs <| Alternative (ReaderT DocElabContext (ReaderT PartElabM.State (StateT DocElabM.State TermElabM)))

instance : MonadRef DocElabM := inferInstanceAs <| MonadRef (ReaderT DocElabContext (ReaderT PartElabM.State (StateT DocElabM.State TermElabM)))

instance : MonadQuotation DocElabM := inferInstanceAs <| MonadQuotation (ReaderT DocElabContext (ReaderT PartElabM.State (StateT DocElabM.State TermElabM)))

instance : Monad DocElabM := inferInstanceAs <| Monad (ReaderT DocElabContext (ReaderT PartElabM.State (StateT DocElabM.State TermElabM)))

instance : MonadControl TermElabM DocElabM :=
  let ⟨stM, liftWith, restoreM⟩ := inferInstanceAs <| MonadControlT TermElabM (ReaderT DocElabContext (ReaderT PartElabM.State (StateT DocElabM.State TermElabM)))
  {stM, liftWith, restoreM := (· >>= restoreM)}

instance : MonadExceptOf Exception DocElabM := inferInstanceAs <| MonadExceptOf Exception (ReaderT DocElabContext (ReaderT PartElabM.State (StateT DocElabM.State TermElabM)))

instance : MonadAlwaysExcept Exception DocElabM := inferInstanceAs <| MonadAlwaysExcept Exception (ReaderT DocElabContext (ReaderT PartElabM.State (StateT DocElabM.State TermElabM)))

instance : MonadReaderOf PartElabM.State DocElabM := inferInstanceAs <| MonadReaderOf PartElabM.State (ReaderT DocElabContext (ReaderT PartElabM.State (StateT DocElabM.State TermElabM)))

instance : MonadStateOf DocElabM.State DocElabM := inferInstanceAs <| MonadStateOf DocElabM.State (ReaderT DocElabContext (ReaderT PartElabM.State (StateT DocElabM.State TermElabM)))

instance : MonadFinally DocElabM := inferInstanceAs <| MonadFinally (ReaderT DocElabContext (ReaderT PartElabM.State (StateT DocElabM.State TermElabM)))

instance : MonadInfoTree DocElabM := inferInstanceAs <| MonadInfoTree (ReaderT DocElabContext (ReaderT PartElabM.State (StateT DocElabM.State TermElabM)))

instance : MonadEnv DocElabM := inferInstanceAs <| MonadEnv (ReaderT DocElabContext (ReaderT PartElabM.State (StateT DocElabM.State TermElabM)))

instance : MonadFileMap DocElabM := inferInstanceAs <| MonadFileMap (ReaderT DocElabContext (ReaderT PartElabM.State (StateT DocElabM.State TermElabM)))

instance : MonadOptions DocElabM := inferInstanceAs <| MonadOptions (ReaderT DocElabContext (ReaderT PartElabM.State (StateT DocElabM.State TermElabM)))

instance : MonadWithOptions DocElabM := inferInstanceAs <| MonadWithOptions (ReaderT DocElabContext (ReaderT PartElabM.State (StateT DocElabM.State TermElabM)))

instance : MonadWithReaderOf Core.Context DocElabM := inferInstanceAs <| MonadWithReaderOf Core.Context (ReaderT DocElabContext (ReaderT PartElabM.State (StateT DocElabM.State TermElabM)))

instance : MonadWithReaderOf Term.Context DocElabM := inferInstanceAs <| MonadWithReaderOf Term.Context (ReaderT DocElabContext (ReaderT PartElabM.State (StateT DocElabM.State TermElabM)))

instance : MonadReaderOf DocElabContext DocElabM := inferInstanceAs <| MonadReaderOf DocElabContext (ReaderT DocElabContext (ReaderT PartElabM.State (StateT DocElabM.State TermElabM)))

instance : MonadReaderOf PartElabM.State DocElabM := inferInstanceAs <| MonadReaderOf PartElabM.State (ReaderT DocElabContext (ReaderT PartElabM.State (StateT DocElabM.State TermElabM)))

def DocElabM.withFileMap (fileMap : FileMap) (act : DocElabM α) : DocElabM α :=
  fun ρ ρ' σ ctxt σ' mctxt rw cctxt => act ρ ρ' σ ctxt σ' mctxt rw {cctxt with fileMap := fileMap}

instance : MonadRecDepth DocElabM where
  withRecDepth n act := fun ρ st st' => MonadRecDepth.withRecDepth n (act ρ st st')
  getRecDepth := fun _ _ st' => do return (← MonadRecDepth.getRecDepth, st')
  getMaxRecDepth := fun _ _ st' => do return (← MonadRecDepth.getMaxRecDepth, st')

def PartElabM.liftDocElabM (act : DocElabM α) : PartElabM α := do
  let ⟨gStx, g, _⟩ ← readThe DocElabContext
  let (out, st') ← act.run gStx g (← getThe DocElabM.State) (← getThe PartElabM.State)
  set st'
  pure out

instance : MonadLift DocElabM PartElabM := ⟨PartElabM.liftDocElabM⟩

def PartElabM.State.currentLevel (state : PartElabM.State) : Nat := state.partContext.level

def PartElabM.currentLevel : PartElabM Nat := do return (← getThe State).currentLevel

def PartElabM.setTitle (titlePreview : String) (titleInlines : Array (TSyntax `term)) : PartElabM Unit := modifyThe State fun st =>
  {st with partContext.expandedTitle := some (titlePreview, titleInlines)}

def findLinksAndNotes : Expr → MetaM (Array (Expr × Expr))
  | .app t1 t2 => do return (← findLinksAndNotes t1) ++ (← findLinksAndNotes t2)
  | e@(.mvar _) => do
    let ty ← Meta.inferType e
    if ty.isAppOf ``HasLink || ty.isAppOf ``HasNote then pure #[(e, ty)] else pure #[]
  | .lam _ t b _ | .forallE _ t b _ => do return (← findLinksAndNotes t) ++ (← findLinksAndNotes b)
  | .letE _ t d b _ => do return (← findLinksAndNotes t) ++ (← findLinksAndNotes d) ++ (← findLinksAndNotes b)
  | .mdata _ e | .proj _ _ e => findLinksAndNotes e
  | .sort .. | .fvar .. | .bvar .. | .const .. | .lit .. => pure #[]

def DocElabM.genreExpr : DocElabM Expr := do
  let ⟨_, g, _⟩ ← readThe DocElabContext
  return g

def DocElabM.blockType : DocElabM Expr := do
  let ⟨_, g, _⟩ ← readThe DocElabContext
  return .app (.const ``Doc.Block []) g

def DocElabM.inlineType : DocElabM Expr := do
  let ⟨_, g, _⟩ ← readThe DocElabContext
  return .app (.const ``Doc.Inline []) g

def DocElabM.emptyBlock : DocElabM Expr := do
  pure <| mkApp2 (.const ``Block.concat []) (← genreExpr) (← Meta.mkArrayLit (← blockType) [])

open Lean Meta Elab Term in
def DocElabM.defineInline (inline : Expr) : DocElabM Name := do
  let ⟨_, g, _⟩ ← readThe DocElabContext

  let n ← mkFreshUserName `inline

  let type : Expr := .app (.const ``Doc.Inline []) g
  let t ← ensureHasType (some type) inline
  let t ← instantiateMVars t
  let links ← findLinksAndNotes t
  let t ← links.foldrM (init := t) fun (mv, mvty) t =>
    (.lam `inst mvty · .instImplicit) <$> t.abstractM #[mv]
  let t ← instantiateMVars t

  let xs ← Term.addAutoBoundImplicits #[] none
  let type ← instantiateMVars type
  let type ← mkForallFVars (links.map (·.1)) type (binderInfoForMVars := .instImplicit)
  let type ← mkForallFVars xs type
  let type ← levelMVarToParam type
  let usedParams  := collectLevelParams {} type |>.params

  match sortDeclLevelParams [] [] usedParams with
  | Except.error msg      => throwError msg
  | Except.ok levelParams =>
    synthesizeSyntheticMVarsNoPostponing
    let t ← instantiateMVars t
    let type ← instantiateMVars type
    let t ← ensureHasType (some type) t
    let decl := Declaration.defnDecl {
      name := n,
      levelParams := levelParams,
      type := type,
      value := t,
      hints := .abbrev,
      safety := .safe
    }
    Term.ensureNoUnassignedMVars decl
    addAndCompile decl
  return n

open Lean Meta Elab Term in
def DocElabM.defineBlock (block : Expr) : DocElabM Name := do
  let ⟨_, g, _⟩ ← readThe DocElabContext

  let n ← mkFreshUserName `block

  let type : Expr := .app (.const ``Doc.Block []) g
  let t ← ensureHasType (some type) block
  let t ← instantiateMVars t
  let links ← findLinksAndNotes t
  let t ← links.foldrM (init := t) fun (mv, mvty) t =>
    (.lam `inst mvty · .instImplicit) <$> t.abstractM #[mv]
  let t ← instantiateMVars t

  let xs ← Term.addAutoBoundImplicits #[] none
  let type ← instantiateMVars type
  let type ← mkForallFVars (links.map (·.1)) type (binderInfoForMVars := .instImplicit)
  let type ← mkForallFVars xs type
  let type ← levelMVarToParam type
  let usedParams  := collectLevelParams {} type |>.params

  match sortDeclLevelParams [] [] usedParams with
  | Except.error msg      => throwError msg
  | Except.ok levelParams =>
    synthesizeSyntheticMVarsNoPostponing
    let t ← instantiateMVars t
    let type ← instantiateMVars type
    let t ← ensureHasType (some type) t
    let decl := Declaration.defnDecl {
      name := n,
      levelParams := levelParams,
      type := type,
      value := t,
      hints := .abbrev,
      safety := .safe
    }
    Term.ensureNoUnassignedMVars decl
    addAndCompile decl
  return n

open Lean Meta Elab Term in
def PartElabM.addBlockExpr (block : Expr) : PartElabM Unit := do
  let n ← DocElabM.defineBlock block
  modifyThe State fun st =>
    { st with partContext.blocks := st.partContext.blocks.push (mkIdent n) }

open Lean Meta Elab Term in
def PartElabM.addBlock (block : TSyntax `term) : PartElabM Unit := withRef block <| do
  let ⟨_, g, _⟩ ← readThe DocElabContext
  let type : Expr := .app (.const ``Doc.Block []) g
  let t ← elabTerm block (some type)
  addBlockExpr t


def PartElabM.addPart (finished : FinishedPart) : PartElabM Unit := modifyThe State fun st =>
  {st with partContext.priorParts := st.partContext.priorParts.push finished}

def PartElabM.addLinkDef (refName : TSyntax `str) (url : String) : PartElabM Unit := do
  let strName := refName.getString
  let docName ← currentDocName
  match (← getThe State).linkDefs[strName]? with
  | none =>
    let t := mkApp2 (.const ``HasLink []) (toExpr strName) (toExpr docName)
    let n ← mkFreshUserName (docName ++ `inst.link ++ strName.toName)
    addAndCompile <| .defnDecl {
      name := n,
      levelParams := [],
      type := t,
      value := mkApp3 (.const ``HasLink.mk []) (toExpr strName) (toExpr docName) (toExpr url),
      hints := .abbrev,
      safety := .safe
    }
    Meta.addInstance n AttributeKind.global (eval_prio default)
    modifyThe State fun st => {st with linkDefs := st.linkDefs.insert strName ⟨refName, url⟩}

  | some ⟨_, url'⟩ =>
    throwErrorAt refName "Already defined as '{url'}'"

def DocElabM.addLinkRef (refName : TSyntax `str) : DocElabM (TSyntax `term) := do
  let strName := refName.getString
  match (← getThe State).linkRefs[strName]? with
  | none =>
    modifyThe State fun st => {st with linkRefs := st.linkRefs.insert strName ⟨#[refName]⟩}
    linkRefName (← currentDocName) refName
  | some ⟨uses⟩ =>
    modifyThe State fun st => {st with linkRefs := st.linkRefs.insert strName ⟨uses.push refName⟩}
    linkRefName (← currentDocName) refName


def PartElabM.addFootnoteDef (refName : TSyntax `str) (content : Array (TSyntax `term)) : PartElabM Unit := do
  let strName := refName.getString
  let docName ← currentDocName
  let ⟨_, genre, _⟩ ← readThe DocElabContext
  match (← getThe State).footnoteDefs[strName]? with
  | none =>
    let t := mkApp3 (.const ``HasNote []) (toExpr strName) (toExpr docName) genre
    let n ← mkFreshUserName (docName ++ `inst.note ++ strName.toName)
    let inlTy := Expr.app (.const ``Doc.Inline []) genre
    let inls ← Term.elabTerm (← `(#[$content,*])) (some (.app (.const ``Array [0]) inlTy))
    let inls ← instantiateMVars inls
    addAndCompile <| .defnDecl {
      name := n,
      levelParams := [],
      type := t,
      value := mkApp4 (.const ``HasNote.mk []) (toExpr strName) (toExpr docName) genre inls,
      hints := .abbrev,
      safety := .safe
    }
    Meta.addInstance n AttributeKind.global (eval_prio default)
    modifyThe State fun st => {st with footnoteDefs := st.footnoteDefs.insert strName ⟨refName, content⟩}
  | some ⟨_, content⟩ =>
    throwErrorAt refName "Already defined as '{content}'"

def DocElabM.addFootnoteRef (refName : TSyntax `str) : DocElabM (TSyntax `term) := do
  let strName := refName.getString
  let ⟨genre, _, _⟩ ← readThe DocElabContext
  match (← getThe State).footnoteRefs[strName]? with
  | none =>
    modifyThe State fun st => {st with footnoteRefs := st.footnoteRefs.insert strName ⟨#[refName]⟩}
    footnoteRefName ⟨genre⟩ (← currentDocName) refName
  | some ⟨uses⟩ =>
    modifyThe State fun st => {st with footnoteRefs := st.footnoteRefs.insert strName ⟨uses.push refName⟩}
    footnoteRefName ⟨genre⟩ (← currentDocName) refName


def PartElabM.push (fr : PartFrame) : PartElabM Unit := modifyThe State fun st => {st with partContext := st.partContext.push fr}

def PartElabM.debug (msg : String) : PartElabM Unit := do
  let st ← getThe State
  dbg_trace "DEBUG: {msg}"
  dbg_trace "  partContext: {repr st.partContext}"
  dbg_trace ""
  pure ()

/-- Custom info tree data to save the locations and identities of lists -/
structure DocListInfo where
  bullets : Array Syntax
  items : Array Syntax
deriving Repr, TypeName


def closes (openTok closeTok : Syntax) : DocElabM Unit := do
  let (.original _ pos _ _) := openTok.getHeadInfo
    | return ()
  let (.original ..) := closeTok.getHeadInfo
    | return ()
  let text ← getFileMap
  let {line, ..} := text.utf8PosToLspPos pos
  let lineStr := text.source.extract (text.lineStart (line + 1)) (text.lineStart (line + 2)) |>.trim
  let lineStr := if lineStr.startsWith "`" || lineStr.endsWith "`" then " " ++ lineStr ++ " " else lineStr
  Hover.addCustomHover closeTok (.markdown s!"Closes line {line + 1}: ``````````{lineStr}``````````")


abbrev InlineElab := Syntax → DocElabM Expr

initialize inlineElabAttr : KeyedDeclsAttribute InlineElab ←
  mkDocExpanderAttribute `inline_elab ``InlineElab "Indicates that this function elaborates inline elements of a given name" `inlineElabAttr

unsafe def inlineElabsForUnsafe (x : Name) : DocElabM (Array InlineElab) := do
  let expanders := inlineElabAttr.getEntries (← getEnv) x
  return expanders.map (·.value) |>.toArray

@[implemented_by inlineElabsForUnsafe]
opaque inlineElabsFor (x : Name) : DocElabM (Array InlineElab)


abbrev InlineExpander := Syntax → DocElabM (TSyntax `term)

initialize inlineExpanderAttr : KeyedDeclsAttribute InlineExpander ←
  mkDocExpanderAttribute `inline_expander ``InlineExpander "Indicates that this function expands inline elements of a given name" `inlineExpanderAttr

unsafe def inlineExpandersForUnsafe (x : Name) : DocElabM (Array InlineExpander) := do
  let expanders := inlineExpanderAttr.getEntries (← getEnv) x
  return expanders.map (·.value) |>.toArray

@[implemented_by inlineExpandersForUnsafe]
opaque inlineExpandersFor (x : Name) : DocElabM (Array InlineExpander)


abbrev BlockElab := Syntax → DocElabM Expr

initialize blockElabAttr : KeyedDeclsAttribute BlockElab ←
  mkDocExpanderAttribute `block_elab ``BlockElab "Indicates that this function expands block elements of a given name" `blockElabAttr

unsafe def blockElabsForUnsafe (x : Name) : DocElabM (Array BlockElab) := do
  let expanders := blockElabAttr.getEntries (← getEnv) x
  return expanders.map (·.value) |>.toArray

@[implemented_by blockElabsForUnsafe]
opaque blockElabsFor (x : Name) : DocElabM (Array BlockElab)


abbrev BlockExpander := Syntax → DocElabM (TSyntax `term)

initialize blockExpanderAttr : KeyedDeclsAttribute BlockExpander ←
  mkDocExpanderAttribute `block_expander ``BlockExpander "Indicates that this function expands block elements of a given name" `blockExpanderAttr

unsafe def blockExpandersForUnsafe (x : Name) : DocElabM (Array BlockExpander) := do
  let expanders := blockExpanderAttr.getEntries (← getEnv) x
  return expanders.map (·.value) |>.toArray

@[implemented_by blockExpandersForUnsafe]
opaque blockExpandersFor (x : Name) : DocElabM (Array BlockExpander)



abbrev PartCommand := Syntax → PartElabM Unit

initialize partCommandAttr : KeyedDeclsAttribute PartCommand ←
  mkDocExpanderAttribute `part_command ``PartCommand "Indicates that this function is used for side effects on the structure of the document" `partCommandAttr

unsafe def partCommandsForUnsafe (x : Name) : PartElabM (Array PartCommand) := do
  let expanders := partCommandAttr.getEntries (← getEnv) x
  return expanders.map (·.value) |>.toArray

@[implemented_by partCommandsForUnsafe]
opaque partCommandsFor (x : Name) : PartElabM (Array PartCommand)


abbrev RoleElab := Array Arg → TSyntaxArray `inline → DocElabM Expr

initialize roleElabAttr : KeyedDeclsAttribute RoleElab ←
  mkDocExpanderAttribute `role_elab ``RoleElab "Indicates that this function is used to elaborate a given role" `roleElabAttr

unsafe def roleElabsForUnsafe (x : Name) : DocElabM (Array RoleElab) := do
  let elabs := roleElabAttr.getEntries (← getEnv) x
  return elabs.map (·.value) |>.toArray

@[implemented_by roleElabsForUnsafe]
opaque roleElabsFor (x : Name) : DocElabM (Array RoleElab)


abbrev RoleExpander := Array Arg → TSyntaxArray `inline → DocElabM (Array (TSyntax `term))

initialize roleExpanderAttr : KeyedDeclsAttribute RoleExpander ←
  mkDocExpanderAttribute `role_expander ``RoleExpander "Indicates that this function is used to implement a given role" `roleExpanderAttr

unsafe def roleExpandersForUnsafe (x : Name) : DocElabM (Array RoleExpander) := do
  let expanders := roleExpanderAttr.getEntries (← getEnv) x
  return expanders.map (·.value) |>.toArray

@[implemented_by roleExpandersForUnsafe]
opaque roleExpandersFor (x : Name) : DocElabM (Array RoleExpander)


abbrev CodeBlockElab := Array Arg → TSyntax `str → DocElabM Expr

initialize codeBlockElabAttr : KeyedDeclsAttribute CodeBlockElab ←
  mkDocExpanderAttribute `code_block_elab ``CodeBlockElab "Indicates that this function is used to elaborate a given code block" `codeBlockElabAttr

unsafe def codeBlockElabsForUnsafe (x : Name) : DocElabM (Array CodeBlockElab) := do
  let elabs := codeBlockElabAttr.getEntries (← getEnv) x
  return elabs.map (·.value) |>.toArray

@[implemented_by codeBlockElabsForUnsafe]
opaque codeBlockElabsFor (x : Name) : DocElabM (Array CodeBlockElab)


abbrev CodeBlockExpander := Array Arg → TSyntax `str → DocElabM (Array (TSyntax `term))

initialize codeBlockExpanderAttr : KeyedDeclsAttribute CodeBlockExpander ←
  mkDocExpanderAttribute `code_block_expander ``CodeBlockExpander "Indicates that this function is used to implement a given code block" `codeBlockExpanderAttr

unsafe def codeBlockExpandersForUnsafe (x : Name) : DocElabM (Array CodeBlockExpander) := do
  let expanders := codeBlockExpanderAttr.getEntries (← getEnv) x
  return expanders.map (·.value) |>.toArray

@[implemented_by codeBlockExpandersForUnsafe]
opaque codeBlockExpandersFor (x : Name) : DocElabM (Array CodeBlockExpander)


abbrev DirectiveElab := Array Arg → TSyntaxArray `block → DocElabM Expr

initialize directiveElabAttr : KeyedDeclsAttribute DirectiveElab ←
  mkDocExpanderAttribute `directive_elab ``DirectiveElab "Indicates that this function is used to elaborate a given directive" `directiveElabAttr

unsafe def directiveElabsForUnsafe (x : Name) : DocElabM (Array DirectiveElab) := do
  let expanders := directiveElabAttr.getEntries (← getEnv) x
  return expanders.map (·.value) |>.toArray

@[implemented_by directiveElabsForUnsafe]
opaque directiveElabsFor (x : Name) : DocElabM (Array DirectiveElab)


abbrev DirectiveExpander := Array Arg → TSyntaxArray `block → DocElabM (Array (TSyntax `term))

initialize directiveExpanderAttr : KeyedDeclsAttribute DirectiveExpander ←
  mkDocExpanderAttribute `directive_expander ``DirectiveExpander "Indicates that this function is used to implement a given directive" `directiveExpanderAttr

unsafe def directiveExpandersForUnsafe (x : Name) : DocElabM (Array DirectiveExpander) := do
  let expanders := directiveExpanderAttr.getEntries (← getEnv) x
  return expanders.map (·.value) |>.toArray

@[implemented_by directiveExpandersForUnsafe]
opaque directiveExpandersFor (x : Name) : DocElabM (Array DirectiveExpander)


abbrev BlockRoleElab := Array Arg → Array Syntax → DocElabM Expr

initialize blockRoleElabAttr : KeyedDeclsAttribute BlockRoleElab ←
  mkDocExpanderAttribute `block_role_elab ``BlockRoleElab "Indicates that this function is used to implement a given blockRole" `blockRoleElabAttr

unsafe def blockRoleElabsForUnsafe (x : Name) : DocElabM (Array BlockRoleElab) := do
  let elabs := blockRoleElabAttr.getEntries (← getEnv) x
  return elabs.map (·.value) |>.toArray

@[implemented_by blockRoleElabsForUnsafe]
opaque blockRoleElabsFor (x : Name) : DocElabM (Array BlockRoleElab)



abbrev BlockRoleExpander := Array Arg → Array Syntax → DocElabM (Array (TSyntax `term))

initialize blockRoleExpanderAttr : KeyedDeclsAttribute BlockRoleExpander ←
  mkDocExpanderAttribute `block_role_expander ``BlockRoleExpander "Indicates that this function is used to implement a given blockRole" `blockRoleExpanderAttr

unsafe def blockRoleExpandersForUnsafe (x : Name) : DocElabM (Array BlockRoleExpander) := do
  let expanders := blockRoleExpanderAttr.getEntries (← getEnv) x
  return expanders.map (·.value) |>.toArray

@[implemented_by blockRoleExpandersForUnsafe]
opaque blockRoleExpandersFor (x : Name) : DocElabM (Array BlockRoleExpander)
