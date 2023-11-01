import Lean
import LeanDoc.Doc
import LeanDoc.Doc.Elab.ExpanderAttribute
import LeanDoc.Doc.Elab.InlineString
import LeanDoc.SyntaxUtils

namespace LeanDoc.Doc.Elab

open Lean Elab
open LeanDoc.SyntaxUtils

-- For use in IDE features and previews and such
@[inline_to_string LeanDoc.Syntax.text]
def _root_.LeanDoc.Syntax.text.inline_to_string : InlineToString
  | _, `<low|(LeanDoc.Syntax.text ~(.atom _ s))> => some s
  | _, _ => none

@[inline_to_string LeanDoc.Syntax.linebreak]
def _root_.LeanDoc.Syntax.linebreak.inline_to_string : InlineToString
  | _, `<low|(LeanDoc.Syntax.linebreak ~_ )> => some " "
  | _, _ => none

@[inline_to_string LeanDoc.Syntax.emph]
def _root_.LeanDoc.Syntax.emph.inline_to_string : InlineToString
  | env, `<low|(LeanDoc.Syntax.emph ~_open ~(.node _ `null args) ~_close)> =>
    some <| String.intercalate " " (Array.map (inlineToString env) args).toList
  | _, _ => none

@[inline_to_string LeanDoc.Syntax.bold]
def _root_.LeanDoc.Syntax.bold.inline_to_string : InlineToString
  | env, `<low|(LeanDoc.Syntax.bold ~_open ~(.node _ `null args) ~_close)> =>
    some <| String.intercalate " " (Array.map (inlineToString env) args).toList
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
  | `<low|(LeanDoc.Syntax.header ~(.atom _ _hashes ) ~(.node _ `null inlines) ) > => inlinesToString env inlines
  | headerStx => dbg_trace "didn't understand {headerStx} for string"
    "<missing>"

inductive TOC where
  | mk (title : String) (titleSyntax : Syntax) (endPos : String.Pos) (children : Array TOC)
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
  | mk (titleSyntax : Syntax) (expandedTitle : Array (TSyntax `term)) (titlePreview : String) (blocks : Array (TSyntax `term)) (subParts : Array FinishedPart) (endPos : String.Pos)
deriving Repr, BEq

partial def FinishedPart.toSyntax [Monad m] [MonadQuotation m] : FinishedPart → m (TSyntax `term)
  | .mk _titleStx titleInlines _titleString blocks subParts _endPos => do
    let subStx ← subParts.mapM toSyntax
    ``(Part.mk #[$[$titleInlines],*] #[$[$blocks],*] #[$[$subStx],*])

partial def FinishedPart.toTOC : FinishedPart → TOC
  | .mk titleStx _titleInlines titleString _blocks subParts endPos =>
    .mk titleString titleStx endPos (subParts.map toTOC)

structure PartFrame where
  titleSyntax : Syntax
  expandedTitle : Option (String × Array (TSyntax `term)) := none
  blocks : Array (TSyntax `term)
  priorParts : Array FinishedPart
deriving Repr

def PartFrame.close (fr : PartFrame) (endPos : String.Pos) : FinishedPart :=
  let (titlePreview, titleInlines) := fr.expandedTitle.getD ("<anonymous>", #[])
  .mk fr.titleSyntax titleInlines titlePreview fr.blocks fr.priorParts endPos

structure PartContext extends PartFrame where
  parents : Array PartFrame
deriving Repr

def PartContext.level (ctxt : PartContext) : Nat := ctxt.parents.size
def PartContext.close (ctxt : PartContext) (endPos : String.Pos) : Option PartContext := do
  let fr ← ctxt.parents.back?
  pure {
    parents := ctxt.parents.pop,
    blocks := fr.blocks,
    titleSyntax := fr.titleSyntax,
    expandedTitle := fr.expandedTitle,
    priorParts := fr.priorParts.push <| ctxt.toPartFrame.close endPos
  }

def PartContext.push (ctxt : PartContext) (fr : PartFrame) : PartContext := ⟨fr, ctxt.parents.push ctxt.toPartFrame⟩

structure PartElabM.State where
  partContext : PartContext
deriving Repr


def PartElabM.State.init (title : Syntax) (expandedTitle : Option (String × Array (TSyntax `term)) := none) : PartElabM.State where
  partContext := {titleSyntax := title, expandedTitle, blocks := #[], priorParts := #[], parents := #[]}

def PartElabM (α : Type) : Type := StateT PartElabM.State TermElabM α

def PartElabM.run (st : PartElabM.State) (act : PartElabM α) : TermElabM (α × PartElabM.State) :=
  StateT.run act st


instance : MonadRef PartElabM := inferInstanceAs <| MonadRef (StateT PartElabM.State TermElabM)

instance : MonadQuotation PartElabM := inferInstanceAs <| MonadQuotation (StateT PartElabM.State TermElabM)

instance : Monad PartElabM := inferInstanceAs <| Monad (StateT PartElabM.State TermElabM)

instance : MonadLift TermElabM PartElabM := inferInstanceAs <| MonadLift TermElabM (StateT PartElabM.State TermElabM)

instance : MonadExceptOf Exception PartElabM := inferInstanceAs <| MonadExceptOf Exception (StateT PartElabM.State TermElabM)

instance : MonadState PartElabM.State PartElabM := inferInstanceAs <| MonadState PartElabM.State (StateT PartElabM.State TermElabM)

instance : MonadStateOf PartElabM.State PartElabM := inferInstanceAs <| MonadStateOf PartElabM.State (StateT PartElabM.State TermElabM)

instance : MonadStateOf PartElabM.State PartElabM := inferInstanceAs <| MonadStateOf PartElabM.State (StateT PartElabM.State TermElabM)

instance : MonadFinally PartElabM := inferInstanceAs <| MonadFinally (StateT PartElabM.State TermElabM)

instance : MonadRef PartElabM := inferInstanceAs <| MonadRef (StateT PartElabM.State TermElabM)

def DocElabM (α : Type) : Type := ReaderT PartElabM.State TermElabM α

def DocElabM.run (st : PartElabM.State) (act : DocElabM α) : TermElabM α :=
  ReaderT.run act st

instance : MonadRef DocElabM := inferInstanceAs <| MonadRef (ReaderT PartElabM.State TermElabM)

instance : MonadQuotation DocElabM := inferInstanceAs <| MonadQuotation (ReaderT PartElabM.State TermElabM)

instance : Monad DocElabM := inferInstanceAs <| Monad (ReaderT PartElabM.State TermElabM)

instance : MonadLift TermElabM DocElabM := inferInstanceAs <| MonadLift TermElabM (ReaderT PartElabM.State TermElabM)

instance : MonadExceptOf Exception DocElabM := inferInstanceAs <| MonadExceptOf Exception (ReaderT PartElabM.State TermElabM)

instance : MonadReader PartElabM.State DocElabM := inferInstanceAs <| MonadReader PartElabM.State (ReaderT PartElabM.State TermElabM)

instance : MonadReaderOf PartElabM.State DocElabM := inferInstanceAs <| MonadReaderOf PartElabM.State (ReaderT PartElabM.State TermElabM)

instance : MonadReaderOf PartElabM.State DocElabM := inferInstanceAs <| MonadReaderOf PartElabM.State (ReaderT PartElabM.State TermElabM)

instance : MonadFinally DocElabM := inferInstanceAs <| MonadFinally (ReaderT PartElabM.State TermElabM)

instance : MonadRecDepth DocElabM := inferInstanceAs <| MonadRecDepth (ReaderT PartElabM.State TermElabM)

def PartElabM.liftDocElabM (act : DocElabM α) : PartElabM α := do act.run (← get)

instance : MonadLift DocElabM PartElabM := ⟨PartElabM.liftDocElabM⟩

def PartElabM.currentLevel : PartElabM Nat := do return (← get).partContext.level

def PartElabM.setTitle (titlePreview : String) (titleInlines : Array (TSyntax `term)) : PartElabM Unit := modify fun st =>
  {st with partContext.expandedTitle := some (titlePreview, titleInlines)}

def PartElabM.addBlock (block : TSyntax `term) : PartElabM Unit := modify fun st =>
  {st with partContext.blocks := st.partContext.blocks.push block}

def PartElabM.push (fr : PartFrame) : PartElabM Unit := modify fun st => {st with partContext := st.partContext.push fr}

def PartElabM.debug (msg : String) : PartElabM Unit := do
  let st ← get
  dbg_trace "DEBUG: {msg}"
  dbg_trace "  partContext: {repr st.partContext}"
  dbg_trace ""
  pure ()

/-- Custom info tree data to save the locations and identities of lists -/
structure DocListInfo where
  bullets : Array Syntax
deriving Repr, TypeName



abbrev InlineExpander := Syntax → DocElabM (TSyntax `term)

initialize inlineExpanderAttr : KeyedDeclsAttribute InlineExpander ←
  mkDocExpanderAttribute `inline_expander ``InlineExpander "Indicates that this function expands inline elements of a given name" `inlineExpanderAttr

unsafe def inlineExpandersForUnsafe (x : Name) : DocElabM (Array InlineExpander) := do
  let expanders := inlineExpanderAttr.getEntries (← getEnv) x
  return expanders.map (·.value) |>.toArray

@[implemented_by inlineExpandersForUnsafe]
opaque inlineExpandersFor (x : Name) : DocElabM (Array InlineExpander)



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
