/-
Copyright (c) 2023-2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import Std.Data.HashMap
import Std.Data.HashSet

import Lean.Elab.DeclUtil
import Lean.Meta.Reduce
import Lean.DocString.Syntax

import Verso.Doc
import Verso.Doc.ArgParse
import Verso.Doc.Elab.InlineString
import Verso.Doc.Elab.Basic

set_option doc.verso true

namespace Verso.Doc.Elab

open Lean
open Lean.Elab
open Lean.Doc.Syntax
open Std (HashMap HashSet)
open Verso.ArgParse (FromArgs SigDoc)

initialize registerTraceClass `Elab.Verso
initialize registerTraceClass `Elab.Verso.part
initialize registerTraceClass `Elab.Verso.block

class HasLink (name : String) (doc : Name) where
  url : String

class HasNote (name : String) (doc : Name) (genre : Genre) where
  contents : Array (Inline genre)

private def linkRefName [Monad m] [MonadQuotation m] (docName : Name) (ref : TSyntax `str) : m Term := do
  ``(HasLink.url $(quote ref.getString) $(quote docName) (self := _))

private def footnoteRefName [Monad m] [MonadQuotation m] (genre : Term) (docName : Name) (ref : TSyntax `str) : m Term :=
  ``(HasNote.contents $(quote ref.getString) $(quote docName) (genre := $genre) (self := _))


-- For use in IDE features and previews and such
@[inline_to_string Lean.Doc.Syntax.text]
def _root_.Lean.Doc.Syntax.text.inline_to_string : InlineToString
  | _, `(inline| $s:str) => some s.getString
  | _, _ => none

@[inline_to_string Lean.Doc.Syntax.linebreak]
def _root_.Lean.Doc.Syntax.linebreak.inline_to_string : InlineToString
  | _, `(inline|line! $_) => some " "
  | _, _ => none

@[inline_to_string Lean.Doc.Syntax.emph]
def _root_.Lean.Doc.Syntax.emph.inline_to_string : InlineToString
  | env, `(inline| _[ $args* ]) =>
    some <| String.intercalate " " (Array.map (inlineToString env) args).toList
  | _, _ => none

@[inline_to_string Lean.Doc.Syntax.bold]
def _root_.Lean.Doc.Syntax.bold.inline_to_string : InlineToString
  | env, `(inline| *[ $args* ]) =>
    some <| String.intercalate " " (Array.map (inlineToString env) args).toList
  | _, _ => none

@[inline_to_string Lean.Doc.Syntax.code]
def _root_.Lean.Doc.Syntax.code.inline_to_string : InlineToString
  | _, `(inline| code( $str )) =>
    some str.getString
  | _, _ => none

@[inline_to_string Lean.Doc.Syntax.role]
def _root_.Lean.Doc.Syntax.role.inline_to_string : InlineToString
  | env, `(inline| role{ $_ $_* }[ $body* ]) =>
    String.join (body.toList.map (inlineToString env <| ·.raw))
  | _, _ => none

@[inline_to_string null]
def nullInline_to_string : InlineToString
  | env, .node _ _ contents =>
    return String.join <| contents.toList.map (inlineToString env)
  | _, _ => none

@[inline_to_string Lean.Parser.Term.app]
def app_to_string : InlineToString := fun (env : Environment) => fun
  | `(Verso.Doc.Inline.text $s:str) =>
    return s.getString
  | `(Verso.Doc.Inline.concat #[$xs,*]) =>
    return String.join <| (xs : Array _).toList.map (inlineToString env)
  | _ => none

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

structure DocElabContext where
  genreSyntax : Syntax
  genre : Expr

  /--
  When this is false, a footnote ref like `[^note]` or a link ref like {lit}`[wikipedia]` will be
  treated as an error if the current {lit}`PartElabM` state does not contain a definition for the
  ref.

  When this is true, undefined references in inline text will be ignored until a later time.
  -/
  allowUndefinedRefs : Bool
deriving Inhabited

def DocElabContext.fromGenreTerm (genreSyntax : Term) : TermElabM DocElabContext := do
  let genre ← Term.elabTerm genreSyntax (some (.const ``Doc.Genre []))
  return DocElabContext.mk genreSyntax genre true

structure DocElabM.State where
  linkRefs : HashMap String DocUses := {}
  footnoteRefs : HashMap String DocUses := {}
deriving Inhabited

structure PartElabM.State where
  partContext : PartContext
  linkDefs : HashMap String (DocDef String) := {}
  footnoteDefs : HashMap String (DocDef (Array (TSyntax `term))) := {}
deriving Inhabited

def PartElabM.State.init (title : Syntax) (expandedTitle : Option (String × Array (TSyntax `term)) := none) : PartElabM.State where
  partContext := {titleSyntax := title, expandedTitle, metadata := none, blocks := #[], priorParts := #[], parents := #[]}

/--
Top-level document elaboration monad. Can modify both DocElabM.State and PartElabM.State
-/
def PartElabM (α : Type) : Type := ReaderT DocElabContext (StateT DocElabM.State (StateT PartElabM.State TermElabM)) α

def PartElabM.run (ctx : DocElabContext) (st : DocElabM.State) (st' : PartElabM.State) (act : PartElabM α) : TermElabM (α × DocElabM.State × PartElabM.State) := do
  let ((res, st), st') ← act ctx st st'
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

instance : MonadWithReaderOf DocElabContext PartElabM := inferInstanceAs <| MonadWithReaderOf DocElabContext (ReaderT DocElabContext (StateT DocElabM.State (StateT PartElabM.State TermElabM)))

instance : MonadReaderOf DocElabContext PartElabM := inferInstanceAs <| MonadReaderOf DocElabContext (ReaderT DocElabContext (StateT DocElabM.State (StateT PartElabM.State TermElabM)))

instance : MonadWithOptions PartElabM := inferInstanceAs <| MonadWithOptions (ReaderT DocElabContext (StateT DocElabM.State (StateT PartElabM.State TermElabM)))

def PartElabM.withFileMap (fileMap : FileMap) (act : PartElabM α) : PartElabM α :=
  fun ρ ρ' σ ctxt σ' mctxt rw cctxt => act ρ ρ' σ ctxt σ' mctxt rw {cctxt with fileMap := fileMap}

def withAllowUndefinedRefs [MonadWithReaderOf DocElabContext m] [Monad m] (b : Bool) : m a → m a :=
  withTheReader DocElabContext ({ · with allowUndefinedRefs := b})

/--
Text elaboration monad.

This monad can produce content, but it can't modify the structure of the surrounding document. It
can observe this structure, however.

This means it can modify the {lean}`DocElabM.State`, but it can only read from the
{lean}`PartElabM.State`.
-/
def DocElabM (α : Type) : Type := ReaderT DocElabContext (ReaderT PartElabM.State (StateT DocElabM.State TermElabM)) α

def DocElabM.run (ctx : DocElabContext) (st : DocElabM.State) (st' : PartElabM.State) (act : DocElabM α) : TermElabM (α × DocElabM.State) := do
  StateT.run (act ctx st') st

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
  let (out, stDoc) ← act.run (← readThe DocElabContext) (← getThe DocElabM.State) (← getThe PartElabM.State)
  modifyThe DocElabM.State (fun _ => stDoc)
  pure out

instance : MonadLift DocElabM PartElabM := ⟨PartElabM.liftDocElabM⟩

def PartElabM.State.currentLevel (state : PartElabM.State) : Nat := state.partContext.level

def PartElabM.currentLevel : PartElabM Nat := do return (← getThe State).currentLevel

def PartElabM.setTitle (titlePreview : String) (titleInlines : Array (TSyntax `term)) : PartElabM Unit := modifyThe State fun st =>
  {st with partContext.expandedTitle := some (titlePreview, titleInlines)}

/--
Traverses the Expr structure to find and list MVars that represent undefined links or footnotes.
It is a simplifying precondition that instantiateMVars has just been called on the argument.
-/
def findTypeclassInstances : Expr → MetaM (Array (Expr × Expr))
  | .app t1 t2 => do return (← findTypeclassInstances t1) ++ (← findTypeclassInstances t2)
  | e@(.mvar _) => do
    let ty ← Meta.inferType e
    if ty.isAppOf ``HasLink || ty.isAppOf ``HasNote then
      pure #[(e, ty)]
    else
      pure #[]
  | .lam _ t b _ | .forallE _ t b _ => do return (← findTypeclassInstances t) ++ (← findTypeclassInstances b)
  | .letE _ t d b _ => do
    return (← findTypeclassInstances t) ++ (← findTypeclassInstances d) ++ (← findTypeclassInstances b)
  | .mdata _ e | .proj _ _ e => findTypeclassInstances e
  | .sort .. | .fvar .. | .bvar .. | .const .. | .lit .. => pure #[]

def PartElabM.addBlock (block : TSyntax `term) : PartElabM Unit := withRef block <| do
  let genre := (← readThe DocElabContext).genre

  let mut type := .app (.const ``Doc.Block []) genre
  let mut blockExpr ← Term.elabTerm block (some type)

  -- Find links and footnotes by traversing blockExpr
  -- It simplifies the logic of findTypeclassInstances to have the MVars freshly instantiated
  blockExpr ← instantiateMVars blockExpr
  let links ← findTypeclassInstances blockExpr

  -- Wrap the type and corresponding expression in binders for the links and notes
  type ← Meta.mkForallFVars (links.map (·.1)) type (binderInfoForMVars := .instImplicit)
  blockExpr ← links.foldrM (init := blockExpr) fun (mv, mvty) t =>
    (.lam `inst mvty · .instImplicit) <$> t.abstractM #[mv]

  -- Wrap auto-bound implicits and global variables (this is possibly overly defensive)
  type ← Meta.mkForallFVars (← Term.addAutoBoundImplicits #[] none) type

  -- Replace any universe metavariables with universe variables; report errors
  type ← Term.levelMVarToParam type
  match sortDeclLevelParams [] [] (collectLevelParams {} type |>.params) with
  | Except.error msg      => throwErrorAt block msg
  | Except.ok levelParams =>
    Term.synthesizeSyntheticMVarsNoPostponing
    type ← instantiateMVars type
    blockExpr ← Term.ensureHasType (some type) (← instantiateMVars blockExpr)
    let name ← mkFreshUserName `block
    let decl := Declaration.defnDecl {
      name,
      levelParams,
      type,
      value := blockExpr,
      hints := .abbrev,
      safety := .safe
    }

    -- This is possibly overly defensive (or ineffectual)
    Term.ensureNoUnassignedMVars decl
    addAndCompile decl
    modifyThe PartElabM.State fun st =>
      { st with partContext.blocks := st.partContext.blocks.push (mkIdent name) }


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
    throwErrorAt refName "Already defined link [{strName}] as '{url'}'"

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
  let genre := (← readThe DocElabContext).genre
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
  | some _ =>
    throwErrorAt refName m!"Already defined footnote [^{strName}]"

def DocElabM.addFootnoteRef (refName : TSyntax `str) : DocElabM (TSyntax `term) := do
  let strName := refName.getString
  let genre := (← readThe DocElabContext).genreSyntax
  if !(← readThe DocElabContext).allowUndefinedRefs && !(← readThe PartElabM.State).footnoteDefs.contains strName then
    throwErrorAt refName m!"Footnote reference [^{strName}] is not defined yet when it occurs"
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


def closes (openTok closeTok : Syntax) : DocElabM Unit := do
  let (.original _ pos _ _) := openTok.getHeadInfo
    | return ()
  let (.original ..) := closeTok.getHeadInfo
    | return ()
  let text ← getFileMap
  let {line, ..} := text.utf8PosToLspPos pos
  let lineStr := (text.lineStart (line + 1)).extract text.source  (text.lineStart (line + 2)) |>.trim
  let lineStr := if lineStr.startsWith "`" || lineStr.endsWith "`" then " " ++ lineStr ++ " " else lineStr
  Hover.addCustomHover closeTok (.markdown s!"Closes line {line + 1}: ``````````{lineStr}``````````")



abbrev InlineExpander := Syntax → DocElabM (TSyntax `term)

initialize inlineExpanderAttr : KeyedDeclsAttribute InlineExpander ←
  mkDocExpanderAttribute `inline_expander ``InlineExpander "Indicates that this function expands inline elements of a given name" `inlineExpanderAttr

unsafe def inlineExpandersForUnsafe (x : Name) : DocElabM (Array InlineExpander) := do
  let expanders := inlineExpanderAttr.getEntries (← getEnv) x
  return expanders.map (·.value) |>.toArray

@[implemented_by inlineExpandersForUnsafe]
opaque inlineExpandersFor (x : Name) : DocElabM (Array InlineExpander)


/--
Creates a term denoting a {lean}`VersoDoc` value from a {lean}`FinishedPart`. This is the final step
in turning a parsed verso doc into syntax.
-/
def FinishedPart.toVersoDoc [Monad m] [MonadQuotation m] [MonadError m] [MonadLog m] [AddMessageContext m] [MonadOptions m]
    (genreSyntax : Term)
    (finished : FinishedPart)
    (docElabState : DocElabM.State)
    (partElabState : PartElabM.State)
    : m Term := do

  for (ref, uses) in docElabState.footnoteRefs do
    if !partElabState.footnoteDefs.contains ref then
      for use in uses.useSites do
        throwErrorAt use m!"No definition for footnote [^{ref}]"
  for (ref, site) in partElabState.footnoteDefs do
    if !docElabState.footnoteRefs.contains ref then
      logWarningAt site.defSite m!"Unused footnote [^{ref}]"

  for (ref, uses) in docElabState.linkRefs do
    if !partElabState.linkDefs.contains ref then
      for use in uses.useSites do
        throwErrorAt use m!"No definition for link [{ref}]"
  for (ref, site) in partElabState.linkDefs do
    if !docElabState.linkRefs.contains ref then
      logWarningAt site.defSite m!"Unused link [{ref}]"

  let finishedSyntax ← finished.toSyntax genreSyntax
  ``(VersoDoc.mk (fun () => $finishedSyntax))


abbrev BlockExpander := Syntax → DocElabM (TSyntax `term)

initialize blockExpanderAttr : KeyedDeclsAttribute BlockExpander ←
  mkDocExpanderAttribute `block_expander ``BlockExpander "Indicates that this function expands block elements of a given name" `blockExpanderAttr

unsafe def blockExpandersForUnsafe (x : Name) : DocElabM (Array BlockExpander) := do
  let expanders := blockExpanderAttr.getEntries (← getEnv) x
  return expanders.map (·.value) |>.toArray

@[implemented_by blockExpandersForUnsafe]
opaque blockExpandersFor (x : Name) : DocElabM (Array BlockExpander)

initialize expanderSignatureExt : PersistentEnvExtension (Name × SigDoc) (Name × SigDoc) (NameMap SigDoc) ←
  registerPersistentEnvExtension {
    mkInitial := pure {},
    addImportedFn xss :=
      pure <| xss.foldl (init := {}) fun ns xs =>
        xs.foldl (init := ns) fun ns (x, s) =>
          ns.insert x s
    addEntryFn
      | xs, (x, y) =>
        xs.insert x y
    exportEntriesFn xs :=
      xs.toArray
  }

private def sig (α) [inst : FromArgs α DocElabM] : Option ArgParse.SigDoc :=
  inst.fromArgs.signature

abbrev PartCommand := Syntax → PartElabM Unit

initialize partCommandAttr : KeyedDeclsAttribute PartCommand ←
  mkDocExpanderAttribute `part_command ``PartCommand "Indicates that this function is used for side effects on the structure of the document" `partCommandAttr

unsafe def partCommandsForUnsafe (x : Name) : PartElabM (Array PartCommand) := do
  let expanders := partCommandAttr.getEntries (← getEnv) x
  return expanders.map (·.value) |>.toArray

@[implemented_by partCommandsForUnsafe]
opaque partCommandsFor (x : Name) : PartElabM (Array PartCommand)


abbrev RoleExpander := Array Arg → TSyntaxArray `inline → DocElabM (Array (TSyntax `term))

abbrev RoleExpanderOf α := α → TSyntaxArray `inline → DocElabM Term

initialize roleExpanderAttr : KeyedDeclsAttribute RoleExpander ←
  mkDocExpanderAttribute `role_expander ``RoleExpander "Indicates that this function is used to implement a given role" `roleExpanderAttr

private def toRole {α : Type} [FromArgs α DocElabM] (expander : α → TSyntaxArray `inline → DocElabM Term) : RoleExpander :=
  fun args inlines => do
    let v ← ArgParse.parse args
    return #[← expander v inlines]

syntax (name := role) "role " (ident)? : attr


initialize roleExpanderExt : PersistentEnvExtension (Name × Array Name) (Name × Name) (NameMap (Array Name)) ←
  registerPersistentEnvExtension {
    mkInitial := pure {},
    addImportedFn xss :=
      pure <| xss.foldl (init := {}) fun ns xs =>
        xs.foldl (init := ns) fun ns (x, ys) =>
          ns.insert x <| (ns.find? x |>.getD #[]) ++ ys
    addEntryFn
      | xs, (x, y) =>
        xs.insert x (xs.find? x |>.getD #[] |>.push y)
    exportEntriesFn xs :=
      xs.toArray
  }

private unsafe def roleExpandersForUnsafe' (x : Name) : DocElabM (Array (RoleExpander × Option String × Option SigDoc)) := do
  let expanders := roleExpanderExt.getState (← getEnv) |>.find? x |>.getD #[]
  expanders.mapM fun n => do
    let e ← evalConst RoleExpander n
    let doc? ← findDocString? (← getEnv) n
    let sig := expanderSignatureExt.getState (← getEnv) |>.find? n
    return (e, doc?, sig)

private unsafe def roleExpandersForUnsafe'' (x : Name) : DocElabM (Array RoleExpander) := do
  let expanders := roleExpanderAttr.getEntries (← getEnv) x
  return expanders.map (·.value) |>.toArray

private unsafe def roleExpandersForUnsafe (x : Name) : DocElabM (Array (RoleExpander × Option String × Option SigDoc)) := do
  return (← roleExpandersForUnsafe' x) ++ (← roleExpandersForUnsafe'' x).map (·, none, none)

@[implemented_by roleExpandersForUnsafe]
opaque roleExpandersFor (x : Name) : DocElabM (Array (RoleExpander × Option String × Option SigDoc))

private unsafe def evalIOOptStringUnsafe (x : Name) : MetaM (Option SigDoc) := do
  evalConst (Option SigDoc) x

@[implemented_by evalIOOptStringUnsafe]
private opaque evalOptMsg (x : Name) : MetaM (Option SigDoc)

private def saveSignature (expanderName : Name) (argTy : Expr) : MetaM Unit := do
  let s ← Meta.mkAppM ``sig #[argTy]
  let inst ← Meta.synthInstance (mkApp2 (.const ``FromArgs []) argTy (.const ``DocElabM []))
  let s := .app s inst
  let s ← instantiateExprMVars s
  let s ← Meta.whnf s
  let name ← mkFreshUserName <| expanderName ++ `signature
  addAndCompile <| .defnDecl {
    name,
    levelParams := [],
    type := .app (.const ``Option [0]) (.const ``SigDoc []),
    value := s,
    hints := .opaque,
    safety := .safe
  }
  let str? ← evalOptMsg name
  if let some str := str? then
    modifyEnv (expanderSignatureExt.addEntry · (expanderName, str))

unsafe initialize registerBuiltinAttribute {
  name := `role,
  descr := "Define a new role",
  applicationTime := .afterCompilation,
  add declName stx k := do
    unless k == .global do throwError m!"Must be `global`"
    let roleName ←
      match stx with
      | `(attr|role) => pure declName
      | `(attr|role $x) => realizeGlobalConstNoOverloadWithInfo x
      | _ => throwError "Invalid `role` attribute"

    let n ← mkFreshUserName <| declName ++ `role

    let ((e, t), _) ← Meta.MetaM.run (ctx := {}) (s := {}) do
      let e ← Meta.mkAppM ``toRole #[.const declName []]
      let e ← instantiateMVars e
      let t ← Meta.inferType e


      match_expr e with
      | toRole ty _ _ => saveSignature n ty
      | _ => pure ()

      pure (e, t)

    addAndCompile <| .defnDecl {
      name := n,
      levelParams := [],
      type := t,
      value := e,
      hints := .opaque,
      safety := .safe
    }

    addDocStringCore' n (← findSimpleDocString? (← getEnv) declName)

    modifyEnv fun env =>
      roleExpanderExt.addEntry env (roleName, n)
}


abbrev CodeBlockExpander := Array Arg → TSyntax `str → DocElabM (Array (TSyntax `term))

abbrev CodeBlockExpanderOf α := α → StrLit → DocElabM Term


initialize codeBlockExpanderAttr : KeyedDeclsAttribute CodeBlockExpander ←
  mkDocExpanderAttribute `code_block_expander ``CodeBlockExpander "Indicates that this function is used to implement a given code block" `codeBlockExpanderAttr

private def toCodeBlock {α : Type} [FromArgs α DocElabM] (expander : α → StrLit → DocElabM Term) : CodeBlockExpander :=
  fun args str => do
    let v ← ArgParse.parse args
    return #[← expander v str]

syntax (name := code_block) "code_block " (ident)? : attr

initialize codeBlockExpanderExt : PersistentEnvExtension (Name × Array Name) (Name × Name) (NameMap (Array Name)) ←
  registerPersistentEnvExtension {
    mkInitial := pure {},
    addImportedFn xss :=
      pure <| xss.foldl (init := {}) fun ns xs =>
        xs.foldl (init := ns) fun ns (x, ys) =>
          ns.insert x <| (ns.find? x |>.getD #[]) ++ ys
    addEntryFn
      | xs, (x, y) =>
        xs.insert x (xs.find? x |>.getD #[] |>.push y)
    exportEntriesFn xs :=
      xs.toArray
  }

unsafe initialize registerBuiltinAttribute {
  name := `code_block,
  descr := "Define a new code_block",
  applicationTime := .afterCompilation,
  add declName stx k := do
    unless k == .global do throwError m!"Must be `global`"
    let blockName ←
      match stx with
      | `(attr|code_block) => pure declName
      | `(attr|code_block $x) => realizeGlobalConstNoOverloadWithInfo x
      | _ => throwError "Invalid `code_block` attribute"

    let n ← mkFreshUserName <| declName ++ `code_block

    let ((e, t), _) ← Meta.MetaM.run (ctx := {}) (s := {}) do
      let e ← Meta.mkAppM ``toCodeBlock #[.const declName []]
      let e ← instantiateMVars e
      let t ← Meta.inferType e


      match_expr e with
      | toCodeBlock ty _ _ => saveSignature n ty
      | _ => pure ()

      pure (e, t)

    addAndCompile <| .defnDecl {
      name := n,
      levelParams := [],
      type := t,
      value := e,
      hints := .opaque,
      safety := .safe
    }

    addDocStringCore' n (← findSimpleDocString? (← getEnv) declName)

    modifyEnv fun env =>
      codeBlockExpanderExt.addEntry env (blockName, n)
}

private unsafe def codeBlockExpandersForUnsafe' (x : Name) : DocElabM (Array (CodeBlockExpander × Option String × Option SigDoc)) := do
  let expanders := codeBlockExpanderExt.getState (← getEnv) |>.find? x |>.getD #[]
  expanders.mapM fun n => do
    let e ← evalConst CodeBlockExpander n
    let doc? ← findDocString? (← getEnv) n
    let sig := expanderSignatureExt.getState (← getEnv) |>.find? n
    return (e, doc?, sig)

private unsafe def codeBlockExpandersForUnsafe'' (x : Name) : DocElabM (Array CodeBlockExpander) := do
  let expanders := codeBlockExpanderAttr.getEntries (← getEnv) x
  return expanders.map (·.value) |>.toArray

private unsafe def codeBlockExpandersForUnsafe (x : Name) : DocElabM (Array (CodeBlockExpander × Option String × Option SigDoc)) := do
  return (← codeBlockExpandersForUnsafe' x) ++ (← codeBlockExpandersForUnsafe'' x).map (·, none, none)

@[implemented_by codeBlockExpandersForUnsafe]
opaque codeBlockExpandersFor (x : Name) : DocElabM (Array (CodeBlockExpander × Option String × Option SigDoc))

abbrev DirectiveExpander := Array Arg → TSyntaxArray `block → DocElabM (Array (TSyntax `term))

abbrev DirectiveExpanderOf α := α → TSyntaxArray `block → DocElabM Term


initialize directiveExpanderAttr : KeyedDeclsAttribute DirectiveExpander ←
  mkDocExpanderAttribute `directive_expander ``DirectiveExpander "Indicates that this function is used to implement a given directive" `directiveExpanderAttr

private def toDirective {α : Type} [FromArgs α DocElabM] (expander : α → TSyntaxArray `block → DocElabM Term) : DirectiveExpander :=
  fun args blocks => do
    let v ← ArgParse.parse args
    return #[← expander v blocks]

syntax (name := directive) "directive " (ident)? : attr

initialize directiveExpanderExt : PersistentEnvExtension (Name × Array Name) (Name × Name) (NameMap (Array Name)) ←
  registerPersistentEnvExtension {
    mkInitial := pure {},
    addImportedFn xss :=
      pure <| xss.foldl (init := {}) fun ns xs =>
        xs.foldl (init := ns) fun ns (x, ys) =>
          ns.insert x <| (ns.find? x |>.getD #[]) ++ ys
    addEntryFn
      | xs, (x, y) =>
        xs.insert x (xs.find? x |>.getD #[] |>.push y)
    exportEntriesFn xs :=
      xs.toArray
  }

unsafe initialize registerBuiltinAttribute {
  name := `directive,
  descr := "Define a new directive",
  applicationTime := .afterCompilation,
  add declName stx k := do
    unless k == .global do throwError m!"Must be `global`"
    let directiveName ←
      match stx with
      | `(attr|directive) => pure declName
      | `(attr|directive $x) => realizeGlobalConstNoOverloadWithInfo x
      | _ => throwError "Invalid `directive` attribute"

    let n ← mkFreshUserName <| declName ++ `directive

    let ((e, t), _) ← Meta.MetaM.run (ctx := {}) (s := {}) do
      let e ← Meta.mkAppM ``toDirective #[.const declName []]
      let e ← instantiateMVars e
      let t ← Meta.inferType e


      match_expr e with
      | toDirective ty _ _ => saveSignature n ty
      | _ => pure ()

      pure (e, t)

    addAndCompile <| .defnDecl {
      name := n,
      levelParams := [],
      type := t,
      value := e,
      hints := .opaque,
      safety := .safe
    }

    addDocStringCore' n (← findSimpleDocString? (← getEnv) declName)

    modifyEnv fun env =>
      directiveExpanderExt.addEntry env (directiveName, n)
}

private unsafe def directiveExpandersForUnsafe' (x : Name) : DocElabM (Array (DirectiveExpander × Option String × Option SigDoc)) := do
  let expanders := directiveExpanderExt.getState (← getEnv) |>.find? x |>.getD #[]
  expanders.mapM fun n => do
    let e ← evalConst DirectiveExpander n
    let doc? ← findDocString? (← getEnv) n
    let sig := expanderSignatureExt.getState (← getEnv) |>.find? n
    return (e, doc?, sig)

private unsafe def directiveExpandersForUnsafe'' (x : Name) : DocElabM (Array DirectiveExpander) := do
  let expanders := directiveExpanderAttr.getEntries (← getEnv) x
  return expanders.map (·.value) |>.toArray

private unsafe def directiveExpandersForUnsafe (x : Name) : DocElabM (Array (DirectiveExpander × Option String × Option SigDoc)) := do
  return (← directiveExpandersForUnsafe' x) ++ (← directiveExpandersForUnsafe'' x).map (·, none, none)

@[implemented_by directiveExpandersForUnsafe]
opaque directiveExpandersFor (x : Name) : DocElabM (Array (DirectiveExpander × Option String × Option SigDoc))


abbrev BlockCommandExpander := Array Arg → DocElabM (Array (TSyntax `term))

abbrev BlockCommandOf α := α → DocElabM Term

initialize blockCommandExpanderAttr : KeyedDeclsAttribute BlockCommandExpander ←
  mkDocExpanderAttribute `block_command_expander ``BlockCommandExpander "Indicates that this function is used to implement a given block-level command" `blockCommandExpanderAttr

private def toBlockCommand {α : Type} [FromArgs α DocElabM] (expander : α → DocElabM Term) : BlockCommandExpander :=
  fun args => do
    let v ← ArgParse.parse args
    return #[← expander v]

syntax (name := block_command) "block_command " (ident)? : attr

initialize blockCommandExpanderExt : PersistentEnvExtension (Name × Array Name) (Name × Name) (NameMap (Array Name)) ←
  registerPersistentEnvExtension {
    mkInitial := pure {},
    addImportedFn xss :=
      pure <| xss.foldl (init := {}) fun ns xs =>
        xs.foldl (init := ns) fun ns (x, ys) =>
          ns.insert x <| (ns.find? x |>.getD #[]) ++ ys
    addEntryFn
      | xs, (x, y) =>
        xs.insert x (xs.find? x |>.getD #[] |>.push y)
    exportEntriesFn xs :=
      xs.toArray
  }

unsafe initialize registerBuiltinAttribute {
  name := `block_command,
  descr := "Define a new block command",
  applicationTime := .afterCompilation,
  add declName stx k := do
    unless k == .global do throwError m!"Must be `global`"
    let cmdName ←
      match stx with
      | `(attr|block_command) => pure declName
      | `(attr|block_command $x) => realizeGlobalConstNoOverloadWithInfo x
      | _ => throwError "Invalid `block_command` attribute"

    let n ← mkFreshUserName <| declName ++ `block_command

    let ((e, t), _) ← Meta.MetaM.run (ctx := {}) (s := {}) do
      let e ← Meta.mkAppM ``toBlockCommand #[.const declName []]
      let e ← instantiateMVars e
      let t ← Meta.inferType e

      match_expr e with
      | toBlockCommand ty _ _ => saveSignature n ty
      | _ => pure ()

      pure (e, t)

    addAndCompile <| .defnDecl {
      name := n,
      levelParams := [],
      type := t,
      value := e,
      hints := .opaque,
      safety := .safe
    }

    addDocStringCore' n (← findSimpleDocString? (← getEnv) declName)

    modifyEnv fun env =>
      blockCommandExpanderExt.addEntry env (cmdName, n)
}

private unsafe def blockCommandExpandersForUnsafe' (x : Name) : DocElabM (Array (BlockCommandExpander × Option String × Option SigDoc)) := do
  let expanders := blockCommandExpanderExt.getState (← getEnv) |>.find? x |>.getD #[]
  expanders.mapM fun n => do
    let e ← evalConst BlockCommandExpander n
    let doc? ← findDocString? (← getEnv) n
    let sig := expanderSignatureExt.getState (← getEnv) |>.find? n
    return (e, doc?, sig)

private unsafe def blockCommandExpandersForUnsafe'' (x : Name) : DocElabM (Array BlockCommandExpander) := do
  let expanders := blockCommandExpanderAttr.getEntries (← getEnv) x
  return expanders.map (·.value) |>.toArray

private unsafe def blockCommandExpandersForUnsafe (x : Name) : DocElabM (Array (BlockCommandExpander × Option String × Option SigDoc)) := do
  return (← blockCommandExpandersForUnsafe' x) ++ (← blockCommandExpandersForUnsafe'' x).map (·, none, none)

@[implemented_by blockCommandExpandersForUnsafe]
opaque blockCommandExpandersFor (x : Name) : DocElabM (Array (BlockCommandExpander × Option String × Option SigDoc))
