/-
Copyright (c) 2023-2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module
import Std.Data.HashMap
import Std.Data.HashSet

import Lean.Elab.DeclUtil
import Lean.Meta.Reduce
import Lean.DocString.Syntax
import Lean.DocString

import SubVerso.Highlighting
import Verso.Doc
import Verso.EnvExtension
public import Verso.Doc.ArgParse
public import Verso.Doc.Elab.InlineString
meta import Verso.Doc.Elab.InlineString
public import Verso.Doc.Elab.Basic
import Verso.Doc.Elab.ExpanderAttribute
public import Verso.Doc.Name
import Verso.Doc.DocName

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


-- For use in IDE features and previews and such
@[inline_to_string Lean.Doc.Syntax.text]
public meta def _root_.Lean.Doc.Syntax.text.inline_to_string : InlineToString
  | _, `(inline| $s:str) => some s.getString
  | _, _ => none

@[inline_to_string Lean.Doc.Syntax.linebreak]
public meta def _root_.Lean.Doc.Syntax.linebreak.inline_to_string : InlineToString
  | _, `(inline|line! $_) => some " "
  | _, _ => none

@[inline_to_string Lean.Doc.Syntax.emph]
public meta def _root_.Lean.Doc.Syntax.emph.inline_to_string : InlineToString
  | env, `(inline| _[ $args* ]) =>
    some <| String.intercalate " " (Array.map (inlineToString env) args).toList
  | _, _ => none

@[inline_to_string Lean.Doc.Syntax.bold]
public meta def _root_.Lean.Doc.Syntax.bold.inline_to_string : InlineToString
  | env, `(inline| *[ $args* ]) =>
    some <| String.intercalate " " (Array.map (inlineToString env) args).toList
  | _, _ => none

@[inline_to_string Lean.Doc.Syntax.code]
public meta def _root_.Lean.Doc.Syntax.code.inline_to_string : InlineToString
  | _, `(inline| code( $str )) =>
    some str.getString
  | _, _ => none

@[inline_to_string Lean.Doc.Syntax.link]
public meta def _root_.Lean.Doc.Syntax.link.inline_to_string : InlineToString
  | env, `(inline| link[ $args* ] $_:link_target) =>
    some <| String.intercalate " " (Array.map (inlineToString env) args).toList
  | _, _ => none

@[inline_to_string Lean.Doc.Syntax.image]
public meta def _root_.Lean.Doc.Syntax.image.inline_to_string : InlineToString
  | _, `(inline| image( $_:str ) $_:link_target) => some ""
  | _, _ => none

@[inline_to_string Lean.Doc.Syntax.footnote]
public meta def _root_.Lean.Doc.Syntax.footnote.inline_to_string : InlineToString
  | _, `(inline| footnote( $_:str )) => some ""
  | _, _ => none

@[inline_to_string Lean.Doc.Syntax.role]
public meta def _root_.Lean.Doc.Syntax.role.inline_to_string : InlineToString
  | env, `(inline| role{ $_ $_* }[ $body* ]) =>
    String.join (body.toList.map (inlineToString env <| ·.raw))
  | _, _ => none

@[inline_to_string null]
public meta def nullInline_to_string : InlineToString
  | env, .node _ _ contents =>
    return String.join <| contents.toList.map (inlineToString env)
  | _, _ => none

@[inline_to_string Lean.Parser.Term.app]
public meta def app_to_string : InlineToString := fun (env : Environment) => fun
  | `(Verso.Doc.Inline.text $s:str) =>
    return s.getString
  | `(Verso.Doc.Inline.concat #[$xs,*]) =>
    return String.join <| (xs : Array _).toList.map (inlineToString env)
  | _ => none

public def inlinesToString (env : Environment) (inlines : Array Syntax)  : String :=
  String.intercalate " " (inlines.map (inlineToString env) |>.filter (!·.isEmpty)).toList

public def inlineSyntaxToString (env : Environment) (inlines : Syntax) : String :=
    if let `<low| ~(.node _ _ args)> := inlines then
      inlinesToString env args
    else
      dbg_trace "didn't understand inline sequence {inlines} for string"
      "<missing>"

public def headerStxToString (env : Environment) : Syntax → String
  | `(block|header($_){$inlines*}) => inlinesToString env inlines
  | headerStx => dbg_trace "didn't understand {headerStx} for string"
    "<missing>"

/--
Specifies the elaboration behavior of inline references in Verso.
-/
public inductive RefsAllowed : Type where
  /--
  A footnote ref like `[^note]` or a link ref like {lit}`[wikipedia]` are treated as an error if the
  current {lit}`PartElabM` state does not contain a definition for the ref.
  -/
  | onlyIfDefined
  /--
  Undefined link and footnote references in inline text are permitted with no warning.
  -/
  | always
deriving Inhabited, BEq

public structure DocElabContext where
  genreSyntax : Syntax
  genre : Expr


  /-- Whether references to undefined (not-yet-defined) footnotes and links are permitted. -/
  refsAllowed : RefsAllowed

  /--
  The docReconstructionPlaceholder provides a free variable during Verso document elaboration. This
  syntax object cannot be successfully elaborated to a term until closed as a function
  {lit}`` `(fun $docReconstructionPlaceholder => $termContainingFreeVariable) ``.
  -/
  docReconstructionPlaceholder : Option Ident
deriving Inhabited


public def DocElabContext.fromGenreTerm (genreSyntax : Term) : TermElabM DocElabContext := do
  let genre ← Term.elabTerm genreSyntax (some (.const ``Doc.Genre []))
  return DocElabContext.mk genreSyntax genre .always (.some <| mkIdent (← mkFreshUserName `docReconst))

public structure DocElabM.State where
  linkRefs : HashMap String DocUses := {}
  footnoteRefs : HashMap String DocUses := {}

  /--
  Retains a more efficient representation of document-wide information about highlighted code.
  (Used only by the {lit}`Manual` genre at present.)
  -/
  highlightDeduplicationTable : Option SubVerso.Highlighting.Exporting := .none
deriving Inhabited

public structure PartElabM.State where
  partContext : PartContext
  linkDefs : HashMap String (DocDef String) := {}
  footnoteDefs : HashMap String (DocDef (Array (TSyntax `term))) := {}
  /-- The footnote uses in each footnote's contents, by the footnote's label. -/
  footnoteUses : HashMap String (Array (String × Syntax)) := {}
  deferredBlocks : Array (Name × Term) := #[]
deriving Inhabited

public def PartElabM.State.init (rangeSyntax : Syntax) (selectionSyntax : Syntax) (expandedTitle : Option (String × Array (TSyntax `term)) := none) : PartElabM.State where
  partContext := {rangeSyntax, selectionSyntax, expandedTitle, metadata := none, blocks := #[], priorParts := #[], parents := #[]}

/--
Top-level document elaboration monad. Can modify both DocElabM.State and PartElabM.State
-/
@[expose]
public def PartElabM (α : Type) : Type := ReaderT DocElabContext (StateT DocElabM.State (StateT PartElabM.State TermElabM)) α

public def PartElabM.run (ctx : DocElabContext) (st : DocElabM.State) (st' : PartElabM.State) (act : PartElabM α) : TermElabM (α × DocElabM.State × PartElabM.State) := do
  let ((res, st), st') ← act ctx st st'
  pure (res, st, st')

public instance : Alternative PartElabM := inferInstanceAs <| Alternative (ReaderT DocElabContext (StateT DocElabM.State (StateT PartElabM.State TermElabM)))

public instance : MonadRef PartElabM := inferInstanceAs <| MonadRef (ReaderT DocElabContext (StateT DocElabM.State (StateT PartElabM.State TermElabM)))

public instance : MonadAlwaysExcept Exception PartElabM := inferInstanceAs <| MonadAlwaysExcept Exception (ReaderT DocElabContext (StateT DocElabM.State (StateT PartElabM.State TermElabM)))

public instance : AddErrorMessageContext PartElabM := inferInstanceAs <| AddErrorMessageContext (ReaderT DocElabContext (StateT DocElabM.State (StateT PartElabM.State TermElabM)))

public instance : MonadQuotation PartElabM := inferInstanceAs <| MonadQuotation (ReaderT DocElabContext (StateT DocElabM.State (StateT PartElabM.State TermElabM)))

public instance : Monad PartElabM := inferInstanceAs <| Monad (ReaderT DocElabContext (StateT DocElabM.State (StateT PartElabM.State TermElabM)))

public instance : MonadLift TermElabM PartElabM where
  monadLift act := private fun _ st st' => do return ((← Term.withDeclName (← currentDocName) act, st), st')

public instance : MonadExceptOf Exception PartElabM := inferInstanceAs <| MonadExceptOf Exception (ReaderT DocElabContext (StateT DocElabM.State (StateT PartElabM.State TermElabM)))

public instance : MonadStateOf DocElabM.State PartElabM := inferInstanceAs <| MonadStateOf DocElabM.State (ReaderT DocElabContext (StateT DocElabM.State (StateT PartElabM.State TermElabM)))

public instance instMonadStatePartElabM : MonadStateOf PartElabM.State PartElabM := inferInstanceAs <| MonadStateOf PartElabM.State (ReaderT DocElabContext (StateT DocElabM.State (StateT PartElabM.State TermElabM)))

public instance : MonadFinally PartElabM := inferInstanceAs <| MonadFinally (ReaderT DocElabContext (StateT DocElabM.State (StateT PartElabM.State TermElabM)))

public instance : MonadWithReaderOf Core.Context PartElabM := inferInstanceAs <| MonadWithReaderOf Core.Context (ReaderT DocElabContext (StateT DocElabM.State (StateT PartElabM.State TermElabM)))

public instance instMonadReaderOfPartElabM : MonadWithReaderOf Term.Context PartElabM := inferInstanceAs <| MonadWithReaderOf Term.Context (ReaderT DocElabContext (StateT DocElabM.State (StateT PartElabM.State TermElabM)))

public instance : MonadWithReaderOf DocElabContext PartElabM := inferInstanceAs <| MonadWithReaderOf DocElabContext (ReaderT DocElabContext (StateT DocElabM.State (StateT PartElabM.State TermElabM)))

public instance : MonadReaderOf DocElabContext PartElabM := inferInstanceAs <| MonadReaderOf DocElabContext (ReaderT DocElabContext (StateT DocElabM.State (StateT PartElabM.State TermElabM)))

public instance : MonadWithOptions PartElabM := inferInstanceAs <| MonadWithOptions (ReaderT DocElabContext (StateT DocElabM.State (StateT PartElabM.State TermElabM)))

public def PartElabM.withFileMap (fileMap : FileMap) (act : PartElabM α) : PartElabM α :=
  fun ρ ρ' σ ctxt σ' mctxt rw cctxt => act ρ ρ' σ ctxt σ' mctxt rw {cctxt with fileMap := fileMap}

public def withRefsAllowed [MonadWithReaderOf DocElabContext m] [Monad m] (b : RefsAllowed) : m a → m a :=
  withTheReader DocElabContext ({ · with refsAllowed := b})

/--
Text elaboration monad.

This monad can produce content, but it can't modify the structure of the surrounding document. It
can observe this structure, however.

This means it can modify the {lean}`DocElabM.State`, but it can only read from the
{lean}`PartElabM.State`.
-/
@[expose]
public def DocElabM (α : Type) : Type := ReaderT DocElabContext (ReaderT PartElabM.State (StateT DocElabM.State TermElabM)) α

public def DocElabM.run (ctx : DocElabContext) (st : DocElabM.State) (st' : PartElabM.State) (act : DocElabM α) : TermElabM (α × DocElabM.State) := do
  StateT.run (act ctx st') st

public instance : Inhabited (DocElabM α) := ⟨fun _ _ _ => default⟩

public instance : AddErrorMessageContext DocElabM := inferInstanceAs <| AddErrorMessageContext (ReaderT DocElabContext (ReaderT PartElabM.State (StateT DocElabM.State TermElabM)))

public instance [MonadWithReaderOf ρ TermElabM] : MonadWithReaderOf ρ DocElabM :=
  inferInstanceAs <| MonadWithReaderOf ρ (ReaderT DocElabContext (ReaderT PartElabM.State (StateT DocElabM.State TermElabM)))

public instance : MonadLift TermElabM DocElabM where
  monadLift act := fun _ _ st' => do return (← Term.withDeclName (← currentDocName) act, st')

public instance : MonadLift IO DocElabM where
  monadLift act := fun _ _ st' => do return (← act, st')

public instance : Alternative DocElabM := inferInstanceAs <| Alternative (ReaderT DocElabContext (ReaderT PartElabM.State (StateT DocElabM.State TermElabM)))

public instance : MonadRef DocElabM := inferInstanceAs <| MonadRef (ReaderT DocElabContext (ReaderT PartElabM.State (StateT DocElabM.State TermElabM)))

public instance : MonadQuotation DocElabM := inferInstanceAs <| MonadQuotation (ReaderT DocElabContext (ReaderT PartElabM.State (StateT DocElabM.State TermElabM)))

public instance : Monad DocElabM := inferInstanceAs <| Monad (ReaderT DocElabContext (ReaderT PartElabM.State (StateT DocElabM.State TermElabM)))

public instance : MonadControl TermElabM DocElabM :=
  let ⟨stM, liftWith, restoreM⟩ := (inferInstance : MonadControlT TermElabM (ReaderT DocElabContext (ReaderT PartElabM.State (StateT DocElabM.State TermElabM))))
  {stM, liftWith, restoreM := (· >>= restoreM)}

public instance : MonadExceptOf Exception DocElabM := inferInstanceAs <| MonadExceptOf Exception (ReaderT DocElabContext (ReaderT PartElabM.State (StateT DocElabM.State TermElabM)))

public instance : MonadAlwaysExcept Exception DocElabM := inferInstanceAs <| MonadAlwaysExcept Exception (ReaderT DocElabContext (ReaderT PartElabM.State (StateT DocElabM.State TermElabM)))

public instance : MonadReaderOf PartElabM.State DocElabM := inferInstanceAs <| MonadReaderOf PartElabM.State (ReaderT DocElabContext (ReaderT PartElabM.State (StateT DocElabM.State TermElabM)))

public instance : MonadStateOf DocElabM.State DocElabM := inferInstanceAs <| MonadStateOf DocElabM.State (ReaderT DocElabContext (ReaderT PartElabM.State (StateT DocElabM.State TermElabM)))

public instance : MonadFinally DocElabM := inferInstanceAs <| MonadFinally (ReaderT DocElabContext (ReaderT PartElabM.State (StateT DocElabM.State TermElabM)))

public instance : MonadInfoTree DocElabM := inferInstanceAs <| MonadInfoTree (ReaderT DocElabContext (ReaderT PartElabM.State (StateT DocElabM.State TermElabM)))

public instance : MonadEnv DocElabM := inferInstanceAs <| MonadEnv (ReaderT DocElabContext (ReaderT PartElabM.State (StateT DocElabM.State TermElabM)))

public instance : MonadFileMap DocElabM := inferInstanceAs <| MonadFileMap (ReaderT DocElabContext (ReaderT PartElabM.State (StateT DocElabM.State TermElabM)))

public instance : MonadOptions DocElabM := inferInstanceAs <| MonadOptions (ReaderT DocElabContext (ReaderT PartElabM.State (StateT DocElabM.State TermElabM)))

public instance : MonadWithOptions DocElabM := inferInstanceAs <| MonadWithOptions (ReaderT DocElabContext (ReaderT PartElabM.State (StateT DocElabM.State TermElabM)))

public instance : MonadWithReaderOf Core.Context DocElabM := inferInstanceAs <| MonadWithReaderOf Core.Context (ReaderT DocElabContext (ReaderT PartElabM.State (StateT DocElabM.State TermElabM)))

public instance instMonadWithReaderOfDocElabM : MonadWithReaderOf Term.Context DocElabM := inferInstanceAs <| MonadWithReaderOf Term.Context (ReaderT DocElabContext (ReaderT PartElabM.State (StateT DocElabM.State TermElabM)))

public instance : MonadReaderOf DocElabContext DocElabM := inferInstanceAs <| MonadReaderOf DocElabContext (ReaderT DocElabContext (ReaderT PartElabM.State (StateT DocElabM.State TermElabM)))

public instance instMonadReaderOfDocElabM : MonadReaderOf PartElabM.State DocElabM := inferInstanceAs <| MonadReaderOf PartElabM.State (ReaderT DocElabContext (ReaderT PartElabM.State (StateT DocElabM.State TermElabM)))

public def DocElabM.withFileMap (fileMap : FileMap) (act : DocElabM α) : DocElabM α :=
  fun ρ ρ' σ ctxt σ' mctxt rw cctxt => act ρ ρ' σ ctxt σ' mctxt rw {cctxt with fileMap := fileMap}

public instance : MonadRecDepth DocElabM where
  withRecDepth n act := fun ρ st st' => MonadRecDepth.withRecDepth n (act ρ st st')
  getRecDepth := fun _ _ st' => do return (← MonadRecDepth.getRecDepth, st')
  getMaxRecDepth := fun _ _ st' => do return (← MonadRecDepth.getMaxRecDepth, st')

public def PartElabM.liftDocElabM (act : DocElabM α) : PartElabM α := do
  let (out, stDoc) ← act.run (← readThe DocElabContext) (← getThe DocElabM.State) (← getThe PartElabM.State)
  modifyThe DocElabM.State (fun _ => stDoc)
  pure out

public instance : MonadLift DocElabM PartElabM := ⟨PartElabM.liftDocElabM⟩

public def PartElabM.State.currentLevel (state : PartElabM.State) : Nat := state.partContext.level

public def PartElabM.currentLevel : PartElabM Nat := do return (← getThe State).currentLevel

public def PartElabM.setTitle (titlePreview : String) (titleInlines : Array (TSyntax `term)) : PartElabM Unit := modifyThe State fun st =>
  {st with partContext.expandedTitle := some (titlePreview, titleInlines)}

public partial def PartElabM.closePartsUntil (outer : Nat) (endPos : String.Pos.Raw) : PartElabM Unit := do
  let level ← currentLevel
  if outer ≤ level then
    match (← getThe PartElabM.State).partContext.close endPos with
    | some ctxt' =>
      modifyThe PartElabM.State fun st => {st with partContext := ctxt'}
      if outer < level then
        closePartsUntil outer endPos
    | none => pure ()

/--
Adds a block (syntax denoting a {lit}`Block g`) to the elaboration state.

The block becomes a function of document reconstruction data. The function's parameter is
{name}`blockInternalDocReconstructionPlaceholder` if it is given, and otherwise the current
{name}`DocElabContext`'s {name}`DocElabContext.docReconstructionPlaceholder`.
-/
public def PartElabM.addBlock (block : TSyntax `term) (blockInternalDocReconstructionPlaceholder : Option Ident := .none)  : PartElabM Unit := do
  -- The syntax denoting the top-level Part structure will refer to this block by name, passing it
  -- the ident that holds the `DocReconstruction` object.
  let name ← mkFreshUserName `block
  let .some docReconstructionPlaceholder := (← read).docReconstructionPlaceholder
    | throwErrorAt block "No doc reconstruction placeholder available"
  let blockRefSyntax ← ``($(mkIdent name) $docReconstructionPlaceholder)

  -- If the internal block includes a doc reconstruction placeholder, it should be different from
  -- the one in the current `DocElabContext` to maintain good hygiene.
  let blockDefSyntax ← match blockInternalDocReconstructionPlaceholder with
    | .none => `(fun $docReconstructionPlaceholder => $block)
    | .some name => `(fun $name => $block)

  modifyThe PartElabM.State fun st =>
    { st with
      partContext.blocks := st.partContext.blocks.push blockRefSyntax
      deferredBlocks := st.deferredBlocks.push (name, blockDefSyntax)
    }

public def PartElabM.addPart (finished : FinishedPart) : PartElabM Unit := modifyThe State fun st =>
  { st with partContext.priorParts := st.partContext.priorParts.push finished }

/--
The start of the document under construction. It identifies the document within its file.
-/
public def PartElabM.State.documentPos? (state : PartElabM.State) : Option String.Pos.Raw :=
  let root := state.partContext.parents[0]?.getD state.partContext.toPartFrame
  root.rangeSyntax.getPos?

/--
Records a definition or use of a link or footnote in the info tree, for editor features.
-/
def pushDocRefInfo [Monad m] [MonadInfoTree m]
    (state : PartElabM.State) (kind : DocRefKind) (labelStx : TSyntax `str) (isDef : Bool) : m Unit :=
  let info : DocRefInfo :=
    { kind, label := labelStx.getString, documentPos? := state.documentPos?, isDef }
  pushInfoLeaf <| .ofCustomInfo { stx := labelStx, value := Dynamic.mk info }

/--
Describes the location of the definition {name}`d`. The file name is included when it differs from
the current file.
-/
def describeDefLocation {α : Type} (d : DocDef α) : PartElabM MessageData := do
  let lineCol := m!"line {d.position.line}, column {d.position.column}"
  if d.fileName == (← getFileName) then
    return lineCol
  else
    return m!"{lineCol} of {d.fileName}"

/-- A definition of the label {name}`labelStx` with the value {name}`val`, in the current file. -/
def PartElabM.mkDocDef {α : Type} (labelStx : TSyntax `str) (val : α) : PartElabM (DocDef α) := do
  let position := (← getFileMap).toPosition (labelStx.raw.getPos?.getD 0)
  return { labelStx, val, fileName := ← getFileName, position }

/--
Records the definition of the link whose label is {name}`labelStx`. A second definition of the same
label in one document is an error.
-/
public def PartElabM.addLinkDef (labelStx : TSyntax `str) (url : String) : PartElabM Unit := do
  let label := labelStx.getString
  match (← getThe State).linkDefs[label]? with
  | none =>
    let d ← mkDocDef labelStx url
    modifyThe State fun st => {st with linkDefs := st.linkDefs.insert label d}
    pushDocRefInfo (← getThe State) .link labelStx (isDef := true)
  | some prev =>
    throwErrorAt labelStx
      m!"Duplicate definition of link label [{label}]. It is already defined at {← describeDefLocation prev}, with the URL '{prev.val}'. This definition has the URL '{url}'."

/--
Records a use of the link whose label is {name}`labelStx`, and returns a term for its URL.
-/
public def DocElabM.addLinkRef (labelStx : TSyntax `str) : DocElabM (TSyntax `term) := do
  let label := labelStx.getString
  match (← readThe DocElabContext).refsAllowed with
    | .always => pure ()
    | .onlyIfDefined =>
      if !(← readThe PartElabM.State).linkDefs.contains label then
        throwErrorAt labelStx m!"Link reference [{label}] does not have a definition"
  let .some docReconst := (← readThe DocElabContext).docReconstructionPlaceholder
    | throwErrorAt labelStx m!"The link label [{label}] can't be used here, because this text is elaborated outside of a document"

  modifyThe State fun st =>
    {st with linkRefs := st.linkRefs.insert label ((st.linkRefs.getD label {}).add labelStx)}
  pushDocRefInfo (← readThe PartElabM.State) .link labelStx (isDef := false)
  ``(DocReconstruction.linkUrl $docReconst $(quote label))

/--
Elaborates a footnote's contents to check them, and reports their errors. Returns {lean}`true` when
the contents have no errors. The elaborated term is discarded, and the info tree is left unchanged.
-/
def PartElabM.checkFootnoteContents (content : Array (TSyntax `term)) : PartElabM Bool := do
  let ctx ← readThe DocElabContext
  let .some docReconst := ctx.docReconstructionPlaceholder
    | throwError "No doc reconstruction placeholder available"
  let genre : Term := ⟨ctx.genreSyntax⟩
  let stx ← ``(fun ($docReconst : DocReconstruction $genre) => (#[$content,*] : Array (Doc.Inline $genre)))
  let act : TermElabM Bool := withEnableInfoTree false do
    try
      let e ← Term.elabTerm stx none
      Term.synthesizeSyntheticMVarsNoPostponing
      return !(← instantiateMVars e).hasSyntheticSorry
    catch ex =>
      logException ex
      return false
  act

/--
Records the definition of the footnote whose label is {name}`labelStx`, with the contents
{name}`content`, which are terms that denote inlines. A second definition of the same label in one
document is an error.

The contents are checked here, so that their errors appear at the definition. Contents with errors
are recorded as empty.

{name}`contentUses` are the footnote uses in the contents, each paired with its label.
-/
public def PartElabM.addFootnoteDef (labelStx : TSyntax `str) (content : Array (TSyntax `term))
    (contentUses : Array (String × Syntax) := #[]) : PartElabM Unit := do
  let label := labelStx.getString
  match (← getThe State).footnoteDefs[label]? with
  | none =>
    let content := if ← checkFootnoteContents content then content else #[]
    let d ← mkDocDef labelStx content
    modifyThe State fun st => { st with
      footnoteDefs := st.footnoteDefs.insert label d
      footnoteUses := st.footnoteUses.insert label contentUses
    }
    pushDocRefInfo (← getThe State) .footnote labelStx (isDef := true)
  | some prev =>
    throwErrorAt labelStx
      m!"Duplicate definition of footnote label [^{label}]. It is already defined at {← describeDefLocation prev}."

/--
Records a use of the footnote whose label is {name}`labelStx`, and returns a term for its contents.
-/
public def DocElabM.addFootnoteRef (labelStx : TSyntax `str) : DocElabM (TSyntax `term) := do
  let label := labelStx.getString
  match (← readThe DocElabContext).refsAllowed with
    | .always => pure ()
    | .onlyIfDefined =>
      if !(← readThe PartElabM.State).footnoteDefs.contains label then
        throwErrorAt labelStx m!"Footnote reference [^{label}] does not have a definition"
  let .some docReconst := (← readThe DocElabContext).docReconstructionPlaceholder
    | throwErrorAt labelStx m!"The footnote label [^{label}] can't be used here, because this text is elaborated outside of a document"

  modifyThe State fun st =>
    {st with footnoteRefs := st.footnoteRefs.insert label ((st.footnoteRefs.getD label {}).add labelStx)}
  pushDocRefInfo (← readThe PartElabM.State) .footnote labelStx (isDef := false)
  ``(DocReconstruction.footnoteContents $docReconst $(quote label))

/--
Orders the labels of a document's footnotes so that each footnote comes after the footnotes that its
contents use. Also returns each use that makes a footnote's contents use the footnote itself,
directly or through other footnotes. Each of these uses is paired with its label and with the labels
of the other footnotes in the cycle, in the order of the cycle.
-/
public partial def footnoteOrder (partElabState : PartElabM.State) :
    Array String × Array (String × Array String × Syntax) :=
  let labels := partElabState.footnoteDefs.toArray.mergeSort (fun (_, d1) (_, d2) =>
    d1.labelStx.raw.getPos?.getD 0 ≤ d2.labelStx.raw.getPos?.getD 0) |>.map (·.1)
  let (_, _, order, cycles) := labels.foldl (init := ({}, #[], #[], #[])) fun st label => visit label st
  (order, cycles)
where
  -- `active` holds the labels of the footnotes being visited, from the outermost to the innermost.
  visit (label : String) :
      HashSet String × Array String × Array String × Array (String × Array String × Syntax) →
      HashSet String × Array String × Array String × Array (String × Array String × Syntax)
    | (done, active, order, cycles) =>
      if done.contains label then (done, active, order, cycles) else
      let st := (partElabState.footnoteUses.getD label #[]).foldl (init := (done, active.push label, order, cycles))
        fun (done, active, order, cycles) (used, useStx) =>
          if !partElabState.footnoteDefs.contains used then (done, active, order, cycles)
          else match active.idxOf? used with
            | some i => (done, active, order, cycles.push (used, active.extract (i + 1) active.size, useStx))
            | none => visit used (done, active, order, cycles)
      let (done, active, order, cycles) := st
      (done.insert label, active.pop, order.push label, cycles)

/--
Compares a document's link and footnote uses with its definitions. Each use without a definition
results in an error, and each definition without a use results in a warning. Cyclic footnotes result
in an error as well. The messages are in source order.
-/
public def checkLinksAndFootnotes (docElabState : DocElabM.State) (partElabState : PartElabM.State) :
    Array (Syntax × MessageSeverity × MessageData) := Id.run do
  let mut msgs := #[]
  for (label, uses) in docElabState.footnoteRefs do
    if !partElabState.footnoteDefs.contains label then
      for use in uses.useSites do
        msgs := msgs.push (use, .error, m!"No definition for footnote [^{label}]")
  for (label, d) in partElabState.footnoteDefs do
    if !docElabState.footnoteRefs.contains label then
      msgs := msgs.push (d.labelStx.raw, .warning, m!"Unused footnote [^{label}]")
  for (label, uses) in docElabState.linkRefs do
    if !partElabState.linkDefs.contains label then
      for use in uses.useSites do
        msgs := msgs.push (use, .error, m!"No definition for link [{label}]")
  for (label, d) in partElabState.linkDefs do
    if !docElabState.linkRefs.contains label then
      msgs := msgs.push (d.labelStx.raw, .warning, m!"Unused link [{label}]")
  for (label, path, use) in (footnoteOrder partElabState).2 do
    msgs := msgs.push (use, .error, m!"Footnote [^{label}] is used inside its own contents{through path}")
  return msgs.mergeSort fun (stx1, _) (stx2, _) => startPos stx1 ≤ startPos stx2
where
  startPos (stx : Syntax) : Nat := stx.getPos?.map (·.byteIdx) |>.getD 0
  -- ", through [^b]", ", through [^b] and [^c]", or ", through [^b], [^c] and [^d]"
  through (path : Array String) : String :=
    let labels := path.toList.map (s!"[^{·}]")
    match labels.reverse with
    | [] => ""
    | [l] => s!", through {l}"
    | last :: rest => s!", through {", ".intercalate rest.reverse} and {last}"

public def PartElabM.push (fr : PartFrame) : PartElabM Unit := modifyThe State fun st => {st with partContext := st.partContext.push fr}

public def PartElabM.debug (msg : String) : PartElabM Unit := do
  let st ← getThe State
  dbg_trace "DEBUG: {msg}"
  dbg_trace "  partContext: {repr st.partContext}"
  dbg_trace ""
  pure ()


public def closes (openTok closeTok : Syntax) : DocElabM Unit := do
  let (.original _ pos _ _) := openTok.getHeadInfo
    | return ()
  let (.original ..) := closeTok.getHeadInfo
    | return ()
  let text ← getFileMap
  let {line, ..} := text.utf8PosToLspPos pos
  let lineStr := (text.lineStart (line + 1)).extract text.source  (text.lineStart (line + 2)) |>.trimAscii
  let lineStr := if lineStr.startsWith "`" || lineStr.endsWith "`" then " " ++ lineStr ++ " " else lineStr.copy
  Hover.addCustomHover closeTok (.markdown s!"Closes line {line + 1}: ``````````{lineStr}``````````")

public abbrev InlineExpander := Syntax → DocElabM (TSyntax `term)

initialize inlineExpanderAttr : KeyedDeclsAttribute InlineExpander ←
  mkDocExpanderAttribute `inline_expander ``InlineExpander "Indicates that this function expands inline elements of a given name" `inlineExpanderAttr

unsafe def inlineExpandersForUnsafe (x : Name) : DocElabM (Array InlineExpander) := do
  let expanders := inlineExpanderAttr.getEntries (← getEnv) x
  return expanders.map (·.value) |>.toArray

@[implemented_by inlineExpandersForUnsafe]
public opaque inlineExpandersFor (x : Name) : DocElabM (Array InlineExpander)

/--
Creates a term denoting a {lean}`VersoDoc` value from a {lean}`FinishedPart`. This is the final step
in turning a parsed verso doc into syntax.

It also reports the document's undefined and unused links and footnotes, and compiles the document's
blocks.

{name}`commandStart?` is the start of the command that finishes the document. It is used when the
command's syntax has no source range.
-/
public def FinishedPart.toVersoDoc
    (genreSyntax : Term)
    (finished : FinishedPart)
    (ctx : DocElabContext)
    (docElabState : DocElabM.State)
    (partElabState : PartElabM.State)
    (commandStart? : Option String.Pos.Raw := none) :
    TermElabM Term := do

  -- Lean suppresses the elaboration errors of a command with a parse error. Messages about syntax
  -- outside the current command are logged with this suppression turned off. This way, a parse
  -- error in the last block of a `#doc` document leaves the messages about earlier blocks visible.
  -- When the command's syntax has no source range, `commandStart?` gives its start.
  let cmdRange? := (← getRef).getRange?
  for (stx, severity, msg) in checkLinksAndFootnotes docElabState partElabState do
    let outsideCommand := match cmdRange?, commandStart?, stx.getPos? with
      | some r, _, some pos => !(r.start ≤ pos && pos ≤ r.stop)
      | none, some start, some pos => pos < start
      | _, _, _ => false
    if outsideCommand then
      withTheReader Core.Context ({ · with suppressElabErrors := false }) <|
        logAt stx msg severity
    else
      logAt stx msg severity

  -- Add and compile blocks
  for (name, block) in partElabState.deferredBlocks do
    withRef block do
    withCurrHeartbeats do -- reset the heartbeat count for each block addAndCompile

      let mut type ← Term.elabType (← ``(DocReconstruction $genreSyntax → Doc.Block $genreSyntax))
      let mut blockExpr ← Term.elabTerm block (some type)

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
        withOptions (·.setBool `compiler.extract_closed false) <| addAndCompile decl

  -- Generate and return outermost syntax
  let finishedSyntax ← finished.toSyntax genreSyntax
  let .some docReconstructionPlaceholder := ctx.docReconstructionPlaceholder
    | throwError "No doc reconstruction placeholder available"

  let reconstJson := match docElabState.highlightDeduplicationTable with
    | .none => Json.mkObj []
    | .some table => Json.mkObj [("highlight", table.toExport.toJson)]

  let body ← refTables genreSyntax docReconstructionPlaceholder partElabState finishedSyntax
  ``(VersoDoc.mk (fun $docReconstructionPlaceholder => $body) $(quote reconstJson.compress))
where
  /--
  Wraps {name}`body` so that the document reconstruction data {name}`docReconst` also holds the
  document's link table and footnote table.
  Each footnote's contents can use the links. Footnotes are added in the order of
  {name}`footnoteOrder`, so each footnote comes after its footnote dependencies.
  -/
  refTables (genreSyntax : Term) (docReconst : Ident) (partElabState : PartElabM.State) (body : Term) :
      TermElabM Term := do
    if partElabState.linkDefs.isEmpty && partElabState.footnoteDefs.isEmpty then
      return body
    let links ← (inSourceOrder partElabState.linkDefs).mapM fun (label, d) =>
      ``(($(quote label), $(quote d.val)))
    let footnotes ← (footnoteOrder partElabState).1.filterMapM fun label => do
      let some d := partElabState.footnoteDefs[label]? | return none
      some <$> ``(($(quote label),
          fun ($docReconst : DocReconstruction $genreSyntax) =>
            (#[$(d.val),*] : Array (Doc.Inline $genreSyntax))))
    let tables ← ``(DocReconstruction.withDefs $docReconst #[$links,*] #[$footnotes,*])
    `(let $docReconst := $tables
      $body)
  inSourceOrder {α : Type} (defs : HashMap String (DocDef α)) : Array (String × DocDef α) :=
    defs.toArray.mergeSort fun (_, d1) (_, d2) =>
      d1.labelStx.raw.getPos?.getD 0 ≤ d2.labelStx.raw.getPos?.getD 0


public abbrev BlockExpander := Syntax → DocElabM (TSyntax `term)

initialize blockExpanderAttr : KeyedDeclsAttribute BlockExpander ←
  mkDocExpanderAttribute `block_expander ``BlockExpander "Indicates that this function expands block elements of a given name" `blockExpanderAttr

unsafe def blockExpandersForUnsafe (x : Name) : DocElabM (Array BlockExpander) := do
  let expanders := blockExpanderAttr.getEntries (← getEnv) x
  return expanders.map (·.value) |>.toArray

@[implemented_by blockExpandersForUnsafe]
public opaque blockExpandersFor (x : Name) : DocElabM (Array BlockExpander)

-- We eagerly rebuild a `NameMap` from imported entries instead of keeping the
-- exported arrays sorted and doing binary search at lookup time, which is the
-- more common pattern for local persistent extensions.
--
-- This preserves the existing eager lookup-state initialization: doc expander
-- signatures are looked up by name repeatedly during elaboration, so the hot path
-- should be a single map lookup. The import-time cost should be small in the
-- expected case, since few signatures are exported by typical modules.
--
-- Another reason not to rely on per-module sorted arrays is that expanders are
-- not required to be registered in the same module as their associated
-- identifier, so lookup would otherwise need to search all imported arrays unless
-- we built an index anyway.
initialize expanderSignatureExt :
    LocalPersistentEnvExtension (Name × SigDoc) (Name × SigDoc) (NameMap SigDoc) ←
  LocalPersistentEnvExtension.register {
    name := `expanderSignatureExt
    mkInitialState := pure {}
    addImportedEntryFn
      | entries, (x, y) =>
        entries.insert x y
    addEntryFn
      | entries, (x, y) =>
        entries.insert x y
    exportEntriesFn _ entries :=
      .uniform entries.toArray
  }

public def sig (α) [inst : FromArgs α DocElabM] : Option ArgParse.SigDoc :=
  inst.fromArgs.signature

public abbrev PartCommand := Syntax → PartElabM Unit

initialize partCommandAttr : KeyedDeclsAttribute PartCommand ←
  mkDocExpanderAttribute `part_command ``PartCommand "Indicates that this function is used for side effects on the structure of the document" `partCommandAttr

unsafe def partCommandsForUnsafe (x : Name) : PartElabM (Array PartCommand) := do
  let expanders := partCommandAttr.getEntries (← getEnv) x
  return expanders.map (·.value) |>.toArray

@[implemented_by partCommandsForUnsafe]
public opaque partCommandsFor (x : Name) : PartElabM (Array PartCommand)


private def addExpanderEntry (entries : NameMap (Array Name)) (key value : Name) :
    NameMap (Array Name) :=
  entries.insert key <| (entries.find? key |>.getD #[]).push value

private abbrev ExpanderExtension :=
  LocalPersistentEnvExtension (Name × Array Name) (Name × Name) (NameMap (Array Name))

private def mkExpanderExtension (name : Name) : IO ExpanderExtension :=
  LocalPersistentEnvExtension.register {
    name
    mkInitialState := pure {}
    addImportedEntryFn
      | entries, (x, ys) =>
        ys.foldl (init := entries) fun entries y =>
          addExpanderEntry entries x y
    addEntryFn
      | entries, (x, y) =>
        addExpanderEntry entries x y
    exportEntriesFn _ entries :=
      .uniform entries.toArray
  }

public abbrev RoleExpander := Array Arg → TSyntaxArray `inline → DocElabM (Array (TSyntax `term))

public abbrev RoleExpanderOf α := α → TSyntaxArray `inline → DocElabM Term

initialize roleExpanderAttr : KeyedDeclsAttribute RoleExpander ←
  mkDocExpanderAttribute `role_expander ``RoleExpander "Indicates that this function is used to implement a given role" `roleExpanderAttr

public def toRole {α : Type} [FromArgs α DocElabM] (expander : α → TSyntaxArray `inline → DocElabM Term) : RoleExpander :=
  fun args inlines => do
    let v ← ArgParse.parse args
    return #[← expander v inlines]

public section
syntax (name := role) "role " (ident)? : attr
end

initialize roleExpanderExt : ExpanderExtension ←
  mkExpanderExtension `roleExpanderExt

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
public opaque roleExpandersFor (x : Name) : DocElabM (Array (RoleExpander × Option String × Option SigDoc))

private def registeredExpanderNames
    (ext : LocalPersistentEnvExtension (Name × Array Name) (Name × Name) (NameMap (Array Name)))
    (attr : KeyedDeclsAttribute α) : DocElabM (Array Name) := do
  let env ← getEnv
  let mut names : NameSet := {}
  for (n, _) in ext.getState env do
    names := names.insert n
  for (n, _) in env.constants do
    if !(attr.getEntries env n).isEmpty then
      names := names.insert n
  pure names.toList.toArray

private def registeredRoleNamesImpl : DocElabM (Array Name) :=
  registeredExpanderNames roleExpanderExt roleExpanderAttr

@[implemented_by registeredRoleNamesImpl]
public opaque registeredRoleNames : DocElabM (Array Name)

private unsafe def evalIOOptStringUnsafe (x : Name) : MetaM (Option SigDoc) := do
  evalConst (Option SigDoc) x

@[implemented_by evalIOOptStringUnsafe]
private opaque evalOptMsg (x : Name) : MetaM (Option SigDoc)

private meta unsafe def evalSigDocUnsafe (s : Expr) : MetaM (Option SigDoc) :=
  Meta.evalExpr (Option SigDoc) (.app (.const ``Option [0]) (.const ``SigDoc [])) s (checkMeta := false)

@[implemented_by evalSigDocUnsafe]
private opaque evalSigDoc (s : Expr) : MetaM (Option SigDoc)

private def saveSignature (expanderName : Name) (argTy : Expr) : MetaM Unit := do
  let s ← Meta.mkAppM ``sig #[argTy]
  let inst ← Meta.synthInstance (mkApp2 (.const ``FromArgs []) argTy (.const ``DocElabM []))
  let s := .app s inst
  let s ← instantiateExprMVars s
  -- Evaluate the signature now, while the argument parser's definitions are available in the
  -- elaboration environment, and store the result as data. The parser may be built from `partial`
  -- or meta definitions; storing the parser expression unevaluated would re-run it when the module
  -- is loaded, where those definitions are absent.
  let sig ← evalSigDoc s
  let name ← mkFreshUserName <| expanderName ++ `signature
  let decl := Declaration.defnDecl {
    name,
    levelParams := [],
    type := .app (.const ``Option [0]) (.const ``SigDoc []),
    value := toExpr sig,
    hints := .opaque,
    safety := .safe
  }
  addDecl decl

  if (← getEnv).header.isModule then
    modifyEnv (markMeta · name)

  compileDecl decl
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

    ensureAttrDeclIsMeta `role declName k

    let n ← mkFreshUserName <| declName ++ `role

    let ((e, t), _) ← Meta.MetaM.run (ctx := {}) (s := {}) do
      let e ← Meta.mkAppM ``toRole #[.const declName []]
      let e ← instantiateMVars e
      let t ← Meta.inferType e


      match_expr e with
      | toRole ty _ _ => saveSignature n ty
      | _ => pure ()

      pure (e, t)

    let decl := Declaration.defnDecl {
      name := n,
      levelParams := [],
      type := t,
      value := e,
      hints := .opaque,
      safety := .safe
    }
    addDecl decl

    if (← getEnv).header.isModule then
      modifyEnv (markMeta · n)

    compileDecl decl

    addDocStringCore' n (← findSimpleDocString? (← getEnv) declName)

    modifyEnv fun env =>
      roleExpanderExt.addEntry env (roleName, n)
}


public abbrev CodeBlockExpander := Array Arg → TSyntax `str → DocElabM (Array (TSyntax `term))

public abbrev CodeBlockExpanderOf α := α → StrLit → DocElabM Term


initialize codeBlockExpanderAttr : KeyedDeclsAttribute CodeBlockExpander ←
  mkDocExpanderAttribute `code_block_expander ``CodeBlockExpander "Indicates that this function is used to implement a given code block" `codeBlockExpanderAttr

public def toCodeBlock {α : Type} [FromArgs α DocElabM] (expander : α → StrLit → DocElabM Term) : CodeBlockExpander :=
  fun args str => do
    let v ← ArgParse.parse args
    return #[← expander v str]

syntax (name := code_block) "code_block " (ident)? : attr

initialize codeBlockExpanderExt : ExpanderExtension ←
  mkExpanderExtension `codeBlockExpanderExt

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

    ensureAttrDeclIsMeta `code_block declName k

    let n ← mkFreshUserName <| declName ++ `code_block

    let ((e, t), _) ← Meta.MetaM.run (ctx := {}) (s := {}) do
      let e ← Meta.mkAppM ``toCodeBlock #[.const declName []]
      let e ← instantiateMVars e
      let t ← Meta.inferType e


      match_expr e with
      | toCodeBlock ty _ _ => saveSignature n ty
      | _ => pure ()

      pure (e, t)

    let decl := Declaration.defnDecl {
      name := n,
      levelParams := [],
      type := t,
      value := e,
      hints := .opaque,
      safety := .safe
    }
    addDecl decl

    if (← getEnv).header.isModule then
      modifyEnv (markMeta · n)

    compileDecl decl

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
public opaque codeBlockExpandersFor (x : Name) : DocElabM (Array (CodeBlockExpander × Option String × Option SigDoc))

private def registeredCodeBlockNamesImpl : DocElabM (Array Name) :=
  registeredExpanderNames codeBlockExpanderExt codeBlockExpanderAttr

@[implemented_by registeredCodeBlockNamesImpl]
public opaque registeredCodeBlockNames : DocElabM (Array Name)

public abbrev DirectiveExpander := Array Arg → TSyntaxArray `block → DocElabM (Array (TSyntax `term))

public abbrev DirectiveExpanderOf α := α → TSyntaxArray `block → DocElabM Term


initialize directiveExpanderAttr : KeyedDeclsAttribute DirectiveExpander ←
  mkDocExpanderAttribute `directive_expander ``DirectiveExpander "Indicates that this function is used to implement a given directive" `directiveExpanderAttr

public def toDirective {α : Type} [FromArgs α DocElabM] (expander : α → TSyntaxArray `block → DocElabM Term) : DirectiveExpander :=
  fun args blocks => do
    let v ← ArgParse.parse args
    return #[← expander v blocks]

syntax (name := directive) "directive " (ident)? : attr

initialize directiveExpanderExt : ExpanderExtension ←
  mkExpanderExtension `directiveExpanderExt

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

    ensureAttrDeclIsMeta `directive declName k

    let n ← mkFreshUserName <| declName ++ `directive

    let ((e, t), _) ← Meta.MetaM.run (ctx := {}) (s := {}) do
      let e ← Meta.mkAppM ``toDirective #[.const declName []]
      let e ← instantiateMVars e
      let t ← Meta.inferType e


      match_expr e with
      | toDirective ty _ _ => saveSignature n ty
      | _ => pure ()

      pure (e, t)

    let decl := Declaration.defnDecl {
      name := n,
      levelParams := [],
      type := t,
      value := e,
      hints := .opaque,
      safety := .safe
    }
    addDecl decl

    if (← getEnv).header.isModule then
      modifyEnv (markMeta · n)

    compileDecl decl

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
public opaque directiveExpandersFor (x : Name) : DocElabM (Array (DirectiveExpander × Option String × Option SigDoc))

private def registeredDirectiveNamesImpl : DocElabM (Array Name) :=
  registeredExpanderNames directiveExpanderExt directiveExpanderAttr

@[implemented_by registeredDirectiveNamesImpl]
public opaque registeredDirectiveNames : DocElabM (Array Name)


public abbrev BlockCommandExpander := Array Arg → DocElabM (Array (TSyntax `term))

public abbrev BlockCommandOf α := α → DocElabM Term

initialize blockCommandExpanderAttr : KeyedDeclsAttribute BlockCommandExpander ←
  mkDocExpanderAttribute `block_command_expander ``BlockCommandExpander "Indicates that this function is used to implement a given block-level command" `blockCommandExpanderAttr

public def toBlockCommand {α : Type} [FromArgs α DocElabM] (expander : α → DocElabM Term) : BlockCommandExpander :=
  fun args => do
    let v ← ArgParse.parse args
    return #[← expander v]

syntax (name := block_command) "block_command " (ident)? : attr

initialize blockCommandExpanderExt : ExpanderExtension ←
  mkExpanderExtension `blockCommandExpanderExt

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

    ensureAttrDeclIsMeta `block_command declName k

    let n ← mkFreshUserName <| declName ++ `block_command

    let ((e, t), _) ← Meta.MetaM.run (ctx := {}) (s := {}) do
      let e ← Meta.mkAppM ``toBlockCommand #[.const declName []]
      let e ← instantiateMVars e
      let t ← Meta.inferType e

      match_expr e with
      | toBlockCommand ty _ _ => saveSignature n ty
      | _ => pure ()

      pure (e, t)

    let decl := Declaration.defnDecl {
      name := n,
      levelParams := [],
      type := t,
      value := e,
      hints := .opaque,
      safety := .safe
    }
    addDecl decl

    if (← getEnv).header.isModule then
      modifyEnv (markMeta · n)

    compileDecl decl

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
public opaque blockCommandExpandersFor (x : Name) : DocElabM (Array (BlockCommandExpander × Option String × Option SigDoc))

private def registeredBlockCommandNamesImpl : DocElabM (Array Name) :=
  registeredExpanderNames blockCommandExpanderExt blockCommandExpanderAttr

@[implemented_by registeredBlockCommandNamesImpl]
public opaque registeredBlockCommandNames : DocElabM (Array Name)
