module

public import MD4Lean
public import Verso.Doc.Elab.Monad
import VersoManual.Docstring.Config
import VersoManual.HighlightedCode
import VersoManual.Markdown
public import VersoManual.Basic
import SubVerso.Highlighting
import Verso.Code.Highlighted
import Lean.Data.Json.FromToJson.Basic
import Lean.DocString
import Lean.Elab.Tactic.Doc
import Verso.Doc.DocName

public section

open Verso.Doc.Elab
open SubVerso.Highlighting
open Lean

namespace Verso.Genre.Manual

/-- Finds the minimum indentation column across non-blank lines in a string. -/
def indentColumn (str : String) : Nat := Id.run do
  let mut i : Option Nat := none
  for line in str.splitToList (· == '\n') do
    let leading := line.takeWhile Char.isWhitespace
    if leading == line.toSlice then continue
    let leading := leading.copy
    if let some i' := i then
      if leading.length < i' then i := some leading.length
    else i := some leading.length
  return i.getD 0

def leanFromMarkdown := ()

def Inline.leanFromMarkdown (hls : Highlighted) : Inline where
  name := ``Verso.Genre.Manual.leanFromMarkdown
  data := ToJson.toJson hls

def Block.leanFromMarkdown (hls : Highlighted) : Block where
  name := ``Verso.Genre.Manual.leanFromMarkdown
  data := ToJson.toJson hls


@[inline_extension leanFromMarkdown]
def leanFromMarkdown.inlinedescr : InlineDescr := withHighlighting {
  traverse _id _data _ := pure none
  toTeX := some <| fun go _ _ content => content.mapM go
  toHtml :=
    open Verso.Output Html in
    open Verso.Doc.Html in
    some <| fun _ _ data _ => do
      match FromJson.fromJson? (α := Highlighted) data with
      | .error err =>
        HtmlT.logError <| "Couldn't deserialize Lean code while rendering inline HTML: " ++ err
        pure .empty
      | .ok (hl : Highlighted) =>
        hl.inlineHtml (g := Manual) "docstring-examples"
}

@[block_extension leanFromMarkdown]
def leanFromMarkdown.blockdescr : BlockDescr := withHighlighting {
  traverse _id _data _ := pure none
  toTeX :=
    some <| fun _goI goB _ _ content => do
      pure <| .seq <| ← content.mapM fun b => do
        pure <| .seq #[← goB b, .raw "\n"]
  toHtml :=
    open Verso.Output Html in
    open Verso.Doc.Html in
    some <| fun _ _ _ data _ => do
      match FromJson.fromJson? (α := Highlighted) data with
      | .error err =>
        HtmlT.logError <| "Couldn't deserialize Lean code while rendering inline HTML: " ++ err
        pure .empty
      | .ok (hl : Highlighted) =>
        hl.blockHtml (g := Manual) "docstring-examples"
}

namespace Block.Docstring


open Lean Elab Term in
def tryElabBlockCodeCommand (str : String) (ignoreElabErrors := false) : DocElabM Term := do
    let loc := (← getRef).getPos?.map (← getFileMap).utf8PosToLspPos
    let src :=
      if let some ⟨line, col⟩ := loc then s!"<docstring at {← getFileName}:{line}:{col}>"
      else s!"<docstring at {← getFileName} (unknown line)>"

    let ictx := Parser.mkInputContext str src
    let cctx : Command.Context := { fileName := ← getFileName, fileMap := FileMap.ofString str, snap? := none, cancelTk? := none}

    let mut cmdState : Command.State := {env := ← getEnv, maxRecDepth := ← MonadRecDepth.getMaxRecDepth, scopes := [{header := ""}]}
    let mut pstate := {pos := 0, recovering := false}
    let mut cmds := #[]

    repeat
      let scope := cmdState.scopes.head!
      let pmctx := { env := cmdState.env, options := scope.opts, currNamespace := scope.currNamespace, openDecls := scope.openDecls }
      let (cmd, ps', messages) := Parser.parseCommand ictx pmctx pstate cmdState.messages
      cmds := cmds.push cmd
      pstate := ps'
      cmdState := {cmdState with messages := messages}

      cmdState ← withInfoTreeContext (mkInfoTree := pure ∘ InfoTree.node (.ofCommandInfo {elaborator := `Manual.Meta.lean, stx := cmd})) do
        match (← liftM <| EIO.toIO' <| (Command.elabCommand cmd cctx).run cmdState) with
        | Except.error e =>
          unless ignoreElabErrors do Lean.logError e.toMessageData
          return cmdState
        | Except.ok ((), s) => return s

      if Parser.isTerminalCommand cmd then break

    if cmdState.messages.hasErrors then
      throwError "Errors found in command"

    let hls ← DocElabM.withFileMap (.ofString str) do
      let mut hls := Highlighted.empty
      for cmd in cmds do
        hls := hls ++ (← highlight cmd cmdState.messages.toArray cmdState.infoState.trees)
      pure <| hls.deIndent (indentColumn str)

    ``(Verso.Doc.Block.other (Block.leanFromMarkdown $(quote hls)) #[Verso.Doc.Block.code $(quote str)])


open Lean Elab Term in
def tryElabInlineCodeName (str : String) : DocElabM Term := do
  let str := str.trimAscii
  let x := str.toName
  if x.toString.toSlice == str then
    let stx := mkIdent x
    let n ← realizeGlobalConstNoOverload stx
    let str := str.copy
    let hl : Highlighted ← constTok n str
    ``(Verso.Doc.Inline.other (Inline.leanFromMarkdown $(quote hl)) #[Verso.Doc.Inline.code $(quote str)])
  else
    throwError "Not a name: '{str}'"
where
  constTok {m} [Monad m] [MonadEnv m] [MonadLiftT MetaM m] [MonadLiftT IO m]
      (name : Name) (str : String) :
      m Highlighted := do
    let docs ← findDocString? (← getEnv) name
    let sig := toString (← (PrettyPrinter.ppSignature name)).1
    pure <| .token ⟨.const name sig docs false none, str⟩

open Lean Elab Term in
private def attempt (str : String) (xs : List (String → DocElabM α)) : DocElabM α := do
  match xs with
  | [] => throwError "No attempt succeeded"
  | [x] => x str
  | x::y::xs =>
    let info ← getInfoState
    try
      setInfoState {}
      x str
    catch e =>
      if isAutoBoundImplicitLocalException? e |>.isSome then
        throw e
      else attempt str (y::xs)
    finally
      setInfoState info

open Lean Elab Term in
def tryParseInlineCodeTactic (str : String) : DocElabM Term := do
  let loc := (← getRef).getPos?.map (← getFileMap).utf8PosToLspPos
  let src :=
    if let some ⟨line, col⟩ := loc then s!"<docstring at {← getFileName}:{line}:{col}>"
    else s!"<docstring at {← getFileName} (unknown line)>"
  match Parser.runParserCategory (← getEnv) `tactic str src with
  | .error e => throw (.error (← getRef) e)
  | .ok stx => DocElabM.withFileMap (.ofString str) <| do
    -- TODO try actually running the tactic - if the parameters are simple enough, then it may work
    -- and give better highlights
    let hls ← highlight stx #[] (PersistentArray.empty)
    ``(Verso.Doc.Inline.other (Inline.leanFromMarkdown $(quote hls)) #[Verso.Doc.Inline.code $(quote str)])

open Lean Elab Term in
def tryInlineOption (str : String) : DocElabM Term := do
  let optName := str.trimAscii.toName
  let optDecl ← getOptionDecl optName
  let hl : Highlighted := optTok optName optDecl.declName optDecl.descr
  ``(Verso.Doc.Inline.other (Inline.leanFromMarkdown $(quote hl)) #[Verso.Doc.Inline.code $(quote str)])
where
  optTok (name declName : Name) (descr : String) : Highlighted :=
    .token ⟨.option name declName descr, name.toString⟩

open Lean Elab in
def tryTacticName (tactics : Array Tactic.Doc.TacticDoc) (str : String) : DocElabM Term := do
  for t in tactics do
    if t.userName == str then
      let hl : Highlighted := tacToken t
      return ← ``(Verso.Doc.Inline.other (Inline.leanFromMarkdown $(quote hl)) #[Verso.Doc.Inline.code $(quote str)])
  throwError "Not a tactic name: {str}"
where
  tacToken (t : Lean.Elab.Tactic.Doc.TacticDoc) : Highlighted :=
    .token ⟨.keyword t.internalName none t.docString, str⟩

open Lean Elab Term in
open Lean.Parser in
def tryHighlightKeywords (extraKeywords : Array String) (str : String) : DocElabM Term := do
  let loc := (← getRef).getPos?.map (← getFileMap).utf8PosToLspPos
  let src :=
    if let some ⟨line, col⟩ := loc then s!"<docstring at {← getFileName}:{line}:{col}>"
    else s!"<docstring at {← getFileName} (unknown line)>"
  let p : Parser := {fn := simpleFn}
  match runParser extraKeywords (← getEnv) (← getOptions) p str src (prec := 0) with
  | .error _e => throwError "Not keyword-highlightable"
  | .ok stx => DocElabM.withFileMap (.ofString str) <| do
    let hls ← highlight stx #[] (PersistentArray.empty)
    ``(Verso.Doc.Inline.other (Inline.leanFromMarkdown $(quote hls)) #[Verso.Doc.Inline.code $(quote str)])
where

  simpleFn := andthenFn whitespace <| nodeFn nullKind <| manyFn tokenFn

  runParser (extraKeywords : Array String) (env : Environment) (opts : Lean.Options) (p : Parser) (input : String) (fileName : String := "<example>") (prec : Nat := 0) : Except (List (Position × String)) Syntax :=
    let ictx := mkInputContext input fileName
    let p' := adaptCacheableContext ({· with prec}) p
    let tokens := extraKeywords.foldl (init := getTokenTable env) (fun x tk => x.insert tk tk)
    let s := p'.fn.run ictx { env, options := opts } tokens (mkParserState input)
    if !s.allErrors.isEmpty then
      Except.error (toErrorMsg ictx s)
    else if ictx.atEnd s.pos then
      Except.ok s.stxStack.back
    else
      Except.error (toErrorMsg ictx (s.mkError "end of input"))

  toErrorMsg (ctx : InputContext) (s : ParserState) : List (Position × String) := Id.run do
    let mut errs := []
    for (pos, _stk, err) in s.allErrors do
      let pos := ctx.fileMap.toPosition pos
      errs := (pos, toString err) :: errs
    errs.reverse


declare_syntax_cat braces_attr
syntax (name := plain) attr : braces_attr
syntax (name := bracketed) "[" attr "]" : braces_attr
syntax (name := atBracketed) "@[" attr "]" : braces_attr

private def getAttr : Syntax → Syntax
  | `(plain| $a)
  | `(bracketed| [ $a ] )
  | `(atBracketed| @[ $a ]) => a
  | _ => .missing

open Lean Elab Term in
def tryParseInlineCodeAttribute (validate := true) (str : String) : DocElabM Term := do
  let loc := (← getRef).getPos?.map (← getFileMap).utf8PosToLspPos
  let src :=
    if let some ⟨line, col⟩ := loc then s!"<docstring at {← getFileName}:{line}:{col}>"
    else s!"<docstring at {← getFileName} (unknown line)>"
  match Parser.runParserCategory (← getEnv) `braces_attr str src with
  | .error e => throw (.error (← getRef) e)
  | .ok stx => DocElabM.withFileMap (.ofString str) <| do
    let inner := getAttr stx
    if validate then
      let attrName ←
        match inner.getKind with
        | `Lean.Parser.Attr.simple => pure inner[0].getId
        | .str (.str (.str (.str .anonymous "Lean") "Parser") "Attr") k => pure k.toName
        | other =>
          let allAttrs := attributeExtension.getState (← getEnv) |>.map |>.toArray |>.map (·.fst) |>.qsort (·.toString < ·.toString)
          throwError "Failed to process attribute kind: {stx.getKind} {isAttribute (← getEnv) stx.getKind} {allAttrs |> repr}"
      match getAttributeImpl (← getEnv) attrName with
      | .error e => throwError e
      | .ok _ =>
        let hls ← highlight stx #[] (PersistentArray.empty)
        ``(Verso.Doc.Inline.other (Inline.leanFromMarkdown $(quote hls)) #[Verso.Doc.Inline.code $(quote str)])
    else
      let hls ← highlight stx #[] (PersistentArray.empty)
      ``(Verso.Doc.Inline.other (Inline.leanFromMarkdown $(quote hls)) #[Verso.Doc.Inline.code $(quote str)])

open Lean Elab Term in
def tryElabInlineCodeUsing (elabs : List (String → DocElabM Term))
    (priorWord : Option String) (str : String) : DocElabM Term := do
  -- Don't try to show Lake commands as terms
  if "lake ".isPrefixOf str then return (← ``(Verso.Doc.Inline.code $(quote str)))
  try
    attempt str <| wordElab priorWord ++ elabs
  catch
    | .error ref e =>
      logWarningAt ref e
      ``(Verso.Doc.Inline.code $(quote str))
    | e =>
      if isAutoBoundImplicitLocalException? e |>.isSome then
        throw e
      else
        logWarning m!"Internal exception uncaught: {e.toMessageData}"
        ``(Verso.Doc.Inline.code $(quote str))
where
  wordElab
    | some "attribute" => [tryParseInlineCodeAttribute (validate := false)]
    | some "tactic" => [tryParseInlineCodeTactic]
    | _ => []

open Lean Elab Term in
def tryElabCodeTermWith (mk : Highlighted → String → DocElabM α) (str : String) (ignoreElabErrors := false) (identOnly := false) : DocElabM α := do
  let loc := (← getRef).getPos?.map (← getFileMap).utf8PosToLspPos
  let src :=
    if let some ⟨line, col⟩ := loc then s!"<docstring at {← getFileName}:{line}:{col}>"
    else s!"<docstring at {← getFileName} (unknown line)>"
  match Parser.runParserCategory (← getEnv) `term str src with
  | .error e => throw (.error (← getRef) e)
  | .ok stx => DocElabM.withFileMap (.ofString str) <| do
    if stx.isIdent && (← readThe Term.Context).autoBoundImplicitContext.isSome then
      throwError m!"Didn't elaborate {stx} as term to avoid spurious auto-implicits"
    if identOnly && !stx.isIdent then
      throwError m!"Didn't elaborate {stx} as term because only identifiers are wanted here"
    let (newMsgs, tree, _e) ← do
      let initMsgs ← Core.getMessageLog
      try
        Core.resetMessageLog
        -- TODO open decls/current namespace
        let (tree', e') ← do
          let e ← Elab.Term.elabTerm (catchExPostpone := true) stx none
          Term.synthesizeSyntheticMVarsNoPostponing
          let e' ← Term.levelMVarToParam (← instantiateMVars e)
          Term.synthesizeSyntheticMVarsNoPostponing
          let e' ← instantiateMVars e'
          let ctx := PartialContextInfo.commandCtx {
            env := ← getEnv, fileMap := ← getFileMap, mctx := ← getMCtx, currNamespace := ← getCurrNamespace,
            openDecls := ← getOpenDecls, options := ← getOptions, ngen := ← getNGen
          }
          pure (InfoTree.context ctx (.node (Info.ofCommandInfo ⟨`Verso.Genre.Manual.docstring, (← getRef)⟩) (← getInfoState).trees), e')
        pure (← Core.getMessageLog, tree', e')
      finally
        Core.setMessageLog initMsgs
    if newMsgs.hasErrors && !ignoreElabErrors then
      for msg in newMsgs.errorsToWarnings.toArray do
        logMessage msg
      throwError m!"Didn't elaborate {stx} as term"

    let hls ← highlight stx #[] (PersistentArray.empty.push tree)
    mk hls str


declare_syntax_cat doc_metavar
syntax (name := docMetavar) term ":" term : doc_metavar


open Lean Elab Term in
def tryElabCodeMetavarTermWith (mk : Highlighted → String → DocElabM α) (str : String) (ignoreElabErrors := false) : DocElabM α := do
  let loc := (← getRef).getPos?.map (← getFileMap).utf8PosToLspPos
  let src :=
    if let some ⟨line, col⟩ := loc then s!"<docstring at {← getFileName}:{line}:{col}>"
    else s!"<docstring at {← getFileName} (unknown line)>"
  match Parser.runParserCategory (← getEnv) `doc_metavar str src with
  | .error e => throw (.error (← getRef) e)
  | .ok stx => DocElabM.withFileMap (.ofString str) <| do
    if let `(doc_metavar|$pat:term : $ty:term) := stx then
      let (newMsgs, tree, _e') ← show TermElabM _ from do
        let initMsgs ← Core.getMessageLog
        try
          Core.resetMessageLog
          -- TODO open decls/current namespace
          let (tree', e') ← do
            let stx' : Term ← `(($pat : $ty))
            let e ← withReader ({· with autoBoundImplicitContext := some ⟨true, {}⟩}) <| elabTerm stx' none
            Term.synthesizeSyntheticMVarsNoPostponing
            let e' ← Term.levelMVarToParam (← instantiateMVars e)
            Term.synthesizeSyntheticMVarsNoPostponing
            let e' ← instantiateMVars e'
            let ctx := PartialContextInfo.commandCtx {
              env := ← getEnv, fileMap := ← getFileMap, mctx := ← getMCtx, currNamespace := ← getCurrNamespace,
              openDecls := ← getOpenDecls, options := ← getOptions, ngen := ← getNGen
            }
            pure (InfoTree.context ctx (.node (Info.ofCommandInfo ⟨`Verso.Genre.Manual.docstring, stx⟩) (← getInfoState).trees), e')
          pure (← Core.getMessageLog, tree', e')
        finally
          Core.setMessageLog initMsgs
      if newMsgs.hasErrors && !ignoreElabErrors then
        for msg in newMsgs.errorsToWarnings.toArray do
          logMessage msg
        throwError m!"Didn't elaborate {pat} : {ty} as term"

      let hls ← highlight stx #[] (PersistentArray.empty.push tree)
      mk hls str
    else
      throwError "Not a doc metavar: {stx}"

open Lean Elab Term in
def tryElabInlineCodeTerm (str : String) (ignoreElabErrors := false) (identOnly := false) : DocElabM Term :=
  tryElabCodeTermWith (ignoreElabErrors := ignoreElabErrors) (identOnly := identOnly) (fun hls str =>
    ``(Verso.Doc.Inline.other (Inline.leanFromMarkdown $(quote hls)) #[Verso.Doc.Inline.code $(quote str)]))
    str

open Lean Elab Term in
def tryElabInlineCodeMetavarTerm (str : String) (ignoreElabErrors := false) : DocElabM Term :=
  tryElabCodeMetavarTermWith (ignoreElabErrors := ignoreElabErrors) (fun hls str =>
    ``(Verso.Doc.Inline.other (Inline.leanFromMarkdown $(quote hls)) #[Verso.Doc.Inline.code $(quote str)]))
    str

open Lean Elab Term in
def tryElabBlockCodeTerm (str : String)  (ignoreElabErrors := false) : DocElabM Term :=
  tryElabCodeTermWith (ignoreElabErrors := ignoreElabErrors) (fun hls str =>
    ``(Verso.Doc.Block.other (Block.leanFromMarkdown $(quote hls)) #[Verso.Doc.Block.code $(quote str)]))
    str


open Elab in
/--
Like `tryElabInlineCode`, but prefers producing un-highlighted code blocks to
displaying metavariable-typed terms (e.g., through auto-bound implicits or
elaboration failures).
-/
def tryElabInlineCodeStrict (allTactics : Array Tactic.Doc.TacticDoc) (extraKeywords : Array String)
    (priorWord : Option String) (str : String) : DocElabM Term :=
  tryElabInlineCodeUsing [
    tryElabInlineCodeName,
    -- When identifiers have the same name as tactics, prefer the identifiers
    tryElabInlineCodeTerm (identOnly := true),
    tryParseInlineCodeTactic,
    tryParseInlineCodeAttribute (validate := true),
    tryInlineOption,
    tryElabInlineCodeTerm,
    tryElabInlineCodeMetavarTerm,
    tryTacticName allTactics,
    tryHighlightKeywords extraKeywords
  ] priorWord str

open Lean Elab Term in
def tryElabBlockCode (_info? _lang? : Option String) (str : String) : DocElabM Term := do
  try
    attempt str [
      tryElabBlockCodeCommand,
      tryElabBlockCodeTerm,
      tryElabBlockCodeCommand (ignoreElabErrors := true),
      withTheReader Term.Context (fun ctx => {ctx with autoBoundImplicitContext := some ⟨true, {}⟩}) ∘
        tryElabBlockCodeTerm (ignoreElabErrors := true)
    ]
  catch
    | .error ref e =>
      logWarningAt ref e
      ``(Verso.Doc.Block.code $(quote str))
    | e =>
      if isAutoBoundImplicitLocalException? e |>.isSome then
        throw e
      else
        logWarning m!"Internal exception uncaught: {e.toMessageData}"
        ``(Verso.Doc.Block.code $(quote str))



open Elab in
def tryElabInlineCode (allTactics : Array Tactic.Doc.TacticDoc) (extraKeywords : Array String)
    (priorWord : Option String) (str : String) : DocElabM Term :=
  tryElabInlineCodeUsing [
    tryElabInlineCodeName,
    -- When identifiers have the same name as tactics, prefer the identifiers
    tryElabInlineCodeTerm (identOnly := true),
    tryParseInlineCodeTactic,
    tryParseInlineCodeAttribute (validate := true),
    tryInlineOption,
    tryElabInlineCodeTerm,
    tryElabInlineCodeMetavarTerm,
    tryTacticName allTactics,
    withTheReader Term.Context (fun ctx => {ctx with autoBoundImplicitContext := some ⟨true, {}⟩}) ∘ tryElabInlineCodeTerm,
    tryElabInlineCodeTerm (ignoreElabErrors := true),
    tryHighlightKeywords extraKeywords
  ] priorWord str


open Lean Elab Term in
/--
Heuristically elaborate Lean fragments in Markdown code. The provided names are used as signatures,
from left to right, with the names bound by the signature being available in the local scope in
which the Lean fragments are elaborated.
-/
public def blockFromMarkdownWithLean (names : List Name) (b : MD4Lean.Block) : DocElabM Term := do
  unless (← Docstring.getElabMarkdown) do
    return (← Markdown.blockFromMarkdown b (handleHeaders := Markdown.strongEmphHeaders))
  let tactics ← Elab.Tactic.Doc.allTacticDocs
  let keywords := tactics.map (·.userName)
  try
    match names with
    | decl :: decls =>
      -- This brings the parameters into scope, so the term elaboration version catches them!
      Meta.forallTelescopeReducing (← getConstInfo decl).type fun _ _ =>
        blockFromMarkdownWithLean decls b
    | [] =>
      -- It'd be silly for some weird edge case to block on this feature...
      let rec loop (max : Nat) (s : SavedState) : DocElabM Term := do
        match max with
        | k + 1 =>
          try
            let res ←
              Markdown.blockFromMarkdown b
                (handleHeaders := Markdown.strongEmphHeaders)
                (elabInlineCode := tryElabInlineCode tactics keywords)
                (elabBlockCode := tryElabBlockCode)
            synthesizeSyntheticMVarsUsingDefault

            discard <| addAutoBoundImplicits #[] (inlayHintPos? := none)

            return res
          catch e =>
            if let some n := isAutoBoundImplicitLocalException? e then
              s.restore (restoreInfo := true)
              Meta.withLocalDecl n .implicit (← Meta.mkFreshTypeMVar) fun x =>
                withTheReader Term.Context (fun ctx => { ctx with autoBoundImplicitContext := ctx.autoBoundImplicitContext.map (fun c => {c with boundVariables := c.boundVariables.push x }) }) do
                  loop k (← (saveState : TermElabM _))
            else throw e
        | 0 => throwError "Ran out of local name attempts"
      let s ← (saveState : TermElabM _)
      try
        loop 40 s
      finally
        (s.restore : TermElabM _)
  catch _ =>
    Markdown.blockFromMarkdown b
      (handleHeaders := Markdown.strongEmphHeaders)
