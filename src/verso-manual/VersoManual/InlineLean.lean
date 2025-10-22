/-
Copyright (c) 2024-2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import Lean.Elab.Command
import Lean.Elab.InfoTree

import SubVerso.Highlighting
import SubVerso.Examples

import Verso
import Verso.CodeTable

import VersoManual.Basic
import VersoManual.HighlightedCode
import VersoManual.InlineLean.Block
import VersoManual.InlineLean.IO
import VersoManual.InlineLean.LongLines
import VersoManual.InlineLean.Option
import VersoManual.InlineLean.Outputs
import VersoManual.InlineLean.Scopes
import VersoManual.InlineLean.Signature
import VersoManual.InlineLean.SyntaxError


open Verso ArgParse Doc Elab Genre.Manual Html Code Highlighted.WebAssets ExpectString
open Lean Elab
open SubVerso.Highlighting

open Verso.SyntaxUtils (parserInputString runParserCategory' SyntaxError)

open Lean.Doc.Syntax
open Lean.Elab.Tactic.GuardMsgs

namespace Verso.Genre.Manual.InlineLean

inline_extension Inline.lean (hls : Highlighted) via withHighlighting where
  data :=
    let defined := definedNames hls
    Json.arr #[ToJson.toJson hls, ToJson.toJson defined]

  traverse id data _ := do
    let .arr #[_, defined] := data
      | logError "Expected two-element JSON for Lean code" *> pure none
    match FromJson.fromJson? defined with
    | .error err =>
      logError <| "Couldn't deserialize Lean code while traversing inline example: " ++ err
      pure none
    | .ok (defs : Array (Name × String)) =>
      saveExampleDefs id defs
      pure none
  toTeX :=
    some <| fun go _ _ content => do
      pure <| .seq <| ← content.mapM fun b => do
        pure <| .seq #[← go b, .raw "\n"]
  toHtml :=
    open Verso.Output.Html in
    some <| fun _ _ data _ => do
      let .arr #[hlJson, _] := data
        | HtmlT.logError "Expected two-element JSON for Lean code" *> pure .empty
      match FromJson.fromJson? hlJson with
      | .error err =>
        HtmlT.logError <| "Couldn't deserialize Lean code while rendering inline HTML: " ++ err
        pure .empty
      | .ok (hl : Highlighted) =>
        hl.inlineHtml (g := Manual) "examples"


section Config

variable [Monad m] [MonadInfoTree m] [MonadLiftT CoreM m] [MonadEnv m] [MonadError m]

structure LeanBlockConfig where
  «show» : Bool
  keep : Bool
  name : Option Name
  error : Bool
  fresh : Bool

def LeanBlockConfig.parse : ArgParse m LeanBlockConfig :=
  LeanBlockConfig.mk <$> .flag `show true <*> .flag `keep true <*> .named `name .name true <*> .flag `error false <*> .flag `fresh false

instance : FromArgs LeanBlockConfig m := ⟨LeanBlockConfig.parse⟩

structure LeanInlineConfig extends LeanBlockConfig where
  /-- The expected type of the term -/
  type : Option StrLit
  /-- Universe variables allowed in the term -/
  universes : Option StrLit

def LeanInlineConfig.parse : ArgParse m LeanInlineConfig :=
  LeanInlineConfig.mk <$> LeanBlockConfig.parse <*> .named `type strLit true <*> .named `universes strLit true
where
  strLit : ValDesc m StrLit := {
    description := "string literal containing an expected type",
    signature := .String
    get
      | .str s => pure s
      | other => throwError "Expected string, got {repr other}"
  }

instance : FromArgs LeanInlineConfig m := ⟨LeanInlineConfig.parse⟩

end Config


open Verso.Genre.Manual.InlineLean.Scopes (getScopes setScopes runWithOpenDecls runWithVariables)

private def abbrevFirstLine (width : Nat) (str : String) : String :=
  let str := str.trimLeft
  let short := str.take width |>.replace "\n" "⏎"
  if short == str then short else short ++ "…"

def LeanBlockConfig.outlineMeta : LeanBlockConfig → String
  | {«show», error, ..} =>
    match «show», error with
    | true, true => " (error)"
    | false, true => " (hidden, error)"
    | false, false => " (hidden)"
    | _, _ => " "

def firstToken? (stx : Syntax) : Option Syntax :=
  stx.find? fun
    | .ident info .. => usable info
    | .atom info .. => usable info
    | _ => false
where
  usable
    | .original .. => true
    | _ => false

/--
Report messages that result from elaboration of inline Lean.

Messages that don't require immediate attention are logged silently to reduce the amount of
irrelevant output in build logs.

If `errorExpected` is `none`, then the messages are logged as-is, and errors are not silent. If it
is `some false`, then the author expected no errors; in this case, messages are logged as in the
`none` case and an additional error is thrown. If it is `some true`, then errors are downgraded to
warnings and all messages are logged silently.
-/
def reportMessages {m} [Monad m] [MonadLog m] [MonadError m]
    (errorExpected : Option Bool) (blame : Syntax) (messages : MessageLog) :
    m Unit := do
  match errorExpected with
  | none =>
    for msg in messages.toArray do
      logMessage {msg with
        isSilent := msg.isSilent || msg.severity != .error
      }
  | some true =>
    if messages.hasErrors then
      for msg in messages.errorsToWarnings.toArray do
        logMessage {msg with isSilent := true}
    else
      throwErrorAt blame "Error expected in code block, but none occurred"
  | some false =>
    for msg in messages.toArray do
      logMessage {msg with isSilent := msg.isSilent || msg.severity != .error}
    if messages.hasErrors then
      throwErrorAt blame "No error expected in code block, one occurred"

def hlFromGlobalExport! (exportTable : SubVerso.Highlighting.Export) (key : SubVerso.Highlighting.Export.Key) :=
  match exportTable.toHighlighted key with
  | .error e => panic! s!"Unable to export key {key}: {e}"
  | .ok v => v

def codeTableName [Monad m] [MonadQuotation m] (name : Name) : m Term :=
  ``(CodeTable.CodeTable.is $(quote name) (self := _))

/--
Produces the syntax of an expression that denotes the `hls` value. Specifically,
within the DocElabM monad, `← quoteHighlightViaSerialization hls` will result in a `Term` that
represents the same highlight as `quote hls`, but will hopefully produce smaller code because of
quoting a compressed version of the highlighted code.
-/
private def quoteHighlightViaSerialization (hls : Highlighted) : DocElabM Term := do
  let docElabState ← get
  if let .some (name, exportTable) := docElabState.exportingTable then
    let (key, exportTable) := hls.export.run exportTable
    set { docElabState with exportingTable := some (name, exportTable) }
    let codeTableSyn ← ``(CodeTable.CodeTable.is $(quote name) (self := _))
    ``(hlFromGlobalExport! $(codeTableSyn) $(quote key))
  else
    let repr := hlToExport hls
    ``(hlFromExport! $(quote repr))

/--
De-indents and returns (syntax of) a Block representation containing highlighted Lean code.
The argument `hls` must be a highlighting of the parsed string `str`.
-/
private def toHighlightedLeanBlock (shouldShow : Bool) (hls : Highlighted) (str: StrLit) : DocElabM Term := do
  if !shouldShow then
    return ← ``(Block.concat #[])

  let col? := (← getRef).getPos? |>.map (← getFileMap).utf8PosToLspPos |>.map (·.character)
  let hls := match col? with
  | .none => hls
  | .some col => hls.deIndent col

  let range := Syntax.getRange? str
  let range := range.map (← getFileMap).utf8RangeToLspRange
  ``(Block.other (Block.lean $(← quoteHighlightViaSerialization hls) (some $(quote (← getFileName))) $(quote range)) #[Block.code $(quote str.getString)])

/--
Returns (syntax of) an Inline representation containing highlighted Lean code.
The argument `hls` must be a highlighting of the parsed string `str`.
-/
private def toHighlightedLeanInline (shouldShow : Bool) (hls : Highlighted) (str : StrLit) : DocElabM Term := do
  if !shouldShow then
    return ← ``(Inline.concat #[])

  ``(Inline.other (Verso.Genre.Manual.InlineLean.Inline.lean $(← quoteHighlightViaSerialization hls)) #[Inline.code $(quote str.getString)])


/--
Elaborates the provided Lean command in the context of the current Verso module.
-/
@[code_block]
def lean : CodeBlockExpanderOf LeanBlockConfig
  | config, str => withoutAsync <| do

    PointOfInterest.save (← getRef) ((config.name.map (·.toString)).getD (abbrevFirstLine 20 str.getString))
      (kind := Lsp.SymbolKind.file)
      (detail? := some ("Lean code" ++ config.outlineMeta))

    let col? := (← getRef).getPos? |>.map (← getFileMap).utf8PosToLspPos |>.map (·.character)

    let origScopes ← if config.fresh then pure [{header := ""}] else getScopes

    -- Turn off async elaboration so that info trees and messages are available when highlighting syntax
    let origScopes := origScopes.modifyHead fun sc =>
      { sc with opts := pp.tagAppFns.set (Elab.async.set sc.opts false) true }

    let altStr ← parserInputString str

    let ictx := Parser.mkInputContext altStr (← getFileName)
    let cctx : Command.Context := { fileName := ← getFileName, fileMap := FileMap.ofString altStr, snap? := none, cancelTk? := none}

    let mut cmdState : Command.State := {env := ← getEnv, maxRecDepth := ← MonadRecDepth.getMaxRecDepth, scopes := origScopes}
    let mut pstate := {pos := 0, recovering := false}
    let mut cmds := #[]

    repeat
      let scope := cmdState.scopes.head!
      let pmctx := { env := cmdState.env, options := scope.opts, currNamespace := scope.currNamespace, openDecls := scope.openDecls }
      let (cmd, ps', messages) := Parser.parseCommand ictx pmctx pstate cmdState.messages
      cmds := cmds.push cmd
      pstate := ps'
      cmdState := {cmdState with messages := messages}


      cmdState ← withInfoTreeContext (mkInfoTree := pure ∘ InfoTree.node (.ofCommandInfo {elaborator := `Manual.Meta.lean, stx := cmd})) <|
        runCommand (Command.elabCommand cmd) cmd cctx cmdState

      if Parser.isTerminalCommand cmd then break

    let origEnv ← getEnv
    try
      setEnv cmdState.env
      setScopes cmdState.scopes

      for t in cmdState.infoState.trees do
        pushInfoTree t


      let mut hls := Highlighted.empty
      let nonSilentMsgs := cmdState.messages.toArray.filter (!·.isSilent)
      for cmd in cmds do
        hls := hls ++ (← highlight cmd nonSilentMsgs cmdState.infoState.trees)

      toHighlightedLeanBlock config.show hls str
    finally
      if !config.keep then
        setEnv origEnv

      if let some name := config.name then
        let nonSilentMsgs := cmdState.messages.toList.filter (!·.isSilent)
        let msgs ← nonSilentMsgs.mapM fun (msg : Message) => do
          let head := if msg.caption != "" then msg.caption ++ ":\n" else ""
          let msg ← highlightMessage msg
          pure { msg with contents := .append #[.text head, msg.contents] }

        saveOutputs name msgs

      reportMessages config.error str cmdState.messages

      if config.show then
        warnLongLines col? str
where
  runCommand (act : Command.CommandElabM Unit) (stx : Syntax)
      (cctx : Command.Context) (cmdState : Command.State) :
      DocElabM Command.State := do
    let (output, cmdState) ←
      match (← liftM <| IO.FS.withIsolatedStreams <| EIO.toIO' <| (act.run cctx).run cmdState) with
      | (output, .error e) => Lean.logError e.toMessageData; pure (output, cmdState)
      | (output, .ok ((), cmdState)) => pure (output, cmdState)

    if output.trim.isEmpty then return cmdState

    let log : MessageData → Command.CommandElabM Unit :=
      if let some tok := firstToken? stx then logInfoAt tok
      else logInfo

    match (← liftM <| EIO.toIO' <| ((log output).run cctx).run cmdState) with
    | .error _ => pure cmdState
    | .ok ((), cmdState) => pure cmdState

/--
Elaborates the provided Lean term in the context of the current Verso module.
-/
@[code_block]
def leanTerm : CodeBlockExpanderOf LeanInlineConfig
  | config, str => withoutAsync <| do

    let altStr ← parserInputString str

    let leveller :=
      if let some us := config.universes then
        let us :=
          us.getString.splitOn " " |>.filterMap fun (s : String) =>
            if s.isEmpty then none else some s.toName
        Elab.Term.withLevelNames us
      else id

    match Parser.runParserCategory (← getEnv) `term altStr (← getFileName) with
    | .error e => throwErrorAt str e
    | .ok stx =>
      let (newMsgs, tree) ← do
        let initMsgs ← Core.getMessageLog
        try
          Core.resetMessageLog

          let tree' ← runWithOpenDecls <| runWithVariables fun _vars => do
            let expectedType ← config.type.mapM fun (s : StrLit) => do
              match Parser.runParserCategory (← getEnv) `term s.getString (← getFileName) with
              | .error e => throwErrorAt stx e
              | .ok stx => withEnableInfoTree false do
                let t ← leveller <| Elab.Term.elabType stx
                Term.synthesizeSyntheticMVarsNoPostponing
                let t ← instantiateMVars t
                if t.hasExprMVar || t.hasLevelMVar then
                  throwErrorAt s "Type contains metavariables: {t}"
                pure t

            let e ← Elab.Term.elabTerm (catchExPostpone := true) stx expectedType
            Term.synthesizeSyntheticMVarsNoPostponing
            let _ ← Term.levelMVarToParam (← instantiateMVars e)

            let ctx := PartialContextInfo.commandCtx {
              env := ← getEnv, fileMap := ← getFileMap, mctx := ← getMCtx, currNamespace := ← getCurrNamespace,
              openDecls := ← getOpenDecls, options := ← getOptions, ngen := ← getNGen
            }
            pure <| InfoTree.context ctx (.node (Info.ofCommandInfo ⟨`Manual.leanInline, str⟩) (← getInfoState).trees)
          pure (← Core.getMessageLog, tree')
        finally
          Core.setMessageLog initMsgs

      if let some name := config.name then
        let msgs ← newMsgs.toList.mapM fun (msg : Message) => do
          let head := if msg.caption != "" then msg.caption ++ ":\n" else ""
          let msg ← highlightMessage msg
          pure { msg with contents := .append #[.text head, msg.contents] }

        saveOutputs name msgs

      pushInfoTree tree

      if config.error then
        if newMsgs.hasErrors then
          for msg in newMsgs.errorsToWarnings.toArray do
            logMessage msg
        else
          throwErrorAt str "Error expected in code, but none occurred"
      else
        for msg in newMsgs.toArray do
          logMessage msg

      let hls := (← highlight stx #[] (PersistentArray.empty.push tree))
      toHighlightedLeanBlock config.show hls str

/--
Elaborates the provided Lean term in the context of the current Verso module.
-/
@[role lean]
def leanInline : RoleExpanderOf LeanInlineConfig
  -- Async elab is turned off to make sure that info trees and messages are available when highlighting
  | config, inlines => withoutAsync do
    let #[arg] := inlines
      | throwError "Expected exactly one argument"
    let `(inline|code( $term:str )) := arg
      | throwErrorAt arg "Expected code literal with the example name"
    let altStr ← parserInputString term

    let leveller :=
      if let some us := config.universes then
        let us :=
          us.getString.splitOn " " |>.filterMap fun (s : String) =>
            if s.isEmpty then none else some s.toName
        Elab.Term.withLevelNames us
      else id

    match Parser.runParserCategory (← getEnv) `term altStr (← getFileName) with
    | .error e => throwErrorAt term e
    | .ok stx =>

      let (newMsgs, type, tree) ← do
        let initMsgs ← Core.getMessageLog
        try
          Core.resetMessageLog
          let (tree', t) ← runWithOpenDecls <| runWithVariables fun _ => do

            let expectedType ← config.type.mapM fun (s : StrLit) => do
              match Parser.runParserCategory (← getEnv) `term s.getString (← getFileName) with
              | .error e => throwErrorAt term e
              | .ok stx => withEnableInfoTree false do
                let t ← leveller <| Elab.Term.elabType stx
                Term.synthesizeSyntheticMVarsNoPostponing
                let t ← instantiateMVars t
                if t.hasExprMVar || t.hasLevelMVar then
                  throwErrorAt s "Type contains metavariables: {t}"
                pure t

            let e ← leveller <| Elab.Term.elabTerm (catchExPostpone := true) stx expectedType
            Term.synthesizeSyntheticMVarsNoPostponing
            let e ← Term.levelMVarToParam (← instantiateMVars e)
            let t ← Meta.inferType e >>= instantiateMVars >>= (Meta.ppExpr ·)
            let t := Std.Format.group <| (← Meta.ppExpr e) ++ (" :" ++ .line) ++ t

            Term.synthesizeSyntheticMVarsNoPostponing
            let ctx := PartialContextInfo.commandCtx {
              env := ← getEnv, fileMap := ← getFileMap, mctx := ← getMCtx, currNamespace := ← getCurrNamespace,
              openDecls := ← getOpenDecls, options := ← getOptions, ngen := ← getNGen
            }
            pure <| (InfoTree.context ctx (.node (Info.ofCommandInfo ⟨`Manual.leanInline, arg⟩) (← getInfoState).trees), t)
          pure (← Core.getMessageLog, t, tree')
        finally
          Core.setMessageLog initMsgs

      if let some name := config.name then

        let msgs ← newMsgs.toList.mapM fun (msg : Message) => do
          let head := if msg.caption != "" then msg.caption ++ ":\n" else ""
          let msg ← highlightMessage msg
          pure { msg with contents := .append #[.text head, msg.contents] }

        saveOutputs name msgs

      pushInfoTree tree

      if let `(inline|role{%$s $f $_*}%$e[$_*]) ← getRef then
        Hover.addCustomHover (mkNullNode #[s, e]) type
        Hover.addCustomHover f type

      if config.error then
        if newMsgs.hasErrors then
          for msg in newMsgs.errorsToWarnings.toArray do
            logMessage {msg with isSilent := true}
        else
          throwErrorAt term "Error expected in code block, but none occurred"
      else
        for msg in newMsgs.toArray do
          logMessage {msg with
            isSilent := msg.isSilent || msg.severity != .error
          }

      reportMessages config.error term newMsgs

      let hls := (← highlight stx #[] (PersistentArray.empty.push tree))

      toHighlightedLeanInline config.show hls term


/--
Elaborates the provided term in the current Verso context, then ensures that it's a type class that has an instance.
-/
@[role]
def inst : RoleExpanderOf LeanBlockConfig
  | config, inlines => withoutAsync <| do
    let #[arg] := inlines
      | throwError "Expected exactly one argument"
    let `(inline|code( $term:str )) := arg
      | throwErrorAt arg "Expected code literal with the example name"
    let altStr ← parserInputString term

    match Parser.runParserCategory (← getEnv) `term altStr (← getFileName) with
    | .error e => throwErrorAt term e
    | .ok stx =>
      let (newMsgs, tree) ← do
        let initMsgs ← Core.getMessageLog
        try
          Core.resetMessageLog
          let tree' ← runWithOpenDecls <| runWithVariables fun _ => do
            let e ← Elab.Term.elabTerm (catchExPostpone := true) stx none
            Term.synthesizeSyntheticMVarsNoPostponing
            let _ ← Term.levelMVarToParam (← instantiateMVars e)
            Term.synthesizeSyntheticMVarsNoPostponing
            -- TODO this is the only difference from the normal inline Lean. Abstract the commonalities out!
            discard <| Meta.synthInstance e
            let ctx := PartialContextInfo.commandCtx {
              env := ← getEnv, fileMap := ← getFileMap, mctx := ← getMCtx, currNamespace := ← getCurrNamespace,
              openDecls := ← getOpenDecls, options := ← getOptions, ngen := ← getNGen
            }
            pure <| InfoTree.context ctx (.node (Info.ofCommandInfo ⟨`Manual.leanInline, arg⟩) (← getInfoState).trees)
          pure (← Core.getMessageLog, tree')
        finally
          Core.setMessageLog initMsgs

      if let some name := config.name then
        let msgs ← newMsgs.toList.mapM fun (msg : Message) => do
          let head := if msg.caption != "" then msg.caption ++ ":\n" else ""
          let msg ← highlightMessage msg
          pure { msg with contents := .append #[.text head, msg.contents] }

        saveOutputs name msgs

      pushInfoTree tree

      reportMessages config.error term newMsgs

      let hls := (← highlight stx #[] (PersistentArray.empty.push tree))

      toHighlightedLeanInline config.show hls term

/--
Elaborates the contained document in a new section.
-/
@[directive_expander leanSection]
def leanSection : DirectiveExpander
  | args, contents => do
    let name? ← ArgParse.run ((some <$> .positional `name .string) <|> pure none) args
    let arg ← `(doc_arg| -«show»)
    let code := name?.map (s!"section {·}") |>.getD "section"
    let start ← `(block|```lean $arg | $(quote code) ```)
    let code := name?.map (s!"end {·}") |>.getD "end"
    let «end» ← `(block|```lean $arg | $(quote code) ```)
    return #[← elabBlock start] ++ (← contents.mapM elabBlock) ++ #[← elabBlock «end»]

private def getClass : MessageSeverity → String
  | .error => "error"
  | .information => "information"
  | .warning => "warning"

block_extension Block.leanOutput via withHighlighting where
  traverse _ _ _ := do
    pure none
  toTeX :=
    some <| fun _ go _ _ content => do
      pure <| .seq <| ← content.mapM fun b => do
        pure <| .seq #[← go b, .raw "\n"]
  toHtml :=
    open Verso.Output.Html in
    some <| fun _ _ _ data _ => do
      match FromJson.fromJson? data with
      | .error err =>
        HtmlT.logError <| "Couldn't deserialize Lean output while rendering HTML: " ++ err ++ "\n" ++ toString data
        pure .empty
      | .ok ((msg, summarize, expandTraces) : Highlighted.Message × Bool × List Name) =>
        msg.blockHtml summarize (expandTraces := expandTraces) (g := Manual)


structure LeanOutputConfig where
  name : Ident
  «show» : Bool := true
  severity : Option MessageSeverity
  summarize : Bool
  whitespace : WhitespaceMode
  normalizeMetas : Bool
  allowDiff : Nat
  expandTraces : List Name := []
  startAt : Option String := none
  stopAt : Option String := none

section
variable [Monad m] [MonadInfoTree m] [MonadLiftT CoreM m] [MonadEnv m] [MonadError m]

def LeanOutputConfig.parser : ArgParse m LeanOutputConfig :=
  LeanOutputConfig.mk <$>
    .positional `name output <*>
    .flag `show true <*>
    .named `severity .messageSeverity true <*>
    .flag `summarize false <*>
    .namedD `whitespace .whitespaceMode .exact <*>
    .flag `normalizeMetas true <*>
    .namedD `allowDiff .nat 0 <*>
    .many (.named `expandTrace .name false) <*>
    .named `startAt .string true <*>
    .named `stopAt .string true
where
  output : ValDesc m Ident := {
    description := "output name",
    signature := .Ident
    get := fun
      | .name x => pure x
      | other => throwError "Expected output name, got {repr other}"
  }

instance : FromArgs LeanOutputConfig m := ⟨LeanOutputConfig.parser⟩

end

private def withNl (s : String) : String :=
  if s.endsWith "\n" then s else s ++ "\n"

open SubVerso.Examples.Messages in
@[code_block]
def leanOutput : CodeBlockExpanderOf LeanOutputConfig
 | config, str => do

    PointOfInterest.save (← getRef) (config.name.getId.toString)
      (kind := Lsp.SymbolKind.file)
      (selectionRange := config.name)
      (detail? := some ("Lean output" ++ (config.severity.map (s!" ({sevStr ·})") |>.getD "")))

    let msgs : List Highlighted.Message ← getOutputs config.name

    let expected :=
      if config.normalizeMetas then
        normalizeMetavars str.getString
      else str.getString

    let mut texts : Array (Highlighted.Span.Kind × String) := #[]

    if config.allowDiff == 0 then
      for msg in msgs do
        let msg ←
          if let some b := config.startAt then
            if let some msg' := msg.startAt b then pure msg'
            else
              texts := texts.push (msg.severity, msg.toString (expandTraces := config.expandTraces))
              continue
          else pure msg

        let msg ←
          if let some e := config.stopAt then
            if let some msg' := msg.stopAt e then pure msg'
            else
              texts := texts.push (msg.severity, msg.toString (expandTraces := config.expandTraces))
              continue
          else pure msg

        let txt := msg.toString (expandTraces := config.expandTraces)
        texts := texts.push (msg.severity, txt)
        let actual :=
          if config.normalizeMetas then
            normalizeMetavars txt
          else txt
        if mostlyEqual config.whitespace expected actual then
          if let some s := config.severity then
            if s != msg.severity.toSeverity then
              throwErrorAt str s!"Expected severity {sevStr s}, but got {sevStr msg.severity.toSeverity}"
          if config.show then
            let content ← `(Block.other {Block.leanOutput with data := ToJson.toJson ($(quote msg), $(quote config.summarize), ($(quote config.expandTraces) : List Name))} #[Block.code $(quote str.getString)])
            return content
          else return (← ``(Block.concat #[]))
    else
      let mut best : Option (Nat × String × Highlighted.Message) := none
      for msg in msgs do
        let txt := msg.toString
        let actual :=
          if config.normalizeMetas then
            normalizeMetavars txt
          else txt
        let (d, d') := diffSize config.whitespace expected actual
        if d ≤ config.allowDiff then
          if let some (n, _, _) := best then
            if d < n then best := (d, d', msg)
          else best := (d, d', msg)
      if let some (d, d', msg) := best then
        if let some s := config.severity then
          let sev := msg.severity.toSeverity
          if s != sev then
            throwErrorAt str s!"Expected severity {sevStr s}, but got {sevStr sev}"

        Log.logSilentInfo m!"Diff is {d} lines:\n{d'}"
        if config.show then
          let content ← `(Block.other {Block.leanOutput with data := ToJson.toJson ($(quote msg), $(quote config.summarize), ($(quote config.expandTraces) : List Name))} #[Block.code $(quote str.getString)])
          return content
        else return (← ``(Block.concat #[]))

    let suggs : Array (Nat × Meta.Hint.Suggestion) := texts.map fun (sev, msg) =>
      ((diffSize config.whitespace msg str.getString).1, {
        suggestion := withNl msg,
        preInfo? := some s!"{sevStr sev.toSeverity}: "
      })
    let suggs : Array Meta.Hint.Suggestion := suggs.qsort (fun x y => x.1 < y.1) |>.map (·.2)

    let hintMsg := if suggs.size > 1 then m!"Replace with one of the actual messages:" else m!"Replace with the actual message:"
    let hint ← hintAt str hintMsg suggs

    throwErrorAt str (m!"Didn't match - got: {indentD (toMessageData <| texts.map (Std.Format.text ·.2))}\nbut expected:{indentD (toMessageData str.getString)}" ++ hint)
where
  sevStr : MessageSeverity → String
    | .error => "error"
    | .information => "information"
    | .warning => "warning"

  mostlyEqual (ws : WhitespaceMode) (s1 s2 : String) : Bool :=
    messagesMatch (ws.apply s1.trim) (ws.apply s2.trim)

  diffSize (ws : WhitespaceMode) (s1 s2 : String) : (Nat × String) :=
    let s1 := ws.apply s1.trim |>.splitOn "\n" |>.toArray
    let s2 := ws.apply s2.trim |>.splitOn "\n" |>.toArray
    let d := Diff.diff s1 s2
    let insDel := d.filter fun
      | (.insert, _) => true
      | (.delete, _) => true
      | _ => false
    (insDel.size, Diff.linesToString d)


inline_extension Inline.name via withHighlighting where
  traverse _ _ _ := do
    pure none
  toTeX := some <| fun go _ _ content => content.mapM go
  toHtml :=
    open Verso.Output.Html in
    some <| fun _ _ data _ => do
      match FromJson.fromJson? data with
      | .error err =>
        HtmlT.logError <| "Couldn't deserialize Lean code while rendering HTML: " ++ err
        pure .empty
      | .ok (hl : Highlighted) =>
        hl.inlineHtml (g := Manual) "examples"

structure NameConfig where
  full : Option Name

section
variable [Monad m] [MonadError m] [MonadLiftT CoreM m] [MonadLiftT TermElabM m]

def NameConfig.parse : ArgParse m NameConfig :=
  NameConfig.mk <$> ((fun _ => none) <$> .done <|> .positional `name ref)
where
  ref : ValDesc m (Option Name) := {
    description := "reference name"
    signature := .Ident
    get := fun
      | .name x =>
        try
          let resolved ← liftM (runWithOpenDecls (runWithVariables fun _ => realizeGlobalConstNoOverloadWithInfo x))
          return some resolved
        catch
          | .error ref e => throwErrorAt ref e
          | _ => return none
      | other => throwError "Expected reference name, got {repr other}"
  }

instance : FromArgs NameConfig m := ⟨NameConfig.parse⟩
end

def constTok [Monad m] [MonadEnv m] [MonadLiftT MetaM m] [MonadLiftT IO m]
    (name : Name) (str : String) :
    m Highlighted := do
  let docs ← findDocString? (← getEnv) name
  let sig := toString (← (PrettyPrinter.ppSignature name)).1
  pure <| .token ⟨.const name sig docs false, str⟩

@[role]
def name : RoleExpanderOf NameConfig
  | cfg, #[arg] => do
    let `(inline|code( $name:str )) := arg
      | throwErrorAt arg "Expected code literal with the example name"
    let exampleName := name.getString.toName
    let identStx := mkIdentFrom arg (cfg.full.getD exampleName) (canonical := true)

    try
      let resolvedName ←
        runWithOpenDecls <| runWithVariables fun _ =>
          withInfoTreeContext (mkInfoTree := pure ∘ InfoTree.node (.ofCommandInfo {elaborator := `Manual.Meta.name, stx := identStx})) do
            realizeGlobalConstNoOverloadWithInfo identStx

      let hl : Highlighted ← constTok resolvedName name.getString

      `(Inline.other {Inline.name with data := ToJson.toJson $(quote hl)} #[Inline.code $(quote name.getString)])
    catch e =>
      logErrorAt identStx e.toMessageData
      ``(Inline.code $(quote name.getString))
  | _, more =>
    if h : more.size > 0 then
      throwErrorAt more[0] "Unexpected contents"
    else
      throwError "Unexpected arguments"

-- Placeholder for module names (eventually hyperlinking these will be important, so better to tag them now)

@[role]
def module : RoleExpanderOf Unit
  | (), #[arg] => do
    let `(inline|code( $name:str )) := arg
      | throwErrorAt arg "Expected code literal with the module's name"
    let exampleName := name.getString.toName
    let identStx := mkIdentFrom arg exampleName (canonical := true)
    ``(Inline.code $(quote name.getString))
  | _, more =>
    if h : more.size > 0 then
      throwErrorAt more[0] "Expected code literal with the module's name"
    else
      throwError "Expected code literal with the module's name"
