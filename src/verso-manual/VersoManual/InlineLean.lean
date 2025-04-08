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
import VersoManual.WithoutAsync

import VersoManual.Basic
import VersoManual.InlineLean.Block
import VersoManual.InlineLean.IO
import VersoManual.InlineLean.LongLines
import VersoManual.InlineLean.Option
import VersoManual.InlineLean.Outputs
import VersoManual.InlineLean.Scopes
import VersoManual.InlineLean.Signature
import VersoManual.InlineLean.SyntaxError


open Lean Elab
open Verso ArgParse Doc Elab Genre.Manual Html Code Highlighted.WebAssets ExpectString
open SubVerso.Highlighting Highlighted

open Verso.SyntaxUtils (parserInputString runParserCategory' SyntaxError)

open Lean.Elab.Tactic.GuardMsgs

namespace Verso.Genre.Manual.InlineLean

inline_extension Inline.lean (hls : Highlighted) where
  data :=
    let defined := hls.definedNames.toArray
    Json.arr #[ToJson.toJson hls, ToJson.toJson defined]

  traverse id data _ := do
    let .arr #[_, defined] := data
      | logError "Expected two-element JSON for Lean code" *> pure none
    match FromJson.fromJson? defined with
    | .error err =>
      logError <| "Couldn't deserialize Lean code while traversing inline example: " ++ err
      pure none
    | .ok (defs : Array Name) =>
      let path ← (·.path) <$> read
      for n in defs do
        let _ ← externalTag id path n.toString
        modify (·.saveDomainObject exampleDomain n.toString id)
      pure none
  toTeX :=
    some <| fun go _ _ content => do
      pure <| .seq <| ← content.mapM fun b => do
        pure <| .seq #[← go b, .raw "\n"]
  extraCss := [highlightingStyle]
  extraJs := [highlightingJs]
  extraJsFiles := [("popper.js", popper), ("tippy.js", tippy)]
  extraCssFiles := [("tippy-border.css", tippy.border.css)]
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
        hl.inlineHtml "examples"


section Config

variable [Monad m] [MonadInfoTree m] [MonadLiftT CoreM m] [MonadEnv m] [MonadError m]

structure LeanBlockConfig where
  «show» : Option Bool := none
  keep : Option Bool := none
  name : Option Name := none
  error : Option Bool := none
  fresh : Bool := false

def LeanBlockConfig.parse : ArgParse m LeanBlockConfig :=
  LeanBlockConfig.mk <$> .named `show .bool true <*> .named `keep .bool true <*> .named `name .name true <*> .named `error .bool true <*> .namedD `fresh .bool false

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
    get
      | .str s => pure s
      | other => throwError "Expected string, got {repr other}"
  }

end Config


open Verso.Genre.Manual.InlineLean.Scopes (getScopes setScopes runWithOpenDecls runWithVariables)

private def abbrevFirstLine (width : Nat) (str : String) : String :=
  let str := str.trimLeft
  let short := str.take width |>.replace "\n" "⏎"
  if short == str then short else short ++ "…"

def LeanBlockConfig.outlineMeta : LeanBlockConfig → String
  | {«show», error, ..} =>
    match «show», error with
    | some true, true | none, true => " (error)"
    | some false, true => " (hidden, error)"
    | some false, false => " (hidden)"
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

/--
Elaborates the provided Lean command in the context of the current Verso module.
-/
@[code_block_expander lean]
def lean : CodeBlockExpander
  | args, str => withoutAsync <| do
    let config ← LeanBlockConfig.parse.run args

    PointOfInterest.save (← getRef) ((config.name.map toString).getD (abbrevFirstLine 20 str.getString))
      (kind := Lsp.SymbolKind.file)
      (detail? := some ("Lean code" ++ config.outlineMeta))

    let col? := (← getRef).getPos? |>.map (← getFileMap).utf8PosToLspPos |>.map (·.character)

    let origScopes ← if config.fresh then pure [{header := ""}] else getScopes

    -- Turn of async elaboration so that info trees and messages are available when highlighting syntax
    let origScopes := origScopes.modifyHead fun sc => {sc with opts := Elab.async.set sc.opts false}

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

      if let some col := col? then
        hls := hls.deIndent col

      if config.show.getD true then
        let range := Syntax.getRange? str
        let range := range.map (← getFileMap).utf8RangeToLspRange
        pure #[← ``(Block.other (Block.lean $(quote hls) (some $(quote (← getFileName))) $(quote range)) #[Block.code $(quote str.getString)])]
      else
        pure #[]
    finally
      if !config.keep.getD true then
        setEnv origEnv

      if let some name := config.name then
        let nonSilentMsgs := cmdState.messages.toList.filter (!·.isSilent)
        let msgs ← nonSilentMsgs.mapM fun msg => do

          let head := if msg.caption != "" then msg.caption ++ ":\n" else ""
          let txt := withNewline <| head ++ (← msg.data.toString)

          pure (msg.severity, txt)
        saveOutputs name msgs

      reportMessages config.error str cmdState.messages

      if config.show.getD true then
        warnLongLines col? str
where
  withNewline (str : String) := if str == "" || str.back != '\n' then str ++ "\n" else str
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
@[code_block_expander leanTerm]
def leanTerm : CodeBlockExpander
  | args, str => withoutAsync <| do
    let config ← LeanInlineConfig.parse.run args

    let altStr ← parserInputString str

    let col? := (← getRef).getPos? |>.map (← getFileMap).utf8PosToLspPos |>.map (·.character)

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
        let msgs ← newMsgs.toList.mapM fun msg => do

          let head := if msg.caption != "" then msg.caption ++ ":\n" else ""
          let txt := withNewline <| head ++ (← msg.data.toString)

          pure (msg.severity, txt)
        saveOutputs name msgs

      pushInfoTree tree

      match config.error with
      | none =>
        for msg in newMsgs.toArray do
          logMessage msg
      | some true =>
        if newMsgs.hasErrors then
          for msg in newMsgs.errorsToWarnings.toArray do
            logMessage msg
        else
          throwErrorAt str "Error expected in code, but none occurred"
      | some false =>
        for msg in newMsgs.toArray do
          logMessage msg
        if newMsgs.hasErrors then
          throwErrorAt str "No error expected in code, one occurred"

      let hls := (← highlight stx #[] (PersistentArray.empty.push tree))
      let hls :=
        if let some col := col? then
          hls.deIndent col
        else hls

      if config.show.getD true then
        let range := Syntax.getRange? str
        let range := range.map (← getFileMap).utf8RangeToLspRange
        pure #[← ``(Block.other (Block.lean $(quote hls) (some $(quote (← getFileName))) $(quote range)) #[Block.code $(quote str.getString)])]
      else
        pure #[]
where
  withNewline (str : String) := if str == "" || str.back != '\n' then str ++ "\n" else str


  modifyInfoTrees {m} [Monad m] [MonadInfoTree m] (f : PersistentArray InfoTree → PersistentArray InfoTree) : m Unit :=
    modifyInfoState fun s => { s with trees := f s.trees }

  -- TODO - consider how to upstream this
  withInfoTreeContext {m α} [Monad m] [MonadInfoTree m] [MonadFinally m] (x : m α) (mkInfoTree : PersistentArray InfoTree → m InfoTree) : m (α × InfoTree) := do
    let treesSaved ← getResetInfoTrees
    MonadFinally.tryFinally' x fun _ => do
      let st    ← getInfoState
      let tree  ← mkInfoTree st.trees
      modifyInfoTrees fun _ => treesSaved.push tree
      pure tree

/--
Elaborates the provided Lean term in the context of the current Verso module.
-/
@[role_expander lean]
def leanInline : RoleExpander
  -- Async elab is turned off to make sure that info trees and messages are available when highlighting
  | args, inlines => withoutAsync do
    let config ← LeanInlineConfig.parse.run args
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
        let msgs ← newMsgs.toList.mapM fun msg => do

          let head := if msg.caption != "" then msg.caption ++ ":\n" else ""
          let txt := withNewline <| head ++ (← msg.data.toString)

          pure (msg.severity, txt)
        saveOutputs name msgs

      pushInfoTree tree

      if let `(inline|role{%$s $f $_*}%$e[$_*]) ← getRef then
        Hover.addCustomHover (mkNullNode #[s, e]) type
        Hover.addCustomHover f type

      match config.error with
      | none =>
        for msg in newMsgs.toArray do
          logMessage {msg with
            isSilent := msg.isSilent || msg.severity != .error
          }
      | some true =>
        if newMsgs.hasErrors then
          for msg in newMsgs.errorsToWarnings.toArray do
            logMessage {msg with isSilent := true}
        else
          throwErrorAt term "Error expected in code block, but none occurred"
      | some false =>
        for msg in newMsgs.toArray do
          logMessage {msg with isSilent := msg.isSilent || msg.severity != .error}
        if newMsgs.hasErrors then
          throwErrorAt term "No error expected in code block, one occurred"

      reportMessages config.error term newMsgs

      let hls := (← highlight stx #[] (PersistentArray.empty.push tree))


      if config.show.getD true then
        pure #[← ``(Inline.other (Verso.Genre.Manual.InlineLean.Inline.lean $(quote hls)) #[Inline.code $(quote term.getString)])]
      else
        pure #[]
where
  withNewline (str : String) := if str == "" || str.back != '\n' then str ++ "\n" else str


  modifyInfoTrees {m} [Monad m] [MonadInfoTree m] (f : PersistentArray InfoTree → PersistentArray InfoTree) : m Unit :=
    modifyInfoState fun s => { s with trees := f s.trees }

  -- TODO - consider how to upstream this
  withInfoTreeContext {m α} [Monad m] [MonadInfoTree m] [MonadFinally m] (x : m α) (mkInfoTree : PersistentArray InfoTree → m InfoTree) : m (α × InfoTree) := do
    let treesSaved ← getResetInfoTrees
    MonadFinally.tryFinally' x fun _ => do
      let st    ← getInfoState
      let tree  ← mkInfoTree st.trees
      modifyInfoTrees fun _ => treesSaved.push tree
      pure tree


/--
Elaborates the provided term in the current Verso context, then ensures that it's a type class that has an instance.
-/
@[role_expander inst]
def inst : RoleExpander
  | args, inlines => withoutAsync <| do
    let config ← LeanBlockConfig.parse.run args
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
        let msgs ← newMsgs.toList.mapM fun msg => do

          let head := if msg.caption != "" then msg.caption ++ ":\n" else ""
          let txt := withNewline <| head ++ (← msg.data.toString)

          pure (msg.severity, txt)
        saveOutputs name msgs

      pushInfoTree tree

      reportMessages config.error term newMsgs

      let hls := (← highlight stx #[] (PersistentArray.empty.push tree))

      if config.show.getD true then
        pure #[← ``(Inline.other (Verso.Genre.Manual.InlineLean.Inline.lean $(quote hls)) #[Inline.code $(quote term.getString)])]
      else
        pure #[]
where
  withNewline (str : String) := if str == "" || str.back != '\n' then str ++ "\n" else str


  modifyInfoTrees {m} [Monad m] [MonadInfoTree m] (f : PersistentArray InfoTree → PersistentArray InfoTree) : m Unit :=
    modifyInfoState fun s => { s with trees := f s.trees }

  -- TODO - consider how to upstream this
  withInfoTreeContext {m α} [Monad m] [MonadInfoTree m] [MonadFinally m] (x : m α) (mkInfoTree : PersistentArray InfoTree → m InfoTree) : m (α × InfoTree) := do
    let treesSaved ← getResetInfoTrees
    MonadFinally.tryFinally' x fun _ => do
      let st    ← getInfoState
      let tree  ← mkInfoTree st.trees
      modifyInfoTrees fun _ => treesSaved.push tree
      pure tree

/--
Elaborates the contained document in a new section.
-/
@[directive_expander leanSection]
def leanSection : DirectiveExpander
  | args, contents => do
    let name? ← ArgParse.run ((some <$> .positional `name .string) <|> pure none) args
    let arg ← `(argument| «show» := false)
    let code := name?.map (s!"section {·}") |>.getD "section"
    let start ← `(block|```lean $arg | $(quote code) ```)
    let code := name?.map (s!"end {·}") |>.getD "end"
    let «end» ← `(block|```lean $arg | $(quote code) ```)
    return #[← elabBlock start] ++ (← contents.mapM elabBlock) ++ #[← elabBlock «end»]

private def getClass : MessageSeverity → String
  | .error => "error"
  | .information => "information"
  | .warning => "warning"

block_extension Block.leanOutput where
  traverse _ _ _ := do
    pure none
  toTeX :=
    some <| fun _ go _ _ content => do
      pure <| .seq <| ← content.mapM fun b => do
        pure <| .seq #[← go b, .raw "\n"]
  extraCss := [highlightingStyle]
  extraJs := [highlightingJs]
  extraJsFiles := [("popper.js", popper), ("tippy.js", tippy)]
  extraCssFiles := [("tippy-border.css", tippy.border.css)]
  toHtml :=
    open Verso.Output.Html in
    some <| fun _ _ _ data _ => do
      match FromJson.fromJson? data with
      | .error err =>
        HtmlT.logError <| "Couldn't deserialize Lean code while rendering HTML: " ++ err
        pure .empty
      | .ok ((sev, txt, summarize) : MessageSeverity × String × Bool) =>
        let wrap html :=
          if summarize then {{<details><summary>"Expand..."</summary>{{html}}</details>}}
          else html
        pure <| wrap {{<div class={{getClass sev}}><pre>{{txt}}</pre></div>}}


structure LeanOutputConfig where
  name : Ident
  «show» : Bool := true
  severity : Option MessageSeverity
  summarize : Bool
  whitespace : WhitespaceMode
  normalizeMetas : Bool

section
variable [Monad m] [MonadInfoTree m] [MonadLiftT CoreM m] [MonadEnv m] [MonadError m]

def LeanOutputConfig.parser  : ArgParse m LeanOutputConfig :=
  LeanOutputConfig.mk <$>
    .positional `name output <*>
    ((·.getD true) <$> .named `show .bool true) <*>
    .named `severity .messageSeverity true <*>
    ((·.getD false) <$> .named `summarize .bool true) <*>
    ((·.getD .exact) <$> .named `whitespace .whitespaceMode true) <*>
    .namedD `normalizeMetas .bool true
where
  output : ValDesc m Ident := {
    description := "output name",
    get := fun
      | .name x => pure x
      | other => throwError "Expected output name, got {repr other}"
  }
  opt {α} (p : ArgParse m α) : ArgParse m (Option α) := (some <$> p) <|> pure none
  optDef {α} (fallback : α) (p : ArgParse m α) : ArgParse m α := p <|> pure fallback

end


@[code_block_expander leanOutput]
def leanOutput : CodeBlockExpander
 | args, str => do
    let config ← LeanOutputConfig.parser.run args

    let col? := (← getRef).getPos? |>.map (← getFileMap).utf8PosToLspPos |>.map (·.character)

    PointOfInterest.save (← getRef) (config.name.getId.toString)
      (kind := Lsp.SymbolKind.file)
      (selectionRange := config.name)
      (detail? := some ("Lean output" ++ (config.severity.map (s!" ({sevStr ·})") |>.getD "")))

    let msgs : List (MessageSeverity × String) ← getOutputs config.name

    let expected :=
      if config.normalizeMetas then
        normalizeMetavars str.getString
      else str.getString

    for (sev, txt) in msgs do
      let actual :=
        if config.normalizeMetas then
          normalizeMetavars txt
        else txt
      if mostlyEqual config.whitespace expected actual then
        if let some s := config.severity then
          if s != sev then
            throwErrorAt str s!"Expected severity {sevStr s}, but got {sevStr sev}"
        if config.show then
          let content ← `(Block.other {Block.leanOutput with data := ToJson.toJson ($(quote sev), $(quote txt), $(quote config.summarize))} #[Block.code $(quote str.getString)])
          return #[content]
        else return #[]

    for (_, m) in msgs do
      let m := "".pushn ' ' (col?.getD 0) ++ if m.endsWith "\n" then m else m ++ "\n"
      Verso.Doc.Suggestion.saveSuggestion str (abbreviateString m) m
    throwErrorAt str "Didn't match - expected one of: {indentD (toMessageData <| msgs.map (·.2))}\nbut got:{indentD (toMessageData str.getString)}"
where
  sevStr : MessageSeverity → String
    | .error => "error"
    | .information => "information"
    | .warning => "warning"

  mostlyEqual (ws : WhitespaceMode) (s1 s2 : String) : Bool :=
    ws.apply s1.trim == ws.apply s2.trim




inline_extension Inline.name where
  traverse _ _ _ := do
    pure none
  toTeX :=
    some <| fun go _ _ content => do
      pure <| .seq <| ← content.mapM fun b => do
        pure <| .seq #[← go b, .raw "\n"]
  extraCss := [highlightingStyle]
  extraJs := [highlightingJs]
  extraJsFiles := [("popper.js", popper), ("tippy.js", tippy)]
  extraCssFiles := [("tippy-border.css", tippy.border.css)]
  toHtml :=
    open Verso.Output.Html in
    some <| fun _ _ data _ => do
      match FromJson.fromJson? data with
      | .error err =>
        HtmlT.logError <| "Couldn't deserialize Lean code while rendering HTML: " ++ err
        pure .empty
      | .ok (hl : Highlighted) =>
        hl.inlineHtml "examples"

structure NameConfig where
  full : Option Name

def NameConfig.parse [Monad m] [MonadError m] [MonadLiftT CoreM m] [MonadLiftT TermElabM m] : ArgParse m NameConfig :=
  NameConfig.mk <$> ((fun _ => none) <$> .done <|> .positional `name ref)
where
  ref : ValDesc m (Option Name) := {
    description := m!"reference name"
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

def constTok [Monad m] [MonadEnv m] [MonadLiftT MetaM m] [MonadLiftT IO m]
    (name : Name) (str : String) :
    m Highlighted := do
  let docs ← findDocString? (← getEnv) name
  let sig := toString (← (PrettyPrinter.ppSignature name)).1
  pure <| .token ⟨.const name sig docs false, str⟩

@[role_expander name]
def name : RoleExpander
  | args, #[arg] => do
    let cfg ← NameConfig.parse.run args
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

      pure #[← `(Inline.other {Inline.name with data := ToJson.toJson $(quote hl)} #[Inline.code $(quote name.getString)])]
    catch e =>
      logErrorAt identStx e.toMessageData
      pure #[← `(Inline.code $(quote name.getString))]
  | _, more =>
    if h : more.size > 0 then
      throwErrorAt more[0] "Unexpected contents"
    else
      throwError "Unexpected arguments"

-- Placeholder for module names (eventually hyperlinking these will be important, so better to tag them now)

@[role_expander module]
def module : RoleExpander
  | args, #[arg] => do
    let cfg ← ArgParse.done.run args
    let `(inline|code( $name:str )) := arg
      | throwErrorAt arg "Expected code literal with the module's name"
    let exampleName := name.getString.toName
    let identStx := mkIdentFrom arg exampleName (canonical := true)
    pure #[← ``(Doc.Inline.code $(quote name.getString))]
  | _, more =>
    if h : more.size > 0 then
      throwErrorAt more[0] "Expected code literal with the module's name"
    else
      throwError "Expected code literal with the module's name"
