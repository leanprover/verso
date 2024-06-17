/-
Copyright (c) 2023-2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import SubVerso.Highlighting
import SubVerso.Examples

import Verso.Genre.Blog.Basic
import Verso.Genre.Blog.Generate
import Verso.Genre.Blog.Site
import Verso.Genre.Blog.Site.Syntax
import Verso.Genre.Blog.Template
import Verso.Genre.Blog.Theme
import Verso.Doc.ArgParse
import Verso.Doc.Lsp
import Verso.Doc.Suggestion
import Verso.Hover
open Verso.Output Html
open Lean (RBMap)

namespace Verso.Genre.Blog

open Lean Elab
open Verso ArgParse Doc Elab

open SubVerso.Examples (loadExamples Example)


def classArgs : ArgParse DocElabM String := .named `«class» .string false

@[role_expander htmlSpan]
def htmlSpan : RoleExpander
  | args, stxs => do
    let classes ← classArgs.run args
    let contents ← stxs.mapM elabInline
    let val ← ``(Inline.other (Blog.InlineExt.htmlSpan $(quote classes)) #[$contents,*])
    pure #[val]

@[directive_expander htmlDiv]
def htmlDiv : DirectiveExpander
  | args, stxs => do
    let classes ← classArgs.run args
    let contents ← stxs.mapM elabBlock
    let val ← ``(Block.other (Blog.BlockExt.htmlDiv $(quote classes)) #[ $contents,* ])
    pure #[val]

private partial def attrs : ArgParse DocElabM (Array (String × String)) := List.toArray <$> remaining attr
where
  remaining {m} {α} (p : ArgParse m α) : ArgParse m (List α) :=
    (.done *> pure []) <|> ((· :: ·) <$> p <*> remaining p)
  attr : ArgParse DocElabM (String × String) :=
    (fun (k, v) => (k.getId.toString (escape := false), v)) <$> .anyNamed "attribute" .string

@[directive_expander html]
def html : DirectiveExpander
  | args, stxs => do
    let (name, attrs) ← ArgParse.run ((·, ·) <$> .positional `name .name <*> attrs) args
    let tag := name.toString (escape := false)
    let contents ← stxs.mapM elabBlock
    let val ← ``(Block.other (Blog.BlockExt.htmlWrapper $(quote tag) $(quote attrs)) #[ $contents,* ])
    pure #[val]

@[directive_expander blob]
def blob : DirectiveExpander
  | #[.anon (.name blobName)], stxs => do
    if h : stxs.size > 0 then logErrorAt stxs[0] "Expected no contents"
    let actualName ← realizeGlobalConstNoOverloadWithInfo blobName
    let val ← ``(Block.other (Blog.BlockExt.blob ($(mkIdentFrom blobName actualName) : Html)) #[])
    pure #[val]
  | _, _ => throwUnsupportedSyntax

@[role_expander blob]
def inlineBlob : RoleExpander
  | #[.anon (.name blobName)], stxs => do
    if h : stxs.size > 0 then logErrorAt stxs[0] "Expected no contents"
    let actualName ← realizeGlobalConstNoOverloadWithInfo blobName
    let val ← ``(Inline.other (Blog.InlineExt.blob ($(mkIdentFrom blobName actualName) : Html)) #[])
    pure #[val]
  | _, _ => throwUnsupportedSyntax

@[role_expander label]
def label : RoleExpander
  | #[.anon (.name l)], stxs => do
    let args ← stxs.mapM elabInline
    let val ← ``(Inline.other (Blog.InlineExt.label $(quote l.getId)) #[ $[ $args ],* ])
    pure #[val]
  | _, _ => throwUnsupportedSyntax

@[role_expander ref]
def ref : RoleExpander
  | #[.anon (.name l)], stxs => do
    let args ← stxs.mapM elabInline
    let val ← ``(Inline.other (Blog.InlineExt.ref $(quote l.getId)) #[ $[ $args ],* ])
    pure #[val]
  | _, _ => throwUnsupportedSyntax


@[role_expander page_link]
def page_link : RoleExpander
  | #[.anon (.name page)], stxs => do
    let args ← stxs.mapM elabInline
    let pageName := mkIdentFrom page <| docName page.getId
    let val ← ``(Inline.other (Blog.InlineExt.pageref $(quote pageName.getId)) #[ $[ $args ],* ])
    pure #[val]
  | _, _ => throwUnsupportedSyntax


-- The assumption here is that suffixes are _mostly_ unique, so the arrays will likely be very
-- small.
structure NameSuffixMap (α : Type) : Type where
  contents : NameMap (Array (Name × α)) := {}
deriving Inhabited

def NameSuffixMap.empty : NameSuffixMap α := {}

def NameSuffixMap.insert (map : NameSuffixMap α) (key : Name) (val : α) : NameSuffixMap α := Id.run do
  let some last := key.components.getLast?
    | map
  let mut arr := map.contents.find? last |>.getD #[]
  for h : i in [0:arr.size] do
    have : i < arr.size := by cases h; simp [*]
    if arr[i].fst == key then
      return {map with contents := map.contents.insert last (arr.set ⟨i, by assumption⟩ (key, val))}
  return {map with contents := map.contents.insert last (arr.push (key, val))}

def NameSuffixMap.toArray (map : NameSuffixMap α) : Array (Name × α) := Id.run do
  let mut arr := #[]
  for (_, arr') in map.contents.toList do
    arr := arr ++ arr'
  arr.qsort (fun x y => x.fst.toString < y.fst.toString)

def NameSuffixMap.toList (map : NameSuffixMap α) : List (Name × α) := map.toArray.toList

def NameSuffixMap.get (map : NameSuffixMap α) (key : Name) : Array (Name × α) := Id.run do
  let ks := key.componentsRev
  let some k' := ks.head?
    | #[]
  let some candidates := map.contents.find? k'
    | #[]
  let mut result := none
  for (n, c) in candidates do
    match matchLength ks n.componentsRev, result with
    | none, _ => continue
    | some l, none => result := some (l, #[(n, c)])
    | some l, some (l', found) =>
      if l > l' then result := some (l, #[(n, c)])
      else if l == l' then result := some (l', found.push (n, c))
      else continue
  let res := result.map Prod.snd |>.getD #[]
  res.qsort (fun x y => x.fst.toString < y.fst.toString)
where
  matchLength : List Name → List Name → Option Nat
    | [], _ => some 0
    | _ :: _, [] => none
    | x::xs, y::ys =>
      if x == y then
        matchLength xs ys |>.map (· + 1)
      else none

/-- info: #[(`a.b.c, 1), (`a.c, 4), (`b.c, 6), (`c, 3)] -/
#guard_msgs in
#eval NameSuffixMap.empty |>.insert `a.b.c 1 |>.insert `b.c 2 |>.insert `c 3 |>.insert `a.c 4 |>.insert `a.b 5 |>.insert `b.c 6 |>.get `c

inductive LeanExampleData where
  | inline (commandState : Command.State) (parserState : Parser.ModuleParserState)
  | subproject (loaded : NameSuffixMap Example)
deriving Inhabited

structure ExampleContext where
  contexts : NameMap LeanExampleData := {}
deriving Inhabited

initialize exampleContextExt : EnvExtension ExampleContext ← registerEnvExtension (pure {})

structure ExampleMessages where
  messages : NameSuffixMap (MessageLog ⊕ List (MessageSeverity × String)) := {}
deriving Inhabited

initialize messageContextExt : EnvExtension ExampleMessages ← registerEnvExtension (pure {})

-- FIXME this is a horrid kludge - find a way to systematically rewrite srclocs?
def parserInputString [Monad m] [MonadFileMap m] (str : TSyntax `str) : m String := do
  let preString := (← getFileMap).source.extract 0 (str.raw.getPos?.getD 0)
  let mut code := ""
  let mut iter := preString.iter
  while !iter.atEnd do
    if iter.curr == '\n' then code := code.push '\n'
    else
      for _ in [0:iter.curr.utf8Size] do
        code := code.push ' '
    iter := iter.next
  code := code ++ str.getString
  return code

initialize registerTraceClass `Elab.Verso.block.lean


open System in
@[block_role_expander leanExampleProject]
def leanExampleProject : BlockRoleExpander
  | args, #[] => withTraceNode `Elab.Verso.block.lean (fun _ => pure m!"Loading example project") <| do
    let (name, projectDir) ← ArgParse.run ((·, ·) <$> .positional `name .name <*> .positional `projectDir .string) args
    if exampleContextExt.getState (← getEnv) |>.contexts |>.contains name then
      throwError "Example context '{name}' already defined in this module"
    let path : FilePath := ⟨projectDir⟩
    if path.isAbsolute then
      throwError "Expected a relative path, got {path}"
    let loadedExamples ← loadExamples path
    let mut savedExamples := {}
    for (mod, modExamples) in loadedExamples.toList do
      for (exName, ex) in modExamples.toList do
        savedExamples := savedExamples.insert (mod ++ exName) ex
    modifyEnv fun env => exampleContextExt.modifyState env fun s => {s with
      contexts := s.contexts.insert name (.subproject savedExamples)
    }
    for (name, ex) in savedExamples.toArray do
      modifyEnv fun env => messageContextExt.modifyState env fun s => {s with messages := s.messages.insert name (.inr ex.messages) }
    Verso.Hover.addCustomHover (← getRef) <| "Contains:\n" ++ String.join (savedExamples.toList.map (s!" * `{toString ·.fst}`\n"))
    pure #[]
  | _, more =>
    if h : more.size > 0 then
      throwErrorAt more[0] "Unexpected contents"
    else
      throwError "Unexpected contents"
where
  getModExamples (mod : Name) (json : Json) : DocElabM (NameMap Example) := do
    let .ok exs := json.getObj?
      | throwError "Not an object: '{json}'"
    let mut found := {}
    for ⟨name, exJson⟩ in exs.toArray do
      match FromJson.fromJson? exJson with
      | .error err =>
        throwError "Error deserializing example '{name}' in '{mod}': {err}\nfrom:\n{json}"
      | .ok ex => found := found.insert (mod ++ name.toName) ex
    pure found

private def getSubproject (project : Ident) : TermElabM (NameSuffixMap Example) := do
  let some ctxt := exampleContextExt.getState (← getEnv) |>.contexts |>.find? project.getId
    | throwErrorAt project "Subproject '{project}' not loaded"
  let .subproject projectExamples := ctxt
    | throwErrorAt project "'{project}' is not loaded as a subproject"
  Verso.Hover.addCustomHover project <| "Contains:\n" ++ String.join (projectExamples.toList.map (s!" * `{toString ·.fst}`\n"))
  pure projectExamples

def NameSuffixMap.getOrSuggest [Monad m] [MonadInfoTree m] [MonadError m]
    (map : NameSuffixMap α) (key : Ident) : m (Name × α) := do
  match map.get key.getId with
  | #[(n', v)] =>
    if n' ≠ key.getId then
      Suggestion.saveSuggestion key n'.toString n'.toString
    pure (n', v)
  | #[] =>
    for (n, _) in map.toArray do
      if FuzzyMatching.fuzzyMatch key.getId.toString n.toString then
        Suggestion.saveSuggestion key n.toString n.toString
    throwErrorAt key "'{key}' not found - options are {map.toList.map (·.fst)}"
  | more =>
    for (n, _) in more do
      Suggestion.saveSuggestion key n.toString n.toString
    throwErrorAt key "'{key}' is ambiguous - options are {more.toList.map (·.fst)}"

@[block_role_expander leanCommand]
def leanCommand : BlockRoleExpander
  | args, #[] => withTraceNode `Elab.Verso.block.lean (fun _ => pure m!"leanCommand") <| do
    let (project, exampleName) ← ArgParse.run ((·, ·) <$> .positional `project .ident <*> .positional `exampleName .ident) args
    let projectExamples ← getSubproject project
    let (_, {highlighted := hls, original := str, ..}) ← projectExamples.getOrSuggest exampleName
    Verso.Hover.addCustomHover exampleName s!"```lean\n{str}\n```"
    pure #[← ``(Block.other (Blog.BlockExt.highlightedCode $(quote project.getId) (SubVerso.Highlighting.Highlighted.seq $(quote hls))) #[Block.code $(quote str)])]
  | _, more =>
    if h : more.size > 0 then
      throwErrorAt more[0] "Unexpected contents"
    else
      throwError "Unexpected contents"

@[role_expander leanKw]
def leanKw : RoleExpander
  | args, #[arg] => do
    ArgParse.run .done args
    let `(inline|code{ $kw:str }) := arg
      | throwErrorAt arg "Expected code literal with the keyword"
    let hl : SubVerso.Highlighting.Highlighted := .token ⟨.keyword none none none, kw.getString⟩
    pure #[← ``(Inline.other (Blog.InlineExt.customHighlight $(quote hl)) #[Inline.code $(quote kw.getString)])]
  | _, more =>
    if h : more.size > 0 then
      throwErrorAt more[0] "Unexpected contents"
    else
      throwError "Unexpected arguments"

@[role_expander leanTerm]
def leanTerm : RoleExpander
  | args, #[arg] => withTraceNode `Elab.Verso.block.lean (fun _ => pure m!"leanTerm") <| do
    let project ← ArgParse.run (.positional `project .ident) args
    let `(inline|code{ $name:str }) := arg
      | throwErrorAt arg "Expected code literal with the example name"
    let exampleName := name.getString.toName
    let projectExamples ← getSubproject project
    let (_, {highlighted := hls, original := str, ..}) ← projectExamples.getOrSuggest <| mkIdentFrom name exampleName
    Verso.Hover.addCustomHover arg s!"```lean\n{str}\n```"
    pure #[← ``(Inline.other (Blog.InlineExt.highlightedCode $(quote project.getId) (SubVerso.Highlighting.Highlighted.seq $(quote hls))) #[Inline.code $(quote str)])]
  | _, more =>
    if h : more.size > 0 then
      throwErrorAt more[0] "Unexpected contents"
    else
      throwError "Unexpected arguments"


structure LeanBlockConfig where
  exampleContext : Ident
  «show» : Option Bool := none
  keep : Option Bool := none
  name : Option Name := none
  error : Option Bool := none

def LeanBlockConfig.parse [Monad m] [MonadInfoTree m] [MonadLiftT CoreM m] [MonadEnv m] [MonadError m] : ArgParse m LeanBlockConfig :=
  LeanBlockConfig.mk <$> .positional `exampleContext .ident <*> .named `show .bool true <*> .named `keep .bool true <*> .named `name .name true <*> .named `error .bool true

@[code_block_expander leanInit]
def leanInit : CodeBlockExpander
  | args , str => withTraceNode `Elab.Verso.block.lean (fun _ => pure m!"leanInit") <| do
    let config ← LeanBlockConfig.parse.run args
    let context := Parser.mkInputContext (← parserInputString str) (← getFileName)
    let (header, state, msgs) ← Parser.parseHeader context
    for imp in header[1].getArgs do
      logErrorAt imp "Imports not yet supported here"
    let opts := Options.empty -- .setBool `trace.Elab.info true
    if header[0].isNone then -- if the "prelude" option was not set, use the current env
      let commandState := configureCommandState (←getEnv) {}
      modifyEnv <| fun env => exampleContextExt.modifyState env fun s => {s with contexts := s.contexts.insert config.exampleContext.getId (.inline commandState  state)}
    else
      if header[1].getArgs.isEmpty then
        let (env, msgs) ← processHeader header opts msgs context 0
        if msgs.hasErrors then
          for msg in msgs.toList do
            logMessage msg
          liftM (m := IO) (throw <| IO.userError "Errors during import; aborting")
        let commandState := configureCommandState env {}
        modifyEnv <| fun env => exampleContextExt.modifyState env fun s => {s with contexts := s.contexts.insert config.exampleContext.getId (.inline commandState state)}
    if config.show.getD false then
      pure #[← ``(Block.code $(quote str.getString))] -- TODO highlighting hack
    else pure #[]
where
  configureCommandState (env : Environment) (msg : MessageLog) : Command.State :=
    { Command.mkState env msg with infoState := { enabled := true } }

open SubVerso.Highlighting Highlighted in
@[code_block_expander lean]
def lean : CodeBlockExpander
  | args, str => withTraceNode `Elab.Verso.block.lean (fun _ => pure m!"lean block") <| do
    let config ← LeanBlockConfig.parse.run args
    let x := config.exampleContext
    let (commandState, state) ← match exampleContextExt.getState (← getEnv) |>.contexts.find? x.getId with
      | some (.inline commandState state) => pure (commandState, state)
      | some (.subproject ..) => throwErrorAt x "Expected an example context for inline Lean, but found a subproject"
      | none => throwErrorAt x "Can't find example context"
    let context := Parser.mkInputContext (← parserInputString str) (← getFileName)
    -- Process with empty messages to avoid duplicate output
    let s ←
      withTraceNode `Elab.Verso.block.lean (fun _ => pure m!"Elaborating commands") <|
      IO.processCommands context state { commandState with messages.unreported := {} }
    for t in s.commandState.infoState.trees do
      pushInfoTree t

    match config.error with
    | none =>
      for msg in s.commandState.messages.toArray do
        logMessage msg
    | some true =>
      if s.commandState.messages.hasErrors then
        for msg in s.commandState.messages.errorsToWarnings.toArray do
          logMessage msg
      else
        throwErrorAt str "Error expected in code block, but none occurred"
    | some false =>
      for msg in s.commandState.messages.toArray do
        logMessage msg
      if s.commandState.messages.hasErrors then
        throwErrorAt str "No error expected in code block, one occurred"

    if config.keep.getD true && !(config.error.getD false) then
      modifyEnv fun env => exampleContextExt.modifyState env fun st => {st with
        contexts := st.contexts.insert x.getId (.inline {s.commandState with messages := {} } s.parserState)
      }
    if let some infoName := config.name then
      modifyEnv fun env => messageContextExt.modifyState env fun st => {st with
        messages := st.messages.insert infoName (.inl s.commandState.messages)
      }
    withTraceNode `Elab.Verso.block.lean (fun _ => pure m!"Highlighting syntax") do
      let mut hls := Highlighted.empty
      let infoSt ← getInfoState
      let env ← getEnv
      try
        setInfoState s.commandState.infoState
        setEnv s.commandState.env
        let msgs := s.commandState.messages.toArray
        for cmd in s.commands do
          hls := hls ++
            (← withTraceNode `Elab.Verso.block.lean (fun _ => pure m!"Highlighting {cmd}") <|
              highlight cmd msgs s.commandState.infoState.trees)
      finally
        setInfoState infoSt
        setEnv env
      if config.show.getD true then
        pure #[← ``(Block.other (Blog.BlockExt.highlightedCode $(quote x.getId) $(quote hls)) #[Block.code $(quote str.getString)])]
      else
        pure #[]

open Lean.Elab.Tactic.GuardMsgs
export WhitespaceMode (exact lax normalized)

structure LeanOutputConfig where
  name : Ident
  severity : Option MessageSeverity
  summarize : Bool
  whitespace : WhitespaceMode

def LeanOutputConfig.parser [Monad m] [MonadInfoTree m] [MonadLiftT CoreM m] [MonadEnv m] [MonadError m] : ArgParse m LeanOutputConfig :=
  LeanOutputConfig.mk <$>
    .positional `name output <*>
    .named `severity sev true <*>
    ((·.getD false) <$> .named `summarize .bool true) <*>
    ((·.getD .exact) <$> .named `whitespace ws true)
where
  output : ValDesc m Ident := {
    description := "output name",
    get := fun
      | .name x => pure x
      | other => throwError "Expected output name, got {repr other}"
  }
  opt {α} (p : ArgParse m α) : ArgParse m (Option α) := (some <$> p) <|> pure none
  optDef {α} (fallback : α) (p : ArgParse m α) : ArgParse m α := p <|> pure fallback
  sev : ValDesc m MessageSeverity := {
    description := open MessageSeverity in m!"The expected severity: '{``error}', '{``warning}', or '{``information}'",
    get := open MessageSeverity in fun
      | .name b => do
        let b' ← realizeGlobalConstNoOverloadWithInfo b
        if b' == ``MessageSeverity.error then pure MessageSeverity.error
        else if b' == ``MessageSeverity.warning then pure MessageSeverity.warning
        else if b' == ``MessageSeverity.information then pure MessageSeverity.information
        else throwErrorAt b "Expected '{``error}', '{``warning}', or '{``information}'"
      | other => throwError "Expected severity, got {repr other}"
  }
  ws : ValDesc m WhitespaceMode := {
    description := open WhitespaceMode in m!"The expected whitespace mode: '{``exact}', '{``normalized}', or '{``lax}'",
    get := open WhitespaceMode in fun
      | .name b => do
        let b' ← realizeGlobalConstNoOverloadWithInfo b
        if b' == ``WhitespaceMode.exact then pure WhitespaceMode.exact
        else if b' == ``WhitespaceMode.normalized then pure WhitespaceMode.normalized
        else if b' == ``WhitespaceMode.lax then pure WhitespaceMode.lax
        else throwErrorAt b "Expected '{``exact}', '{``normalized}', or '{``lax}'"
      | other => throwError "Expected whitespace mode, got {repr other}"
  }

@[code_block_expander leanOutput]
def leanOutput : Doc.Elab.CodeBlockExpander
  | args, str => withTraceNode `Elab.Verso.block.lean (fun _ => pure m!"leanOutput") <| do
    let config ← LeanOutputConfig.parser.run args

    let (_, savedInfo) ← messageContextExt.getState (← getEnv) |>.messages |>.getOrSuggest config.name
    let messages ← match savedInfo with
      | .inl log =>
        let messages ← liftM <| log.toArray.mapM contents
        for m in log.toArray do
          if mostlyEqual config.whitespace str.getString (← contents m) then
            if let some s := config.severity then
              if s != m.severity then
                throwErrorAt str s!"Expected severity {sevStr s}, but got {sevStr m.severity}"
            let content ← if config.summarize then
                let lines := str.getString.splitOn "\n"
                let pre := lines.take 3
                let post := String.join (lines.drop 3 |>.intersperse "\n")
                let preHtml : Html := pre.map (fun (l : String) => {{<code>{{l}}</code>}})
                ``(Block.other (Blog.BlockExt.htmlDetails $(quote (sevStr m.severity)) $(quote preHtml)) #[Block.code $(quote post)])
              else
                ``(Block.other (Blog.BlockExt.htmlDiv $(quote (sevStr m.severity))) #[Block.code $(quote str.getString)])
            return #[content]
        pure messages
      | .inr msgs =>
        let messages := msgs.toArray.map Prod.snd
        for (sev, txt) in msgs do
          if mostlyEqual config.whitespace str.getString txt then
            if let some s := config.severity then
              if s != sev then
                throwErrorAt str s!"Expected severity {sevStr s}, but got {sevStr sev}"
            let content ← if config.summarize then
                let lines := str.getString.splitOn "\n"
                let pre := lines.take 3
                let post := String.join (lines.drop 3 |>.intersperse "\n")
                let preHtml : Html := pre.map (fun (l : String) => {{<code>{{l}}</code>}})
                ``(Block.other (Blog.BlockExt.htmlDetails $(quote (sevStr sev)) $(quote preHtml)) #[Block.code $(quote post)])
              else
                ``(Block.other (Blog.BlockExt.htmlDiv $(quote (sevStr sev))) #[Block.code $(quote str.getString)])
            return #[content]
        pure messages

    for m in messages do
      Verso.Doc.Suggestion.saveSuggestion str (m.take 30 ++ "…") m
    throwErrorAt str "Didn't match - expected one of: {indentD (toMessageData messages)}\nbut got:{indentD (toMessageData str.getString)}"
where
  withNewline (str : String) := if str == "" || str.back != '\n' then str ++ "\n" else str

  sevStr : MessageSeverity → String
    | .error => "error"
    | .information => "information"
    | .warning => "warning"

  contents (message : Message) : IO String := do
    let head := if message.caption != "" then message.caption ++ ":\n" else ""
    pure <| withNewline <| head ++ (← message.data.toString)

  mostlyEqual (ws : WhitespaceMode) (s1 s2 : String) : Bool :=
    ws.apply s1.trim == ws.apply s2.trim

open Lean Elab Command in
elab "#defineLexerBlock" blockName:ident " ← " lexerName:ident : command => do
  let lexer ← liftTermElabM <| realizeGlobalConstNoOverloadWithInfo lexerName
  elabCommand <| ← `(@[code_block_expander $blockName]
    def $blockName : Doc.Elab.CodeBlockExpander
      | #[], str => do
        let out ← Verso.Genre.Blog.LexedText.highlight $(mkIdentFrom lexerName lexer) str.getString
        return #[← ``(Block.other (Blog.BlockExt.lexedText $$(quote out)) #[])]
      | _, str => throwErrorAt str "Expected no arguments")


private def filterString (p : Char → Bool) (str : String) : String := Id.run <| do
  let mut out := ""
  for c in str.toList do
    if p c then out := out.push c
  pure out

def blogMain (theme : Theme) (site : Site) (relativizeUrls := true) (options : List String) : IO UInt32 := do
  let hasError ← IO.mkRef false
  let logError msg := do hasError.set true; IO.eprintln msg
  let cfg ← opts {logError := logError} options
  let (site, xref) ← site.traverse cfg
  let rw := if relativizeUrls then
      some <| relativize
    else none
  site.generate theme {site := site, ctxt := ⟨[], cfg⟩, xref := xref, dir := cfg.destination, config := cfg, rewriteHtml := rw}
  if (← hasError.get) then
    IO.eprintln "Errors were encountered!"
    return 1
  else
    return 0
where
  opts (cfg : Config)
    | ("--output"::dir::more) => opts {cfg with destination := dir} more
    | ("--drafts"::more) => opts {cfg with showDrafts := true} more
    | (other :: _) => throw (↑ s!"Unknown option {other}")
    | [] => pure cfg
  urlAttr (name : String) : Bool := name ∈ ["href", "src", "data", "poster"]
  rwAttr (attr : String × String) : ReaderT TraverseContext Id (String × String) := do
    if urlAttr attr.fst && "/".isPrefixOf attr.snd then
      let path := (← read).path
      pure { attr with
        snd := String.join (List.replicate path.length "../") ++ attr.snd.drop 1
      }
    else
      pure attr
  rwTag (tag : String) (attrs : Array (String × String)) (content : Html) : ReaderT TraverseContext Id (Option Html) := do
    pure <| some <| .tag tag (← attrs.mapM rwAttr) content
  relativize _err ctxt html :=
    pure <| html.visitM (m := ReaderT TraverseContext Id) (tag := rwTag) |>.run ctxt
