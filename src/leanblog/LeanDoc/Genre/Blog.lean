import LeanDoc.Genre.Blog.Basic
import LeanDoc.Genre.Blog.Generate
import LeanDoc.Genre.Blog.Highlighted
import LeanDoc.Genre.Blog.HighlightCode
import LeanDoc.Genre.Blog.Site
import LeanDoc.Genre.Blog.Site.Syntax
import LeanDoc.Genre.Blog.Template
import LeanDoc.Genre.Blog.Theme
open LeanDoc.Output Html
open Lean (RBMap)

namespace LeanDoc.Genre.Blog

open Lean Elab
open LeanDoc Doc Elab


@[role_expander htmlSpan]
def htmlSpan : RoleExpander
  | #[.named `«class» (.string classes)], stxs => do
    let args ← stxs.mapM elabInline
    let val ← ``(Inline.other (Blog.InlineExt.htmlSpan $(quote classes)) #[ $[ $args ],* ])
    pure #[val]
  | _, _ => throwUnsupportedSyntax

@[directive_expander htmlDiv]
def htmlDiv : DirectiveExpander
  | #[.named `«class» (.string classes)], stxs => do
    let args ← stxs.mapM elabBlock
    let val ← ``(Block.other (Blog.BlockExt.htmlDiv $(quote classes)) #[ $[ $args ],* ])
    pure #[val]
  | _, _ => throwUnsupportedSyntax

@[directive_expander blob]
def blob : DirectiveExpander
  | #[.anonymous (.name blobName)], stxs => do
    if h : stxs.size > 0 then logErrorAt stxs[0] "Expected no contents"
    let actualName ← resolveGlobalConstNoOverloadWithInfo blobName
    let val ← ``(Block.other (Blog.BlockExt.blob ($(mkIdentFrom blobName actualName) : Html)) #[])
    pure #[val]
  | _, _ => throwUnsupportedSyntax

@[role_expander blob]
def inlineBlob : RoleExpander
  | #[.anonymous (.name blobName)], stxs => do
    if h : stxs.size > 0 then logErrorAt stxs[0] "Expected no contents"
    let actualName ← resolveGlobalConstNoOverloadWithInfo blobName
    let val ← ``(Inline.other (Blog.InlineExt.blob ($(mkIdentFrom blobName actualName) : Html)) #[])
    pure #[val]
  | _, _ => throwUnsupportedSyntax

@[role_expander label]
def label : RoleExpander
  | #[.anonymous (.name l)], stxs => do
    let args ← stxs.mapM elabInline
    let val ← ``(Inline.other (Blog.InlineExt.label $(quote l.getId)) #[ $[ $args ],* ])
    pure #[val]
  | _, _ => throwUnsupportedSyntax

@[role_expander ref]
def ref : RoleExpander
  | #[.anonymous (.name l)], stxs => do
    let args ← stxs.mapM elabInline
    let val ← ``(Inline.other (Blog.InlineExt.ref $(quote l.getId)) #[ $[ $args ],* ])
    pure #[val]
  | _, _ => throwUnsupportedSyntax


@[role_expander page_link]
def page_link : RoleExpander
  | #[.anonymous (.name page)], stxs => do
    let args ← stxs.mapM elabInline
    let pageName := mkIdentFrom page <| docName page.getId
    let val ← ``(Inline.other (Blog.InlineExt.pageref $(quote pageName.getId)) #[ $[ $args ],* ])
    pure #[val]
  | _, _ => throwUnsupportedSyntax

structure ExampleContext where
  contexts : NameMap (Command.State × Parser.ModuleParserState) := {}
deriving Inhabited

initialize exampleContextExt : EnvExtension ExampleContext ← registerEnvExtension (pure {})

-- FIXME this is a horrid kludge - find a way to systematically rewrite srclocs?
def parserInputString [Monad m] [MonadFileMap m] (str : TSyntax `str) : m String := do
  let preString := (← getFileMap).source.extract 0 (str.raw.getPos?.getD 0)
  let mut code := ""
  let mut iter := preString.iter
  while !iter.atEnd do
    if iter.curr == '\n' then code := code.push '\n'
    else
      for _ in [0:iter.curr.utf8Size.toNat] do
        code := code.push ' '
    iter := iter.next
  code := code ++ str.getString
  return code

@[code_block_expander leanInit]
def leanInit : CodeBlockExpander
  | #[.anonymous (.name x)], str => do
    let context := Parser.mkInputContext (← parserInputString str) "<example>"
    let (header, state, msgs) ← Parser.parseHeader context
    initializeLeanContext
    let opts := Options.empty -- .setBool `trace.Elab.info true
    let (env, msgs) ← processHeader header opts msgs context 0
    if msgs.hasErrors then
      for msg in msgs.toList do
        logMessage msg
      liftM (m := IO) (throw <| IO.userError "Errors during import; aborting")
    let commandState := configureCommandState env msgs
    modifyEnv <| fun env => exampleContextExt.modifyState env fun s => {s with contexts := s.contexts.insert x.getId (commandState, state)}
    pure #[]
  | otherArgs, str => throwErrorAt str "Unexpected arguments {repr otherArgs}"
where
  initializeLeanContext : IO Unit := do
    let leanPath ← Lean.findSysroot
    Lean.initSearchPath leanPath
  configureCommandState (env : Environment) (msg : MessageLog) : Command.State :=
    { Command.mkState env msg with infoState := { enabled := true } }

open LeanDoc.Genre.Highlighted in
@[code_block_expander lean]
def lean : CodeBlockExpander
  | #[.anonymous (.name x)], str => do
    let some (commandState, state) := exampleContextExt.getState (← getEnv) |>.contexts.find? x.getId
      | throwErrorAt x "Can't find example context"
    let context := Parser.mkInputContext (← parserInputString str) "<example>"
    -- Process with empty messages to avoid duplicate output
    let s ← IO.processCommands context state { commandState with messages.msgs := {} }
    for t in s.commandState.infoState.trees do
      pushInfoTree t
    for msg in s.commandState.messages.msgs do
      logMessage msg
    modifyEnv <| fun env => exampleContextExt.modifyState env fun st => {s with contexts := st.contexts.insert x.getId (s.commandState, s.parserState)}
    let mut hls := Highlighted.empty
    let infoSt ← getInfoState
    let env ← getEnv
    try
      setInfoState s.commandState.infoState
      setEnv s.commandState.env
      for cmd in s.commands do
        hls := hls ++ (← highlight cmd)
    finally
      setInfoState infoSt
      setEnv env
    pure #[← ``(Block.other (Blog.BlockExt.highlightedCode $(quote x.getId) $(quote hls)) #[Block.code none #[] 0 $(quote str.getString)])]
  | otherArgs, str => throwErrorAt str "Unexpected arguments {repr otherArgs}"

private def filterString (p : Char → Bool) (str : String) : String := Id.run <| do
  let mut out := ""
  for c in str.toList do
    if p c then out := out.push c
  pure out

def blogMain (theme : Theme) (site : Site) (options : List String) : IO UInt32 := do
  let hasError ← IO.mkRef false
  let logError msg := do hasError.set true; IO.eprintln msg
  let cfg ← opts {logError := logError} options
  let (site, xref) ← site.traverse cfg
  site.generate theme {site := site, ctxt := ⟨[], cfg⟩, xref := xref, dir := cfg.destination, config := cfg}
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
