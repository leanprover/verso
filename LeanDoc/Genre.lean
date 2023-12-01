import Lean.Data.RBMap

import LeanDoc.Doc
import LeanDoc.Html
import LeanDoc.Doc.Html

import LeanDoc.Genre.Blog
import LeanDoc.Genre.Blog.HighlightCode
import LeanDoc.Genre.Blog.Site.Syntax

open LeanDoc.Doc (Genre Part)
open LeanDoc.Doc.Html

namespace LeanDoc.Genre


namespace Blog

open LeanDoc.Html
open Lean (RBMap)

section

open Lean Elab
open LeanDoc Doc Elab


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

open LeanDoc.Genre.Highlighted in
@[code_block_expander lean]
def lean : CodeBlockExpander
  | _, str => do
    -- FIXME this is a horrid kludge - find a way to systematically rewrite srclocs?
    let preString := (← getFileMap).source.extract 0 (str.raw.getPos?.getD 0)
    let inputString := Id.run do
      let mut code := ""
      let mut iter := preString.iter
      while !iter.atEnd do
        if iter.curr == '\n' then code := code.push '\n'
        else code := code.push ' '
        iter := iter.next
      code := code ++ str.getString
      return code
    let context := Parser.mkInputContext inputString "<example>"
    let (header, state, msgs) ← Parser.parseHeader context
    initializeLeanContext
    let opts := Options.empty -- .setBool `trace.Elab.info true
    let (env, msgs) ← processHeader header opts msgs context 0
    if msgs.hasErrors then
      for msg in msgs.toList do
        logMessage msg
      liftM (m := IO) (throw <| IO.userError "Errors during import; aborting")
    let commandState := configureCommandState env msgs
    let s ← IO.processCommands context state commandState
    if let some expectedEnd := str.raw.getTailPos? then
      -- TODO compare code points instead of UTF8
      if s.parserState.pos < expectedEnd then
        dbg_trace "ended at {(← getFileMap).utf8PosToLspPos s.parserState.pos} {s.commands}"
    for t in s.commandState.infoState.trees do
      pushInfoTree t
    for msg in s.commandState.messages.msgs do
      logMessage msg
    let mut hls := Highlighted.empty
    let infoSt ← getInfoState
    let env ← getEnv
    try
      setInfoState s.commandState.infoState
      setEnv s.commandState.env
      for cmd in s.commands do
        hls := hls ++ (← highlight (← getFileMap) cmd false)
    finally
      setInfoState infoSt
      setEnv env
    pure #[← ``(Block.other (Blog.BlockExt.highlightedCode $(quote hls)) #[Block.code none #[] 0 $(quote str.getString)])]
where
  initializeLeanContext : IO Unit := do
    let leanPath ← Lean.findSysroot
    Lean.initSearchPath leanPath
  configureCommandState (env : Environment) (msg : MessageLog) : Command.State :=
    { Command.mkState env msg with infoState := { enabled := true } }

end

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

end Blog
namespace Manual

end Manual
