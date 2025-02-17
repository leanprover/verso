/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import Lean.Elab.Command
import Lean.Elab.InfoTree

import Verso.Doc.ArgParse
import VersoManual
import Verso.Code

import SubVerso.Examples.Slice
import SubVerso.Highlighting

open Lean Elab
open Verso ArgParse Doc Elab Genre.Manual Html Code
open SubVerso.Examples.Slice
open SubVerso.Highlighting Highlighted

namespace DemoTextbook.Exts

def Block.lean : Block where
  name := `DemoTextbook.Exts.lean


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


structure LeanBlockConfig where
  «show» : Option Bool := none
  keep : Option Bool := none
  name : Option Name := none
  error : Option Bool := none

def LeanBlockConfig.parse [Monad m] [MonadInfoTree m] [MonadLiftT CoreM m] [MonadEnv m] [MonadError m] : ArgParse m LeanBlockConfig :=
  LeanBlockConfig.mk <$> .named `show .bool true <*> .named `keep .bool true <*> .named `name .name true <*> .named `error .bool true

@[code_block_expander lean]
def lean : CodeBlockExpander
  | args, str => do
    let config ← LeanBlockConfig.parse.run args

    let altStr ← parserInputString str

    let ictx := Parser.mkInputContext altStr (← getFileName)
    let cctx : Command.Context := { fileName := ← getFileName, fileMap := FileMap.ofString altStr, snap? := none, cancelTk? := none}
    let mut cmdState : Command.State := {env := ← getEnv, maxRecDepth := ← MonadRecDepth.getMaxRecDepth, scopes := [{header := ""}, {header := ""}]}
    let mut pstate := {pos := 0, recovering := false}
    let mut exercises := #[]
    let mut solutions := #[]

    repeat
      let scope := cmdState.scopes.head!
      let pmctx := { env := cmdState.env, options := scope.opts, currNamespace := scope.currNamespace, openDecls := scope.openDecls }
      let (cmd, ps', messages) := Parser.parseCommand ictx pmctx pstate cmdState.messages
      pstate := ps'
      cmdState := {cmdState with messages := messages}

      -- dbg_trace "Unsliced is {cmd}"
      let slices : Slices ← DocElabM.withFileMap (FileMap.ofString altStr) (sliceSyntax cmd)
      let sol := slices.sliced.getD "solution" slices.residual
      solutions := solutions.push sol
      let ex := slices.sliced.getD "exercise" slices.residual
      exercises := exercises.push ex

      cmdState ← withInfoTreeContext (mkInfoTree := pure ∘ InfoTree.node (.ofCommandInfo {elaborator := `DemoTextbook.Exts.lean, stx := cmd})) do
        let mut cmdState := cmdState
        -- dbg_trace "Elaborating {ex}"
        match (← liftM <| EIO.toIO' <| (Command.elabCommand ex cctx).run cmdState) with
        | Except.error e => logError e.toMessageData
        | Except.ok ((), s) =>
          cmdState := {s with env := cmdState.env}

        -- dbg_trace "Elaborating {sol}"
        match (← liftM <| EIO.toIO' <| (Command.elabCommand sol cctx).run cmdState) with
        | Except.error e => logError e.toMessageData
        | Except.ok ((), s) =>
          cmdState := s

        pure cmdState

      if Parser.isTerminalCommand cmd then break

    setEnv cmdState.env
    for t in cmdState.infoState.trees do
      -- dbg_trace (← t.format)
      pushInfoTree t

    match config.error with
    | none =>
      for msg in cmdState.messages.toArray do
        logMessage msg
    | some true =>
      if cmdState.messages.hasErrors then
        for msg in cmdState.messages.errorsToWarnings.toArray do
          logMessage msg
      else
        throwErrorAt str "Error expected in code block, but none occurred"
    | some false =>
      for msg in cmdState.messages.toArray do
        logMessage msg
      if cmdState.messages.hasErrors then
        throwErrorAt str "No error expected in code block, one occurred"

    let mut hls := Highlighted.empty
    for cmd in exercises do
      hls := hls ++ (← highlight cmd cmdState.messages.toArray cmdState.infoState.trees)
    if config.show.getD true then
      pure #[← `(Block.other {Block.lean with data := ToJson.toJson $(quote hls)} #[Block.code $(quote str.getString)])]
    else
      pure #[]

@[block_extension lean]
def lean.descr : BlockDescr where
  traverse _ _ _ := do
    pure none
  toTeX :=
    some <| fun _ go _ _ content => do
      pure <| .seq <| ← content.mapM fun b => do
        pure <| .seq #[← go b, .raw "\n"]
  extraCss := [highlightingStyle]
  extraJs := [highlightingJs]
  toHtml :=
    open Verso.Output.Html in
    some <| fun _ _ _ data _ => do
      match FromJson.fromJson? data with
      | .error err =>
        HtmlT.logError <| "Couldn't deserialize Lean code while rendering HTML: " ++ err
        pure .empty
      | .ok (hl : Highlighted) =>
        hl.blockHtml "exercises"
