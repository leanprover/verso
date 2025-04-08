/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

open Verso.Genre Manual
open Verso.Doc Elab
open Verso.ArgParse
open Lean

namespace DemoTextbook

block_extension Block.savedLean (file : String) (source : String) where
  data := .arr #[.str file, .str source]

  traverse _ _ _ := pure none
  toTeX := none
  toHtml := some fun _ goB _ _ contents =>
    contents.mapM goB

block_extension Block.savedImport (file : String) (source : String) where
  data := .arr #[.str file, .str source]

  traverse _ _ _ := pure none
  toTeX := none
  toHtml := some fun _ _ _ _ _ =>
    pure .empty

/--
Lean code that is saved to the examples file.
-/
@[code_block_expander savedLean]
def savedLean : CodeBlockExpander
  | args, code => do
    let underlying ← InlineLean.lean args code
    return #[← ``(Block.other (Block.savedLean $(quote (← getFileName)) $(quote (code.getString))) #[$underlying,*])]

/--
An import of some other module, to be located in the saved code. Not rendered.
-/
@[code_block_expander savedImport]
def savedImport : CodeBlockExpander
  | args, code => do
    ArgParse.done.run args
    return #[← ``(Block.other (Block.savedImport $(quote (← getFileName)) $(quote (code.getString))) #[])]


/--
Comments to be added as module docstrings to the examples file.
-/
@[code_block_expander savedComment]
def savedComment : CodeBlockExpander
  | args, code => do
    ArgParse.done.run args
    let str := code.getString.trimRight
    let comment := s!"/-!\n{str}\n-/"
    return #[← ``(Block.other (Block.savedLean $(quote (← getFileName)) $(quote comment)) #[])]
