/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

module
public import Verso.Doc.ArgParse
public import Verso.Doc.Elab
public import SubVerso.Highlighting.Code
public import VersoManual.ExternalLean
public meta import Verso.Doc.Elab.Monad

public section

open scoped Lean.Doc.Syntax

open Verso Doc Elab
open Lean
open Verso.SyntaxUtils
open SubVerso.Highlighting
open ArgParse

namespace Verso.Genre.Manual

structure ImportsParams where
  «show» : Bool := true

meta instance : FromArgs ImportsParams m where
  fromArgs := ImportsParams.mk <$> .flag `show true (some "Whether to show the import header")

/--
Parses, but does not validate, a module header.
-/
@[code_block]
meta def imports : CodeBlockExpanderOf ImportsParams
  | { «show» } , str => do
    let p := Parser.whitespace >> Parser.Module.header.fn
    let headerStx ← parseStrLitWith p str
    let hl ← highlight headerStx #[] {}
    if «show» then
      ``(Block.other (Block.lean $(quote hl) {}) #[Block.code $(quote str.getString)])
    else
      ``(Block.empty)
