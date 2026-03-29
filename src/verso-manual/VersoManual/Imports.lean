/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module
import Verso.Doc.ArgParse
import Verso.Doc.Elab
import SubVerso.Highlighting.Code
import VersoManual.ExternalLean
public import Verso.Doc.Elab.Monad

open scoped Lean.Doc.Syntax

open Verso Doc Elab
open Lean
open Verso.SyntaxUtils
open SubVerso.Highlighting
open ArgParse

namespace Verso.Genre.Manual

public structure ImportsParams where
  «show» : Bool := true

public meta instance : FromArgs ImportsParams m where
  fromArgs := ImportsParams.mk <$> .flag `show true (some "Whether to show the import header")

/--
Parses, but does not validate, a module header.
-/
@[code_block]
public meta def imports : CodeBlockExpanderOf ImportsParams
  | { «show» } , str => do
    let altStr ← parserInputString str
    let p := Parser.whitespace >> Parser.Module.header.fn
    let headerStx ← p.parseString altStr
    let hl ← highlight headerStx #[] {}
    if «show» then
      ``(Block.other (Block.lean $(quote hl) {}) #[Block.code $(quote str.getString)])
    else
      ``(Block.empty)
