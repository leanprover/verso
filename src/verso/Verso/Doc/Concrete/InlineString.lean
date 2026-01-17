/-
Copyright (c) 2023-2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module
public import Lean.Elab.Term

public meta import Verso.Parser
import Verso.Doc
public import Verso.Doc.Elab
public meta import Verso.Doc.Elab.Monad
import Verso.Doc.Lsp

import Verso.SyntaxUtils

namespace Verso.Doc.Concrete

open Lean Parser

open Verso Parser SyntaxUtils Doc Elab

syntax:max (name := inlinesLit) "inlines!" noWs str : term
syntax:max (name := blocksLit) "blocks!" noWs str : term

open Lean Elab Term in
elab_rules : term <= ty
  | `(inlines!"") => do
    elabTerm (← ``(Lean.Doc.Inline.empty)) ty
  | `(inlines!%$tk$s) => do
    let inls ← stringToInlines s
    let gTerm ← `(term|_%$tk)
    let g ← Meta.mkFreshExprMVar (some (.const ``Verso.Doc.Genre []))
    let (tms, _) ← DocElabM.run
      ⟨gTerm, g, .onlyIfDefined, .none⟩
      { highlightDeduplicationTable := .none }
      (.init (← `(foo))) <| inls.mapM (elabInline ⟨·⟩)
    elabTerm (← ``(Inline.concat #[ $[$tms],* ] )) ty
  | `(blocks!"") => do
    elabTerm (← ``(Lean.Doc.Block.empty)) ty
  | `(blocks!%$tk$s) => do
    let inls ← stringToBlocks s
    let g ← Meta.mkFreshExprMVar (some (.const ``Verso.Doc.Genre []))
    let gTerm ← `(term|_%$tk)
    let (tms, _) ← DocElabM.run
      ⟨gTerm, g, .onlyIfDefined, .none⟩
      { highlightDeduplicationTable := .none }
      (.init (← `(foo))) <| inls.mapM (elabBlock ⟨·⟩)
    elabTerm (← ``(Block.concat #[ $[$tms],* ] )) ty


set_option pp.rawOnError true

/--
info: Inline.concat #[Inline.text "Hello, ", Inline.emph #[Inline.bold #[Inline.text "emph"]]] : Inline Genre.none
-/
#guard_msgs in
#check (inlines!"Hello, _*emph*_" : Inline .none)

/--
info: Block.concat #[Block.para #[Inline.text "Hello, ", Inline.emph #[Inline.bold #[Inline.text "emph"]]]] : Block Genre.none
-/
#guard_msgs in
#check (blocks!"Hello, _*emph*_" : Block .none)
