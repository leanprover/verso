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
    let ctx := {
      (← DocElabContext.fromGenreTerm gTerm (← currentDocName)) with
      refsAllowed := .onlyIfDefined, docReconstructionPlaceholder := none
    }
    let (tms, _) ← DocElabM.run ctx
      { highlightDeduplicationTable := .none }
      (.init tk tk) <| inls.mapM (elabInline ⟨·⟩)
    elabTerm (← ``(Inline.concat #[ $[$tms],* ] )) ty
  | `(blocks!"") => do
    elabTerm (← ``(Lean.Doc.Block.empty)) ty
  | `(blocks!%$tk$s) => do
    let inls ← stringToBlocks s
    let gTerm ← `(term|_%$tk)
    let ctx := {
      (← DocElabContext.fromGenreTerm gTerm (← currentDocName)) with
      refsAllowed := .onlyIfDefined, docReconstructionPlaceholder := none
    }
    let (tms, _) ← DocElabM.run ctx
      { highlightDeduplicationTable := .none }
      (.init tk tk) <| inls.mapM (elabBlock ⟨·⟩)
    elabTerm (← ``(Block.concat #[ $[$tms],* ] )) ty
