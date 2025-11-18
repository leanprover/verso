/-
Copyright (c) 2023-2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module
public import Lean.Elab.Term

import Verso.Parser
import Verso.Doc
public import Verso.Doc.Elab
public meta import Verso.Doc.Elab.Monad
import Verso.Doc.Lsp

public meta import Verso.SyntaxUtils

namespace Verso.Doc.Concrete

open Lean Parser

open Verso Parser SyntaxUtils Doc Elab

syntax:max (name := inlinesLit) "inlines!" noWs str : term

open Lean Elab Term in
elab_rules : term
  | `(inlines!%$tk$s) => do
    let inls ← stringToInlines s
    let g ← Meta.mkFreshExprMVar (some (.const ``Verso.Doc.Genre []))
    let (tms, _) ← DocElabM.run
        ⟨tk, g, .onlyIfDefined, .none⟩
        { highlightDeduplicationTable := .none }
        (.init (← `(foo)))
        (inls.mapM (elabInline ⟨·⟩))
    elabTerm (← `(term|Inline.concat #[ $[$tms],* ] )) none


set_option pp.rawOnError true

/--
info: Inline.concat #[Inline.text "Hello, ", Inline.emph #[Inline.bold #[Inline.text "emph"]]] : Inline Genre.none
-/
#guard_msgs in
#check (inlines!"Hello, _*emph*_" : Inline .none)
