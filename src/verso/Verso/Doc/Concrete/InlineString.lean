/-
Copyright (c) 2023-2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import Verso.Parser

import Verso.Doc
import Verso.Doc.Elab
import Verso.Doc.Elab.Incremental
import Verso.Doc.Elab.Monad
import Verso.Doc.Lsp

import Verso.SyntaxUtils

namespace Verso.Doc.Concrete

open Lean Parser

open Verso Parser SyntaxUtils Doc Elab

open Lean Elab Term in
def stringToInlines [Monad m] [MonadError m] [MonadEnv m] [MonadQuotation m] (s : StrLit) : m (Array Syntax) :=
  withRef s do
    return (← textLine.parseString s.getString).getArgs

syntax:max (name := inlinesLit) "inlines!" noWs str : term

open Lean Elab Term in
elab_rules : term
  | `(inlines!%$tk$s) => do
    let inls ← stringToInlines s
    let g ← Meta.mkFreshExprMVar (some (.const ``Verso.Doc.Genre []))
    let (tms, _) ← DocElabM.run tk g { exportingTable := .none } (.init (← `(foo))) <| inls.mapM (elabInline ⟨·⟩)
    elabTerm (← `(term|Inline.concat #[ $[$tms],* ] )) none


set_option pp.rawOnError true

/--
info: Inline.concat #[Inline.text "Hello, ", Inline.emph #[Inline.bold #[Inline.text "emph"]]] : Inline Genre.none
-/
#guard_msgs in
#check (inlines!"Hello, _*emph*_" : Inline .none)
