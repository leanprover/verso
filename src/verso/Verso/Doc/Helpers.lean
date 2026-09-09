/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module
public import Lean.Elab.DocString.Builtin.Parsing
public import Lean.DocString.View
public import Lean.Exception
public import Lean.Log

set_option doc.verso true

open Lean
open Lean.Doc

namespace Verso.Doc

/--
If the non-whitespace elements of {name}`inlines` are a single code inline, its contents are
returned. Otherwise, an error is logged and {name}`none` is returned.
-/
public def onlyCode? [Monad m] [MonadError m] [MonadLog m] [AddMessageContext m] [MonadOptions m]
    (inlines : Array VersoInline) : m (Option VersoCode) := do
  try
    return some (← Lean.Doc.onlyCode inlines)
  catch
    | .error ref msg =>
      logErrorAt ref msg
      return none
    | e => throw e

/--
If the non-whitespace elements of {name}`inlines` are a single code inline, the Lean name it
contains is returned as an identifier at its source location. Otherwise, an error is thrown.
-/
public def onlyName [Monad m] [MonadError m]
    (inlines : Array VersoInline) : m Ident := do
  let code ← Lean.Doc.onlyCode inlines
  let str := code.getVersoCode
  let name := if str.contains '.' then str.toName else Name.str .anonymous str
  return mkIdentFrom code name

/-- Reads the single code inline that the arguments to a role consist of. -/
@[deprecated Lean.Doc.onlyCode (since := "2026-09-17")]
public def oneCodeStr [Monad m] [MonadError m] (inlines : Array VersoInline) : m VersoCode :=
  Lean.Doc.onlyCode inlines

/-- Reads the single code inline that the arguments to a role consist of, logging any error. -/
@[deprecated onlyCode? (since := "2026-09-17")]
public def oneCodeStr? [Monad m] [MonadError m] [MonadLog m] [AddMessageContext m] [MonadOptions m]
    (inlines : Array VersoInline) : m (Option VersoCode) :=
  onlyCode? inlines

/-- Reads the Lean name that the arguments to a role consist of. -/
@[deprecated onlyName (since := "2026-09-17")]
public def oneCodeName [Monad m] [MonadError m] (inlines : Array VersoInline) : m Ident :=
  onlyName inlines
