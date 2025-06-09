/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import Lean.Data.Options

open Lean MonadOptions

register_option verso.literateMarkdown.logInlines : Bool := {
  defValue := false
  group := "doc"
  descr := "Whether to log failures to elaborate inline code items in Markdown comments."
}

register_option verso.literateMarkdown.convertDoccomments : Bool := {
  defValue := false
  group := "doc"
  descr := "Whether to convert doccomments on definitions to text ."
}


namespace Verso.Genre.Blog.Literate

def getLogInlines [Monad m] [MonadOptions m] : m Bool := do
  return (← getOptions).get verso.literateMarkdown.logInlines.name verso.literateMarkdown.logInlines.defValue

def getConvertDoccomments [Monad m] [MonadOptions m] : m Bool := do
  return (← getOptions).get verso.literateMarkdown.convertDoccomments.name verso.literateMarkdown.convertDoccomments.defValue
