/-
Copyright (c) 2024-2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module
public import Verso.Output.Html

set_option linter.missingDocs true
set_option doc.verso true

namespace Verso.Genre.Manual

open Verso.Output Html

private def addShy (xs : Array Html) : Array Html :=
  if xs.isEmpty then xs
  else if let some (Verso.Output.Html.tag "wbr" ..) := xs.back? then xs
  else  xs.push (.text false "&shy;")

/--
Adds soft hyphenation opportunities ({lit}`<wbr>` or {lit}`&shy;`) to a single text node, allowing
browsers to break the word at that point. Line break opportunities are added after {lit}`.` and
hyphenation opportunities on transitions from lower-case to upper-case letters, so
{lit}`Verso.Genre.Manual.softHyphenateIdentifiers` becomes
{lit}`Verso.<wbr>Genre.<wbr>Manual.<wbr>soft&shy;Hyphenate&shy;Identifiers`.

Text nodes in the resulting HTML will have their contents escaped according to {name}`esc`.
-/
public def softHyphenateText (esc : Bool) (str : String) : Html := Id.run do
  let mut strs : Array Html := #[]
  let mut prior : Option Char := none
  let mut start := str.startPos
  let mut iter := str.startPos
  while h : iter ≠ str.endPos do
    let current := iter.get h
    let iter' := iter.next h
    if prior == some '.' && current != '.' then
      strs := strs.push (.text esc <| start.extract iter)
      -- Break lines after dots without hyphens
      strs := strs.push {{<wbr/>}}
      start := iter
    else if current.isUpper then
      if prior.map (·.isLower) |>.getD false then
        if !strs.isEmpty then
          strs := addShy strs
        -- Break lines at case changes with hyphens
        strs := strs.push (.text esc <| start.extract iter)
        start := iter

    prior := some current
    iter := iter'

  if start != iter then
    strs := addShy strs
    strs := strs.push (.text esc <| start.extract iter)

  if h : strs.size = 1 then strs[0] else .seq strs

/--
Adds soft hyphenation opportunities ({lit}`<wbr>` or {lit}`&shy;`) to all text nodes in the provided
HTML, allowing browsers to break the word at that point. Line break opportunities are added after
{lit}`.` and hyphenation opportunities on transitions from lower-case to upper-case letters, so
{lit}`Verso.Genre.Manual.softHyphenateIdentifiers` becomes
{lit}`Verso.<wbr>Genre.<wbr>Manual.<wbr>soft&shy;Hyphenate&shy;Identifiers`.
-/
public def softHyphenateTextNodes (html : Html) : Html :=
  html.visitM (m := Id) (text := rwText)
where
  rwText esc str := pure (some (softHyphenateText esc str))

/--
Adds soft hyphenation opportunities ({lit}`<wbr>` or {lit}`&shy;`) to identifiers in HTML, allowing
browsers to break the word at that point. Line break opportunities are added after {lit}`.` and
hyphenation opportunities on transitions from lower-case to upper-case letters, so
{lit}`Verso.Genre.Manual.softHyphenateIdentifiers` becomes
{lit}`Verso.<wbr>Genre.<wbr>Manual.<wbr>soft&shy;Hyphenate&shy;Identifiers`.

Here, “identifiers” refers to text nodes found within `<code>` tags.
-/
public partial def softHyphenateIdentifiers (html : Html) : Html :=
  html.visitM (m := Id) (tag := rwTag)
where
  rwTag
    | "code", attrs, content => pure (some (.tag "code" attrs (softHyphenateTextNodes content)))
    | _, _, _ => pure none
