/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

/-
A module holding tests whose docstrings are written in Markdown and in Verso, for checks that the
captured docstring is Markdown in both cases. It also defines a Verso role with its own Markdown
rendering, for checks that such renderings reach the captured docstring.
-/
module

public import Errata
meta import Lean

open Errata
open Lean Doc Elab
open scoped Lean.Doc.Syntax

/--
A Markdown docstring with `code`, _emphasis_ and **strong** text.

* item one
* item two
-/
@[test]
def markdownDoc : Bool := true

set_option doc.verso true in
/--
A Verso docstring that names {name}`Nat.succ` and {lit}`x`, with _emphasis_ and **strong** text.

* item one
* item two
-/
@[test]
def versoDoc : Bool := true

namespace ErrataTests.Docstrings

/-- A reference to a constant, rendered with the shortest name valid where it is rendered. -/
meta structure ShortName where
  /-- The referenced constant. -/
  target : Name
deriving TypeName

/-- References a constant by the shortest name that is valid where the docstring is rendered. -/
@[doc_role]
meta def shortName (xs : TSyntaxArray `inline) : DocM (Inline ElabInline) := do
  let #[stx] := xs | throwError "expected one code argument"
  let `(inline|code($s)) := stx | throwErrorAt stx "expected a code argument"
  let target ← realizeGlobalConstNoOverloadWithInfo (mkIdentFrom s s.getString.toName)
  return .custom (ShortName.mk target) #[.code s.getString]

/-- Shortens the name in the scope where the docstring is rendered. -/
@[doc_inline_md]
meta def shortNameRender : InlineMdRendererOf ShortName := fun _go data _content => do
  return #[s!"`{← unresolveNameGlobal data.target}`"]

/-- A constant for a docstring to refer to. -/
def docstringTarget : Nat := 0

set_option doc.verso true in
/--
Refers to {shortName}`docstringTarget`, whose name is rendered when the docstring is captured.
-/
@[test]
def customRoleDoc : Bool := true
