/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module
public import Verso.Doc.SourceRange
public import Lean.Server.CodeActions

namespace Verso.Doc

open Lean Elab Server RequestM

public structure PointOfInterest where
  title : String
  selectionRange : Option Syntax.Range := none
  kind : Lean.Lsp.SymbolKind := .constant
  detail? : Option String
deriving TypeName

/--
Save a document-symbol entry for `stx`.

When provided, `selectionSyntax?` marks the smaller source range selected by document-symbol
clients; it must be contained in `stx`'s range. Without it, clients select the whole `stx` range.
-/
public def PointOfInterest.save [Monad m] [MonadInfoTree m] (stx : Syntax) (title : String)
    (selectionSyntax? : Option Syntax := none)
    (kind : Lean.Lsp.SymbolKind := .constant)
    (detail? : Option String := none) : m Unit := do
  let selectionRange :=
    selectionSyntax?.map fun selectionSyntax =>
      let range := requireSyntaxRange s!"PointOfInterest syntax for '{title}'" stx
      let selectionRange := requireSyntaxRange s!"PointOfInterest selection syntax for '{title}'"
        selectionSyntax
      requireContainedSyntaxRange s!"Invalid PointOfInterest selection range for '{title}'"
        range.start range.stop selectionRange
  pushInfoLeaf <| .ofCustomInfo {stx := stx, value := Dynamic.mk (PointOfInterest.mk title selectionRange kind detail?)}
