/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module
public import VersoGen.Doc.Shrink
public import VersoGen.Edit.Basic

set_option doc.verso true

namespace VersoGen.Edit

open VersoGen.Doc VersoGen.Doc.SurfaceDoc Plausible

public instance : Shrinkable PartEdit := {}

public instance : Shrinkable InlineEdit where
  shrink
    | .insertInline i inl => (shrinkInline inl).map (.insertInline i)
    | .wrapInlines start stop w => (shrinkInline w).map (.wrapInlines start stop)
    | _ => []

public instance : Shrinkable SiblingEdit where
  shrink
    | .insert i n => (shrinkNode n).map (.insert i)
    | _ => []

public instance : Shrinkable Edit where
  shrink
    | .inlines e => (Shrinkable.shrink e).map .inlines
    | .footnoteDef e =>
      (shrinkArray shrinkInline e.content).map fun content => .footnoteDef { content }
    | .sibling e => (Shrinkable.shrink e).map .sibling
    | .contents e => (Shrinkable.shrink e).map .contents
    | _ => []
