/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module
public import Plausible.Shrinkable
public import VersoGen.Doc.Basic

set_option doc.verso true

namespace VersoGen.Doc

open SurfaceDoc Plausible

public def shrinkArray (shrinkElem : α → List α) (xs : Array α) : List (Array α) := Id.run do
  let mut out := #[]
  for h : i in [0:xs.size] do
    out := out.push (xs.eraseIdx i)
    for y in shrinkElem xs[i] do
      out := out.push (xs.set i y)
  return out.toList

public partial def shrinkInline (inl : Inline) : List Inline :=
  let content := shrinkArray shrinkInline
  match inl with
  | .emph c => c.toList ++ (content c).map .emph
  | .bold c => c.toList ++ (content c).map .bold
  | .link c t => c.toList ++ (content c).map (.link · t)
  | .role name args c => c.toList ++ (content c).map (.role name args)
  | _ => []

public instance : Shrinkable Inline := ⟨shrinkInline⟩

public partial def shrinkBlock (b : Block) : List Block :=
  let blocks := shrinkArray shrinkBlock
  b.innerBlocks.toList ++
  match b with
  | .para c =>
    shrinkArray shrinkInline c |>.filterMap fun c =>
      if c.isEmpty then none else some (.para c)
  | .ul items => shrinkArray blocks items |>.map .ul
  | .ol items => shrinkArray blocks items |>.map .ol
  | .dl items => shrinkArray (fun (t, bs) => (blocks bs).map (t, ·)) items |>.map .dl
  | .blockquote bs => blocks bs |>.map .blockquote
  | .directive name args bs => blocks bs |>.map (.directive name args)
  | .code name args lines => shrinkArray (fun _ => []) lines |>.map (.code name args)
  | .footnoteDef label c => shrinkArray shrinkInline c |>.map (.footnoteDef label)
  | .linkDef label url =>
    let params := Shrinkable.shrink label |>.flatMap (fun lbl =>
      Shrinkable.shrink url |>.map (lbl, ·))
    params.map fun (lbl, u) => .linkDef lbl u
  | _ => []

public instance : Shrinkable Block := ⟨shrinkBlock⟩

public partial def shrinkPart (p : Part) : List Part :=
  p.subParts.toList ++
  (shrinkArray shrinkBlock p.blocks).map ({ p with blocks := · }) ++
  (shrinkArray shrinkPart p.subParts).map ({ p with subParts := · })

public instance : Shrinkable Part := ⟨shrinkPart⟩

public def shrinkNode : Node → List Node
  | .part p => (shrinkPart p).map .part
  | .block b => (shrinkBlock b).map .block
  | .item bs => (shrinkArray shrinkBlock bs).map .item
  | .descItem (t, bs) => (shrinkArray shrinkBlock bs).map fun bs => .descItem (t, bs)

public instance : Shrinkable Node := ⟨shrinkNode⟩
