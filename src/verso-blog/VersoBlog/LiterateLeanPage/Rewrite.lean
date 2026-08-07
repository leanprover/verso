/-
Copyright (c) 2023-2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module
public import Lean.Data.NameMap

public section

open Lean

namespace Verso.Genre.Blog.Literate

inductive Pat where
  | char : Char → Pat
  | str : String → Pat
  | var : Name → Pat
  | any : Pat
deriving BEq, Hashable, Repr, Inhabited

-- TODO rewrite with dynamic programming
partial def Pat.match (p : List Pat) (str : String) : Option (Lean.NameMap String) :=
  go str.startPos p
where
  go iter
    | [] => if iter = str.endPos then pure {} else failure
    | .char c :: p' =>
      if h : iter ≠ str.endPos then
        if iter.get h == c then
          go (iter.next h) p'
        else failure
      else failure
    | .str s :: p' =>
      go iter (s.toList.map .char ++ p')
    | .var x :: p' => do
      let mut iter' := str.endPos
      while iter' ≥ iter do
        try
          let rest ← go iter' p'
          return rest.insert x (str.extract iter iter')
        catch
          | () =>
            if h : iter' = str.startPos then
              break
            else
              iter' := iter'.prev h
              continue
      failure
    | .any :: p' => do
      let mut iter' := str.endPos
      while iter' ≥ iter do
        try
          return (← go iter' p')
        catch
          | () =>
            if h : iter' = str.startPos then
              break
            else
              iter' := iter'.prev h
              continue
      failure

inductive Template where
  | str : String → Template
  | var : Name → Template
deriving BEq, Hashable, Repr, Inhabited

def Template.subst (vars : Lean.NameMap String) : Template → Except String String
  | .str s => pure s
  | .var x => if let some s := vars.find? x then pure s else throw s!"Not found: '{x}'"

end Verso.Genre.Blog.Literate
