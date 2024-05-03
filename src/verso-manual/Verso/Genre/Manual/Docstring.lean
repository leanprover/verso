/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import Lean
import Verso.Genre.Manual.Basic
import Verso.Doc.Elab.Monad
import Verso.Doc.ArgParse

open Lean

open Verso.Doc.Elab.PartElabM

namespace Verso.Genre.Manual

namespace Block

def docstring (name : Name) : Block where
  name := `Verso.Genre.Manual.Block.docstring
  data := ToJson.toJson name

end Block

def docstring.descr : BlockDescr where
  traverse _ _ _ := pure none
  toHtml := some <| fun _goI goB _id _info contents => contents.mapM goB
  toTeX := some <| fun _goI goB _id _info contents => contents.mapM goB



open Verso.Doc.Elab


@[block_role_expander docstring]
def docstring : BlockRoleExpander
  | args, #[] => do
    match args with
    | #[.anon (.name x)] =>
      let name ← resolveGlobalConstNoOverload x
      match ← Lean.findDocString? (← getEnv) name with
      | none => throwErrorAt x "No docs found for '{x}'"
      | some docs =>
        pure #[← ``(Verso.Doc.Block.other (Verso.Genre.Manual.Block.docstring $(quote name)) #[Verso.Doc.Block.code $(quote docs)])]
    | _ => throwError "Expected exactly one positional argument that is a name"
  | _, more => throwErrorAt more[0]! "Unexpected block argument"
