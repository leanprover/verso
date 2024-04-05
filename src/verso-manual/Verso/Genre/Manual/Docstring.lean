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
  traverse _ _ := pure none
  toHtml := some <| fun go _info contents => contents.mapM go
  toTeX := some <| fun go _info contents => contents.mapM go



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
        pure #[← ``(Verso.Doc.Block.other (Verso.Genre.Manual.Block.docstring $(quote name)) #[Verso.Doc.Block.code none #[] 0 $(quote docs)])]
    | _ => throwError "Expected exactly one positional argument that is a name"
  | _, more => throwErrorAt more[0]! "Unexpected block argument"
