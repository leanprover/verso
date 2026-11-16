import Lean.AddDecl
import Lean.Attributes
import Lean.DocString
import Lean.Elab.Exception
import Lean.Elab.InfoTree.Main
import Lean.Parser.Term

open Lean Elab

set_option doc.verso false

/-!
# Attributes That Define Constants

An attribute that defines a further constant whose name is written in the attribute, the way that
Mathlib's `to_additive` does. The new constant takes its docstring from a doc comment in the attribute
if there is one, and otherwise from the declaration. A nested attribute is applied to the new constant.
-/

/-- Defines a constant with the same type and value under the given name. -/
syntax (name := alsoAs) "also_as " ident (" (" &"attr" " := " Parser.Term.attrInstance ")")? (docComment)? : attr

initialize registerBuiltinAttribute {
  name := `alsoAs
  descr := "Defines a constant with the same type and value under the name in the attribute"
  applicationTime := .afterCompilation
  add := fun decl stx _ => do
    let `(attr| also_as $id:ident $[(attr := $nested)]? $[$doc:docComment]?) := stx
      | throwUnsupportedSyntax
    let info ← getConstInfo decl
    let name := id.getId
    addDecl <| .defnDecl <|
      mkDefinitionValEx name info.levelParams info.type
        (.const decl (info.levelParams.map .param)) .abbrev .safe [decl]
    if let some doc := doc then
      addDocStringCore name (← getDocStringText doc)
    else if let some doc ← findDocString? (← getEnv) decl then
      addDocStringCore name doc
    pushInfoLeaf <| .ofTermInfo {
      elaborator := .anonymous, lctx := {}, expectedType? := none, stx := id,
      expr := .const name [], isBinder := true }
    if let some nested := nested then
      Attribute.add name nested.raw[1].getKind nested.raw[1]
}
