/-
Copyright (c) 2023 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module
public import Lean.Elab.Command
meta import Lean.Elab.Command
import Lean.Parser

namespace Verso.Method

public section

open Lean Parser Elab Command

@[run_builtin_parser_attribute_hooks]
meta def method := leading_parser
  declModifiers false >> "defmethod " >> declId >> ppIndent optDeclSig >> declVal >> optDefDeriving

/-- Like 'def', except the namespace is resolved to an existing unique
name, and the resulting name is defined in that namespace.

In particular, `defmethod A.B.f ...` first resolves `A.B`. If there is
a unique resolution, say `Lib.More.A.B`, then it is equivalent to
`def Lib.More.A.B.f ...`. If there is no unique resolution, it is an
error.
-/
syntax (name := methodDecl) method : command

@[command_elab methodDecl]
meta def elabMethodDecl : CommandElab := fun stx => do
  let ident := stx[0][2][0]
  let .ident origInfo origSubstr x _ := ident
    | throwErrorAt ident "Expected identifier"
  let .str ns@(.str ..) y := x
    | throwErrorAt ident "Expected definable identifier with namespace"
  let options ← (resolveGlobalName ns : CommandElabM _)
  match options with
  | [] => throwErrorAt ident "'{ns}' not found"
  | found@(_ :: _ :: _) =>
    let exprs ← liftTermElabM <| found.mapM fun (i, _) => do
      let i' := mkCIdent i
      Term.elabTerm (← `(term| $i' )) none
    let names : MessageData := .group <| .joinSep (exprs.map (.ofFormat .line ++ toMessageData ·)) ","
    throwErrorAt ident "'{ns}' is ambiguous - found:{names}\n\nPlease write a more specific namespace."
  | [(resolved, _)] =>
    let withNewName := stx.modifyArg 0 (·.modifyArg 2 (·.modifyArg 0 (fun _ => .ident origInfo origSubstr (unambiguous resolved y) [])))
    let decl ← withNewName.replaceM fun
      | .atom info "defmethod" => pure (some (.atom info "def"))
      | .node info ``method args => pure (some (.node info ``Parser.Command.declaration args))
      | _ => pure none
    let decl' := open Parser.Command in
      Syntax.node .none ``declaration #[decl[0][0], .node .none ``definition decl[0].getArgs[1:7]]
    elabCommand decl'
where
  inRoot : Name → Name
    | .anonymous => .str .anonymous "_root_"
    | .str ns n => .str (inRoot ns) n
    | .num ns n => .num (inRoot ns) n
  unambiguous (ns : Name) (y : String) : Name :=
    .str (inRoot ns) y
  replaceIdent (n : Name) : Syntax → CommandElabM Syntax
    | .ident info str _ preres => pure <| .ident info str n preres
    | other => throwErrorAt other "Not an identifier: {other}"

end
