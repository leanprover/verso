/-
Copyright (c) 2024-2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module
import Lean.Meta
public import Lean.Meta.Basic
import Lean.PrettyPrinter.Delaborator

open Lean
open Lean.PrettyPrinter Delaborator

namespace Verso.Genre.Manual.Block.Docstring

def stripNS : Syntax → Syntax
  | .ident info substr x pre => .ident info substr x.getString!.toName pre
  | .node info kind args => .node info kind (args.map stripNS)
  | other => other

def stripInfo : Syntax → Syntax
  | .ident _ substr x pre => .ident .none substr x pre
  | .node _ kind args => .node .none kind (args.map stripInfo)
  | .atom _ x => .atom .none x
  | .missing => .missing

/--
Strip an explicit `_root_` from each identifier, to work around configuration problems in the pretty
printer
-/
def stripRootPrefix (stx : Syntax) : Syntax :=
  stx.rewriteBottomUp fun
  | .ident info substr x pre => .ident info substr (x.replacePrefix `_root_ .anonymous) pre
  | s => s

/--
Postprocess Lean's own `ppSignature` to remove the namespace (used for constructors) and any
`_root_` prefixes that have snuck in. The latter is not strictly correctness preserving, but it's an
expedient hack. It also removes the info from the constant's name if requested, to avoid unwanted
linking from a definition site to itself.
-/
public def ppSignature (c : Name) (showNamespace : Bool := true) (openDecls : List OpenDecl := []) (constantInfo : Bool := true) : MetaM FormatWithInfos :=
  withTheReader Core.Context (fun ρ => {ρ with openDecls := ρ.openDecls ++ openDecls}) <| do
  let decl ← getConstInfo c
  let e := .const c (decl.levelParams.map mkLevelParam)
  let (stx, infos) ← delabCore e (delab := delabConstWithSignature)
  let stx : Syntax ←
    stripRootPrefix <$>
    if showNamespace then pure stx.raw
    else
      match stx with
      | `(declSigWithId|$nameUniv $argsRet:declSig ) => do
        `(declSigWithId|$(⟨stripNS nameUniv⟩) $argsRet) <&> (·.raw)
      | _ => pure stx.raw
  let stx : Syntax ←
    if constantInfo then pure stx
    else
      match stx with
      | `(declSigWithId|$nameUniv $argsRet:declSig ) => do
        `(declSigWithId|$(⟨stripInfo nameUniv⟩) $argsRet) <&> (·.raw)
      | _ => pure stx

  return ⟨← ppTerm ⟨stx⟩, infos⟩  -- HACK: not a term

def nameString (x : Name) (showNamespace : Bool) :=
  if showNamespace then x.toString
  else
    match x with
    | .str _ s => s
    | _ => x.toString

public def ppName (c : Name) (showUniverses := true) (showNamespace : Bool := true) (openDecls : List OpenDecl := []) : MetaM FormatWithInfos :=
  MonadWithReaderOf.withReader (fun (ρ : Core.Context) => {ρ with openDecls := ρ.openDecls ++ openDecls}) <|do
  let decl ← getConstInfo c
  let e := .const c (decl.levelParams.map mkLevelParam)
  let (stx, infos) ← withOptions (pp.universes.set · true |> (pp.fullNames.set · true)) <|
    delabCore e (delab := delabConst)
  -- The special-casing here is to allow the `showNamespace` setting to work. This is perhaps too
  -- big of a hammer...
  match stx with
    | `($x:ident.{$uni,*}) =>
      let unis : Format ← do
        if showUniverses then
          let us ← uni.getElems.toList.mapM (ppCategory `level ·.raw)
          pure <| ".{" ++ Format.joinSep us ", " ++ "}"
        else
          pure .nil

      return ⟨Std.Format.tag SubExpr.Pos.root (.text (nameString x.getId showNamespace)) ++ unis, infos⟩
    | `($x:ident) =>
      return ⟨Std.Format.tag SubExpr.Pos.root (Std.Format.text (nameString x.getId showNamespace)), infos⟩
    | _ =>
      return ⟨← ppTerm stx, infos⟩
