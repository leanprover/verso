/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import VersoManual.Basic
import VersoManual.ExternalLean
import VersoLiterate
import Lean.Data.Json

namespace Verso.Genre.Manual

open VersoLiterate
open Verso.Code.External
open Verso.Output Html
open Verso.Doc.Html
open Lean

block_extension Block.literateDocstring where
  traverse _ _ _ _ := pure none
  toHtml := some fun _goI goB _id _data contents => do
    pure {{<div class="literate-docstring">{{← contents.mapM goB}}</div>}}
  toTeX := none

block_extension Block.literateDocstringPart (level : Nat) where
  data := level
  traverse _ _ _ _ := pure none
  toHtml := some fun goI goB _id data contents => do
    let .ok (level : Nat) := FromJson.fromJson? data
      | HtmlT.logError s!"Couldn't decode nesting level from {data.compress}"
        pure .empty
    let title : Html ←
      if let some title := contents[0]? then
        if let .para xs := title then
          xs.mapM goI
        else
          HtmlT.logError s!"Expected a paragraph at the beginning of a docstring section"
          pure .empty
      else
        HtmlT.logError s!"Expected a block at the beginning of a docstring section"
        pure .empty
    let contents := contents.extract 1
    pure {{
      <section>
        {{.tag s!"h{level + 1}" #[] title}}
        {{← contents.mapM goB}}
      </section>
    }}
  toTeX := none


instance : LoadLiterate Manual where
  inline goI
    | .highlighted hl, _ => ExternalCode.leanInline hl {}
    | .data .., content => .concat <| content.map goI

  block _goI goB
    | .highlighted hl, _ => ExternalCode.leanBlock hl {}
    | .data .., content => .concat <| content.map goB

  docstring _indent _declName? content := .other Block.literateDocstring content

  docstringPart lvl title contents := .other (Block.literateDocstringPart lvl) (#[.para title] ++ contents)


open Lean.Doc.Syntax
open Verso.Doc Elab Concrete
open Lean.Elab Command Term
open PartElabM
def getModuleWithDocs (path : StrLit) (mod : Ident) (title : StrLit) : PartElabM Name :=
  withTraceNode `verso.blog.literate (fun _ => pure m!"Literate '{title.getString}'") do

  let titleParts ← stringToInlines title
  let titleString := inlinesToString (← getEnv) titleParts
  let initState : PartElabM.State := .init (.node .none nullKind titleParts)

  let g := Expr.const ``Manual []

  let (titleTerm, _st) ← DocElabM.run (← manualGenreElabContext) {} initState <| do
    titleParts.mapM (elabInline ⟨·⟩)

  let modJson ← withTraceNode `verso.blog.literate.loadMod (fun _ => pure m!"Loading '{mod}' in '{path}'") <|
    loadModuleJson path.getString mod.getId.toString

  let jsonName ← do
    let name ← mkFreshUserName (mod.getId ++ `json)
    addAndCompile <| .defnDecl {
      name, levelParams := [], type := mkConst ``String, value := mkStrLit modJson,
      hints := .regular 0, safety := .safe
    }
    pure name

  let mod ← do
    let name ← mkFreshUserName (mod.getId ++ `getPart)
    let title ← titleTerm.mapM (elabTerm · (some (.app (mkConst ``Verso.Doc.Inline) g)))
    let title ← Meta.mkArrayLit (.app (mkConst ``Verso.Doc.Inline) g) title.toList
    withOptions (Compiler.LCNF.compiler.extract_closed.set · false) do
      addAndCompile <| .defnDecl {
        name, levelParams := [], type := .app (mkConst ``Verso.Doc.VersoDoc) g,
        value := ← Meta.mkAppM ``modToPage! #[
          ← Meta.mkAppM ``VersoLiterate.loadJsonString! #[mkConst jsonName, mkStrLit s!"JSON for {mod.getId}"],
          title,
          mkStrLit titleString
        ],
        hints := .regular 0, safety := .safe
      }
    pure name
  return mod

section
open ArgParse

variable [Monad m] [MonadError m] [MonadLiftT CoreM m]

structure IncludeLiterateConfig where
  path : StrLit
  level : Option NumLit
  modName : Ident
  title : StrLit

instance : FromArgs IncludeLiterateConfig m where
  fromArgs :=
    IncludeLiterateConfig.mk <$> .positional' `path  <*> .named' `level true <*> .positional' `name <*> .positional' `title


@[part_command Lean.Doc.Syntax.command]
def includeLiterateSection : PartCommand
  | `(block|command{includeLiterate $args* }) => do
    let {path, level, modName, title} ← parseThe IncludeLiterateConfig (← parseArgs args)
    let ref ← getRef
    if let some lvl := level then
      let name ← getModuleWithDocs path modName title
      closePartsUntil lvl.getNat ref.getHeadInfo.getPos!
      addPart <| .included (mkIdentFrom modName name)
    else
      let name ← getModuleWithDocs path modName title
      addPart <| .included (mkIdentFrom modName name)

  | _ => (Lean.Elab.throwUnsupportedSyntax : PartElabM Unit)
