/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import SubVerso.Helper
import SubVerso.Module
import VersoBlog.Basic
import VersoBlog.LiterateLeanPage.Options
import MD4Lean
import VersoLiterate

set_option doc.verso true

open Verso Doc
open Lean

open SubVerso.Highlighting
open SubVerso.Helper
open SubVerso.Module
open Verso.Doc.Concrete (stringToInlines)

namespace Verso.Genre.Blog.Literate

open VersoLiterate

instance [bg : BlogGenre g] : LoadLiterate g where
  inline goI
    | .highlighted hl, content =>
      .other (bg.inline_eq ▸ .highlightedCode { contextName := `lean } hl) <| content.map goI
    | .data .., xs => .concat <| xs.map goI
  block _goI goB
    | .highlighted hl, content =>
      .other (bg.block_eq ▸ .highlightedCode { contextName := `lean } hl) <| content.map goB
    | .data .., xs => .concat <| xs.map goB

  docstring indent declName? xs := .other (bg.block_eq ▸ .docstring indent declName?) xs

  docstringPart lvl title content :=
    .other (bg.block_eq ▸ .docstringSection lvl) <|
      #[.para title] ++ content


section
variable [Monad m] [MonadError m] [MonadQuotation m]


open Verso Doc in
open Lean Elab Command Term in
open PartElabM in
def elabFromModuleDocs (x : Ident) (path : StrLit) (mod : Ident) (title : StrLit) (genre : Term) (metadata? : Option Term) : CommandElabM Unit :=
  withTraceNode `verso.blog.literate (fun _ => pure m!"Literate '{title.getString}'") do

  let titleParts ← stringToInlines title
  let titleString := inlinesToString (← getEnv) titleParts
  let initState : PartElabM.State := .init (.node .none nullKind titleParts)


  let g ← runTermElabM fun _ => Term.elabTerm genre (some (.const ``Doc.Genre []))

  let (titleTerm, _st) ← liftTermElabM <| DocElabM.run ⟨genre, g, .always⟩ {} initState <| do
    titleParts.mapM (elabInline ⟨·⟩)

  let modJson ← withTraceNode `verso.blog.literate.loadMod (fun _ => pure m!"Loading '{mod}' in '{path}'") <|
    loadModuleJson path.getString mod.getId.toString

  let jsonName ← runTermElabM fun _ => do
    let name ← mkFreshUserName (x.getId ++ `json)
    addAndCompile <| .defnDecl {
      name, levelParams := [], type := mkConst ``String, value := mkStrLit modJson,
      hints := .regular 0, safety := .safe
    }
    pure name


  let metadata ← runTermElabM fun _ => do
    let metadataType ← Meta.mkAppM ``Genre.PartMetadata #[g]
    if let some metadataTerm := metadata? then
      Meta.mkAppM ``some #[← elabTerm metadataTerm (some metadataType)]
    else
      Meta.mkAppOptM ``none #[some metadataType]

  let mod ← runTermElabM fun _ => do
    let name ← mkFreshUserName (x.getId ++ `getPart)
    let title ← titleTerm.mapM (elabTerm · (some (.app (mkConst ``Verso.Doc.Inline) g)))
    let title ← Meta.mkArrayLit (.app (mkConst ``Verso.Doc.Inline) g) title.toList
    withOptions (Compiler.LCNF.compiler.extract_closed.set · false) do
      addAndCompile <| .defnDecl {
        name, levelParams := [], type := .app (mkConst ``Verso.Doc.VersoDoc) g,
        value := ← Meta.mkAppM ``modToPage! #[
          ← Meta.mkAppM ``VersoLiterate.loadJsonString! #[mkConst jsonName, mkStrLit s!"JSON for {x.getId}"],
          title,
          mkStrLit titleString,
          metadata
        ],
        hints := .regular 0, safety := .safe
      }
    pure name

  let metadata ← if let some m := metadata? then `(some $m) else `(none)
  elabCommand <| ← `(command|def $x : VersoDoc $genre := $(mkIdent mod).withMetadata $metadata)


end

end Literate
open Literate

open Lean.Parser (sepByIndent)
open Lean.Parser.Term
open Verso.Doc.Concrete

open Lean.Parser.Tactic

/--
Creates a post from a literate Lean module with Verso-based module docstrings in it. Markdown module
docstrings are supported, but no attempt is made to elaborate included code.

Specifically, `literate_page POST from MOD in DIR as TITLE` defines a post {lit}`POST` by elaborating the
module {lit}`MOD` in the project directory {lit}`DIR` with title {lit}`TITLE`.

{lit}`DIR` should be a project directory that contains a toolchain file and a Lake configuration
(`lakefile.toml` or `lakefile.lean`), which should depend on the same version of Verso that this
website is using.
-/
syntax "literate_page " ident optConfig " from " ident " in " str " as " str (" with " term)? : command
/--
Creates a post from a literate Lean module with Verso-based module docstrings in it. Markdown module
docstrings are supported, but no attempt is made to elaborate included code.

Specifically, `literate_post POST from MOD in DIR as TITLE` defines a post {lit}`POST` by elaborating the
module {lit}`MOD` in the project directory {lit}`DIR` with title {lit}`TITLE`.

{lit}`DIR` should be a project directory that contains a toolchain file and a Lake configuration
(`lakefile.toml` or `lakefile.lean`), which should depend on the same version of Verso that this
website is using.
-/
syntax "literate_post " ident optConfig " from " ident " in " str " as " str (" with " term)? : command

open Verso Doc in
open Lean Elab Command in
elab_rules : command
  | `(literate_page $x from $mod in $path as $title $[with $metadata]?) => do

    withScope (fun sc => {sc with opts := Elab.async.set sc.opts false}) do
      let genre ← `(Page)
      elabFromModuleDocs x path mod title genre metadata


open Verso Doc in
open Lean Elab Command in
elab_rules : command
  | `(literate_post $x from $mod in $path as $title $[with $metadata]?) => do

    withScope (fun sc => {sc with opts := Elab.async.set sc.opts false}) do
      let genre ← `(Post)
      elabFromModuleDocs x path mod title genre metadata
