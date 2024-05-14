/-
Copyright (c) 2023-2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import Verso.Doc
import Verso.Doc.Concrete
import Verso.Doc.TeX
import Verso.Doc.Html
import Verso.Output.TeX
import Verso.Output.Html
import Verso.Doc.Lsp
import Verso.Doc.Elab

import Verso.Genre.Manual.Basic
import Verso.Genre.Manual.Slug
import Verso.Genre.Manual.TeX
import Verso.Genre.Manual.Html
import Verso.Genre.Manual.Html.Style
import Verso.Genre.Manual.Docstring

open Lean (Name NameMap Json ToJson FromJson)

open Verso.Doc Elab

open Verso.Genre.Manual.TeX

namespace Verso.Genre

namespace Manual

def Block.paragraph : Block where
  name := `Verso.Genre.Manual.Block.paragraph

def paragraph.descr : BlockDescr where
  traverse := fun _ _ _ => pure none
  toTeX :=
    some <| fun _ go _ _ content => do
      pure <| .seq <| ← content.mapM fun b => do
        pure <| .seq #[← go b, .raw "\n"]
  toHtml :=
    open Verso.Output.Html in
    some <| fun _ go _ _ content => do
      pure <| {{<div class="paragraph">{{← content.mapM go}}</div>}}


@[directive_expander paragraph]
def paragraph : DirectiveExpander
  | #[], stxs => do
    let args ← stxs.mapM elabBlock
    let val ← ``(Block.other Block.paragraph #[ $[ $args ],* ])
    pure #[val]
  | _, _ => Lean.Elab.throwUnsupportedSyntax


structure Config where
  destination : System.FilePath := "_out"
  maxTraversals : Nat := 20

def ensureDir (dir : System.FilePath) : IO Unit := do
  if !(← dir.pathExists) then
    IO.FS.createDirAll dir
  if !(← dir.isDir) then
    throw (↑ s!"Not a directory: {dir}")

def traverse (logError : String → IO Unit) (text : Part Manual) (config : Config) : ReaderT ExtensionImpls IO (Part Manual × TraverseState) := do
  let topCtxt : Manual.TraverseContext := {logError}
  let mut state : Manual.TraverseState := {}
  let mut text := text
  let ExtensionImpls ← readThe ExtensionImpls
  for _ in [0:config.maxTraversals] do
    let (text', state') ← Genre.traverse Manual text |>.run ExtensionImpls topCtxt state
    if text' == text && state' == state then
      return (text', state')
    else
      state := state'
      text := text'
  return (text, state)


open IO.FS in
def emitTeX (logError : String → IO Unit) (config : Config) (state : TraverseState) (text : Part Manual) : ReaderT ExtensionImpls IO Unit := do
  let opts : TeX.Options Manual (ReaderT ExtensionImpls IO) := {
    headerLevels := #["chapter", "section", "subsection", "subsubsection", "paragraph"],
    headerLevel := some ⟨0, by simp_arith [Array.size, List.length]⟩,
    logError := fun msg => logError msg
  }
  let authors := text.metadata.map (·.authors) |>.getD []
  let date := text.metadata.bind (·.date) |>.getD ""
  let ctxt := {logError}
  let frontMatter ← text.content.mapM (·.toTeX (opts, ctxt, state))
  let chapters ← text.subParts.mapM (·.toTeX (opts, ctxt, state))
  let dir := config.destination.join "tex"
  ensureDir dir
  withFile (dir.join "main.tex") .write fun h => do
    h.putStrLn (preamble text.titleString authors date)
    for b in frontMatter do
      h.putStrLn b.asString
    for c in chapters do
      h.putStrLn c.asString
    h.putStrLn postamble

open Verso.Output (Html)

partial def toc (opts : Html.Options Manual (ReaderT ExtensionImpls IO)) (ctxt : TraverseContext) (state : TraverseState) : Part Manual → ReaderT ExtensionImpls IO Html.Toc
  | .mk title sTitle meta _ sub => do
    let titleHtml ← Html.seq <$> title.mapM (Manual.toHtml opts.lift ctxt state)
    let some {id := some id, number, ..} := meta
      | throw <| .userError s!"No ID for {sTitle} - {repr meta}"
    let some v := state.externalTags.find? id
      | throw <| .userError s!"No external ID for {sTitle}"
    let children ← sub.mapM (toc  opts ctxt state)
    pure <| .entry titleHtml v number children

def emitHtmlSingle (logError : String → IO Unit) (config : Config) (state : TraverseState) (text : Part Manual) : ReaderT ExtensionImpls IO Unit := do
  let authors := text.metadata.map (·.authors) |>.getD []
  let date := text.metadata.bind (·.date) |>.getD ""
  let opts := {logError := fun msg => logError msg}
  let ctxt := {logError}
  let titleHtml ← Html.seq <$> text.title.mapM (Manual.toHtml opts ctxt state)
  let introHtml ← Html.seq <$> text.content.mapM (Manual.toHtml opts ctxt state)
  let contents ← Html.seq <$> text.subParts.mapM (Manual.toHtml {opts with headerLevel := 2} ctxt state)
  let pageContent := open Verso.Output.Html in
    {{<section>{{Html.titlePage titleHtml authors introHtml ++ contents}}</section>}}
  let toc ← text.subParts.mapM (toc opts ctxt state)
  let dir := config.destination.join "html-single"
  ensureDir dir
  IO.FS.withFile (dir.join "book.css") .write fun h => do
    h.putStrLn Html.Css.pageStyle
  IO.FS.withFile (dir.join "index.html") .write fun h => do
    h.putStrLn Html.doctype
    h.putStrLn (Html.page toc text.titleString pageContent state.extraCss state.extraJs).asString

abbrev ExtraStep := TraverseContext → TraverseState → IO Unit

def manualMain (extensionImpls : ExtensionImpls) (text : Part Manual) (options : List String) (extraSteps : List ExtraStep := []) : IO UInt32 := (ReaderT.run · extensionImpls) do
  let hasError ← IO.mkRef false
  let logError msg := do hasError.set true; IO.eprintln msg
  let cfg ← opts {} options
  let (text, state) ← traverse logError text cfg
  emitTeX logError cfg state text
  emitHtmlSingle logError cfg state text

  if (← hasError.get) then
    IO.eprintln "Errors were encountered!"
    return 1
  else
    return 0
where
  opts (cfg : Config)
    | ("--output"::dir::more) => opts {cfg with destination := dir} more
    | (other :: _) => throw (↑ s!"Unknown option {other}")
    | [] => pure cfg
