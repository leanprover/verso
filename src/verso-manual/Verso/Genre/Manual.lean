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
import Verso.FS

import Verso.Genre.Manual.Basic
import Verso.Genre.Manual.Slug
import Verso.Genre.Manual.TeX
import Verso.Genre.Manual.Html
import Verso.Genre.Manual.Html.Style
import Verso.Genre.Manual.Index
import Verso.Genre.Manual.Glossary
import Verso.Genre.Manual.Docstring

open Lean (Name NameMap Json ToJson FromJson)

open Verso.FS

open Verso.Doc Elab

open Verso.Genre.Manual.TeX

open Verso.Code.Hover (Dedup)

namespace Verso.Genre

namespace Manual

def Inline.ref : Inline where
  name := `Verso.Genre.Manual.Inline.ref

@[inline_extension Inline.ref]
def ref.descr : InlineDescr where
  traverse := fun _ info content => do
    match FromJson.fromJson? info with
    | .error e =>
      logError e; pure none
    | .ok (name, none) =>
      if let some (path, htmlId) := (← get).resolveTag name then
        let dest := String.join (path.map ("/" ++ ·) |>.toList) ++ "#" ++ htmlId
        pure <| some <| .other {Inline.ref with data := ToJson.toJson (name, some dest)} content
      else pure none
    | .ok (_, some (dest : String)) =>
      pure none

  toTeX :=
    some <| fun go _ _ content => do
      pure <| .seq <| ← content.mapM fun b => do
        pure <| .seq #[← go b, .raw "\n"]
  toHtml :=
    open Verso.Output.Html in
    some <| fun go _ info content => do
      match FromJson.fromJson? info with
      | .error e =>
        Html.HtmlT.logError e; content.mapM go
      | .ok (name, none) =>
        Html.HtmlT.logError ("No destination found for tag '" ++ name ++ "'"); content.mapM go
      | .ok (_, some dest) =>
        pure {{<a href={{dest}}>{{← content.mapM go}}</a>}}

def ref (content : Array (Doc.Inline Manual)) (tag : String) : Doc.Inline Manual :=
  let data : (String × Option String) := (tag, none)
  .other {Inline.ref with data := ToJson.toJson data} content

def Block.paragraph : Block where
  name := `Verso.Genre.Manual.Block.paragraph

@[block_extension Block.paragraph]
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
  htmlDepth := 0
  emitTeX : Bool := true
  emitHtmlSingle : Bool := true
  emitHtmlMulti : Bool := true
  extraFiles : List (System.FilePath × String) := []
  extraCss : List String := []
  extraJs : List String := []

def ensureDir (dir : System.FilePath) : IO Unit := do
  if !(← dir.pathExists) then
    IO.FS.createDirAll dir
  if !(← dir.isDir) then
    throw (↑ s!"Not a directory: {dir}")

def traverseMulti (depth : Nat) (path : Path) (part : Part Manual) : TraverseM (Part Manual) :=
  match depth with
  | 0 => Genre.traverse Manual part
  | d + 1 => MonadWithReaderOf.withReader ({· with path := path : TraverseContext}) do
    let meta' ← Verso.Doc.Traverse.part (g := Manual) part
    let mut p := meta'.map part.withMetadata |>.getD part
    if let some md := p.metadata then
      if let some p' ← Traverse.genrePart md p then
        p := p'
    let .mk title titleString meta content subParts := p
    let subParts' ← subParts.mapM fun p => do
      let path' := path.push (p.metadata.bind (·.file) |>.getD (p.titleString.sluggify.toString))
      MonadWithReaderOf.withReader ({· with path := path' : TraverseContext}) (traverseMulti d path' p)
    pure <| .mk (← title.mapM traverseInline) titleString meta (← content.mapM traverseBlock) subParts'
where
  traverseInline := Verso.Doc.Genre.traverse.inline Manual
  traverseBlock := Verso.Doc.Genre.traverse.block Manual

def traverse (logError : String → IO Unit) (text : Part Manual) (config : Config) : ReaderT ExtensionImpls IO (Part Manual × TraverseState) := do
  let topCtxt : Manual.TraverseContext := {logError}
  let mut state : Manual.TraverseState := {}
  let mut text := text
  let ExtensionImpls ← readThe ExtensionImpls
  for _ in [0:config.maxTraversals] do
    let (text', state') ← traverseMulti config.htmlDepth #[] text |>.run ExtensionImpls topCtxt state
    if text' == text && state' == state then
      return (text', state')
    else
      state := state'
      text := text'
  return (text, state)



open IO.FS in
def emitTeX (logError : String → IO Unit) (config : Config) (text : Part Manual) : ReaderT ExtensionImpls IO Unit := do
  let (text, state) ← traverse logError text config
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
    if frontMatter.size > 0 then
      h.putStrLn "\\chapter*{Introduction}"
    for b in frontMatter do
      h.putStrLn b.asString
    for c in chapters do
      h.putStrLn c.asString
    h.putStrLn postamble

open Verso.Output (Html)

instance : Inhabited (StateT (Dedup Html) (ReaderT ExtensionImpls IO) Html.Toc) where
  default := fun _ => default

partial def toc (depth : Nat) (opts : Html.Options Manual IO) (ctxt : TraverseContext) (state : TraverseState) : Part Manual → StateT (Dedup Html) (ReaderT ExtensionImpls IO) Html.Toc
  | .mk title sTitle meta _ sub => do
    let titleHtml ← Html.seq <$> title.mapM (Manual.toHtml (m := ReaderT ExtensionImpls IO) opts.lift ctxt state ·)
    let some {id := some id, number, ..} := meta
      | throw <| .userError s!"No ID for {sTitle} - {repr meta}"
    let some (_, v) := state.externalTags[id]?
      | throw <| .userError s!"No external ID for {sTitle}"
    let ctxt' := if depth > 0 then {ctxt with path := ctxt.path.push (meta.bind (·.file) |>.getD (sTitle.sluggify.toString))} else ctxt
    let children ← sub.mapM (toc (depth - 1) opts ctxt' state)
    pure <| .entry titleHtml ctxt'.path v number children

def emitHtmlSingle (logError : String → IO Unit) (config : Config) (text : Part Manual) : ReaderT ExtensionImpls IO Unit := do
  let dir := config.destination.join "html-single"
  ensureDir dir
  let ((), docs) ← emitContent dir .empty
  IO.FS.writeFile (dir.join "-verso-docs.json") (toString docs.docJson)
where
  emitContent (dir : System.FilePath) : StateT (Dedup Html) (ReaderT ExtensionImpls IO) Unit := do
    let (text, state) ← traverse logError text {config with htmlDepth := 0}
    let authors := text.metadata.map (·.authors) |>.getD []
    let date := text.metadata.bind (·.date) |>.getD ""
    let opts : Html.Options Manual IO := {logError := fun msg => logError msg}
    let ctxt := {logError}
    let titleHtml ← Html.seq <$> text.title.mapM (Manual.toHtml opts.lift ctxt state)
    let introHtml ← Html.seq <$> text.content.mapM (Manual.toHtml opts.lift ctxt state)
    let contents ← Html.seq <$> text.subParts.mapM (Manual.toHtml {opts.lift with headerLevel := 2} ctxt state ·)
    let pageContent := open Verso.Output.Html in
      {{<section>{{Html.titlePage titleHtml authors introHtml ++ contents}}</section>}}
    let toc ← text.subParts.mapM (toc 0 opts ctxt state)
    IO.FS.withFile (dir.join "book.css") .write fun h => do
      h.putStrLn Html.Css.pageStyle
    for (src, dest) in config.extraFiles do
      copyRecursively logError src (dir.join dest)
    for (name, contents) in state.extraJsFiles do
      ensureDir (dir.join "-verso-js")
      IO.FS.withFile (dir.join "-verso-js" |>.join name) .write fun h => do
        h.putStr contents
    for (name, contents) in state.extraCssFiles do
      ensureDir (dir.join "-verso-css")
      IO.FS.withFile (dir.join "-verso-css" |>.join name) .write fun h => do
        h.putStr contents
    IO.FS.withFile (dir.join "index.html") .write fun h => do
      h.putStrLn Html.doctype
      h.putStrLn (Html.page toc text.titleString titleHtml pageContent state.extraCss state.extraJs (extraStylesheets := config.extraCss ++ state.extraCssFiles.toList.map ("/-verso-css/" ++ ·.1)) (extraJsFiles := config.extraJs.toArray ++ state.extraJsFiles.map ("/-verso-js/" ++ ·.1))).asString

 open Verso.Output.Html in
def emitHtmlMulti (logError : String → IO Unit) (config : Config) (text : Part Manual) : ReaderT ExtensionImpls IO Unit := do
  let root := config.destination.join "html-multi"
  ensureDir root
  let ((), docs) ← emitContent root Dedup.empty
  IO.FS.writeFile (root.join "-verso-docs.json") (toString docs.docJson)
where
  emitContent (root : System.FilePath) : StateT (Dedup Html) (ReaderT ExtensionImpls IO) Unit := do
    let (text, state) ← traverse logError text config
    let authors := text.metadata.map (·.authors) |>.getD []
    let date := text.metadata.bind (·.date) |>.getD ""
    let opts : Html.Options _ IO := {logError := fun msg => logError msg}
    let ctxt := {logError}
    let toc ← text.subParts.mapM (toc config.htmlDepth opts ctxt state)
    let titleHtml ← Html.seq <$> text.title.mapM (Manual.toHtml opts.lift ctxt state ·)
    IO.FS.withFile (root.join "book.css") .write fun h => do
      h.putStrLn Html.Css.pageStyle
    for (src, dest) in config.extraFiles do
      copyRecursively logError src (root.join dest)
    for (name, contents) in state.extraJsFiles do
      ensureDir (root.join "-verso-js")
      IO.FS.withFile (root.join "-verso-js" |>.join name) .write fun h => do
        h.putStr contents
    for (name, contents) in state.extraCssFiles do
      ensureDir (root.join "-verso-css")
      IO.FS.withFile (root.join "-verso-css" |>.join name) .write fun h => do
        h.putStr contents
    emitPart titleHtml authors toc opts.lift ctxt state true config.htmlDepth root text
  emitPart (bookTitle : Html) (authors : List String) (bookContents)
      (opts ctxt state)
      (root : Bool) (depth : Nat) (dir : System.FilePath) (part : Part Manual) : StateT (Dedup Html) (ReaderT ExtensionImpls IO) Unit := do
    let titleHtml ← Html.seq <$> part.title.mapM (Manual.toHtml opts.lift ctxt state)
    let introHtml ← Html.seq <$> part.content.mapM (Manual.toHtml opts.lift ctxt state)
    let contents ←
      if depth == 0 then
        Html.seq <$> part.subParts.mapM (Manual.toHtml {opts.lift with headerLevel := 2} ctxt state)
      else pure .empty
    let pageContent ←
      if root then
        let subToc := (← part.subParts.mapM (toc 1 opts ctxt state)).map (·.html (some depth))
        let subTocHtml := if subToc.size > 0 then {{<ol class="section-toc">{{subToc}}</ol>}} else .empty
        pure {{<section>{{Html.titlePage titleHtml authors introHtml ++ contents}} {{subTocHtml}}</section>}}
      else
        let subToc := (← part.subParts.mapM (toc depth opts ctxt state)).map (·.html (some depth))
        let subTocHtml := if subToc.size > 0 then {{<ol class="section-toc">{{subToc}}</ol>}} else .empty
        pure {{<section><h1>{{titleHtml}}</h1> {{introHtml}} {{contents}} {{subTocHtml}}</section>}}
    let thisFile := part.metadata.bind (·.file) |>.getD (part.titleString.sluggify.toString)
    let dir := if root then dir else dir.join thisFile
    let pageTitle := if root then bookTitle else {{<a href="/">{{bookTitle}}</a>}}
    ensureDir dir
    IO.FS.withFile (dir.join "index.html") .write fun h => do
      h.putStrLn Html.doctype
      h.putStrLn (relativize ctxt.path <| Html.page bookContents part.titleString pageTitle pageContent state.extraCss state.extraJs (extraStylesheets := config.extraCss ++ state.extraCssFiles.toList.map ("/-verso-css/" ++ ·.1)) (extraJsFiles := config.extraJs.toArray ++ state.extraJsFiles.map ("/-verso-js/" ++ ·.1))).asString
    if depth > 0 then
      for p in part.subParts do
        let nextFile := p.metadata.bind (·.file) |>.getD (p.titleString.sluggify.toString)
        emitPart bookTitle authors bookContents opts {ctxt with path := ctxt.path.push nextFile} state false (depth - 1) dir p

  urlAttr (name : String) : Bool := name ∈ ["href", "src", "data", "poster"]
  rwAttr (attr : String × String) : ReaderT Path Id (String × String) := do
    if urlAttr attr.fst && "/".isPrefixOf attr.snd then
      let path := (← read)
      pure { attr with
        snd := String.join (List.replicate path.size "../") ++ attr.snd.drop 1
      }
    else
      pure attr
  rwTag (tag : String) (attrs : Array (String × String)) (content : Html) : ReaderT Path Id (Option Html) := do
    pure <| some <| .tag tag (← attrs.mapM rwAttr) content
  relativize (path : Path) (html : Html) : Html :=
    html.visitM (m := ReaderT Path Id) (tag := rwTag) |>.run path


abbrev ExtraStep := TraverseContext → TraverseState → IO Unit


def manualMain (text : Part Manual)
    (extensionImpls : ExtensionImpls := by exact extension_impls%)
    (options : List String)
    (config : Config := {})
    (extraSteps : List ExtraStep := []) : IO UInt32 :=
  ReaderT.run go extensionImpls

where
  opts (cfg : Config)
    | ("--output"::dir::more) => opts {cfg with destination := dir} more
    | ("--depth"::n::more) => opts {cfg with htmlDepth := n.toNat!} more
    | ("--with-tex"::more) => opts {cfg with emitTeX := true} more
    | ("--without-tex"::more) => opts {cfg with emitTeX := false} more
    | ("--with-html-single"::more) => opts {cfg with emitHtmlSingle := true} more
    | ("--without-html-single"::more) => opts {cfg with emitHtmlSingle := false} more
    | ("--with-html-multi"::more) => opts {cfg with emitHtmlMulti := true} more
    | ("--without-html-multi"::more) => opts {cfg with emitHtmlMulti := false} more
    | (other :: _) => throw (↑ s!"Unknown option {other}")
    | [] => pure cfg

  go : ReaderT ExtensionImpls IO UInt32 := do
    let hasError ← IO.mkRef false
    let logError msg := do hasError.set true; IO.eprintln msg
    let cfg ← opts config options

    if cfg.emitTeX then emitTeX logError cfg text
    if cfg.emitHtmlSingle then emitHtmlSingle logError cfg text
    if cfg.emitHtmlMulti then emitHtmlMulti logError cfg text

    if (← hasError.get) then
      IO.eprintln "Errors were encountered!"
      return 1
    else
      return 0
