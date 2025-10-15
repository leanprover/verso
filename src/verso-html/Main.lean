/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import Lean.Data.Json
import VersoLiterate
import Verso.Output.Html
import Verso.Output.Html.ElasticLunr
import Std.Data.HashMap
import Verso.FS
import VersoSearch

open Lean

open Verso.Output.Html
open Verso.Code

open VersoLiterate
open Std

structure Config where
  inputDir : System.FilePath
  outputDir : System.FilePath

def getConfig (args : List String) : Except String Config :=
  match args with
  | [i, o] => pure { inputDir := i, outputDir := o }
  | _ => throw s!"Didn't understand args: {args}. Expected INDIR OUTDIR"


structure HtmlContext where
  logError : String → IO Unit
  definitionIds : NameMap String
  moduleIds : NameMap String
  traverseState : Literate.TraverseState
  linkTargets : LinkTargets Literate.TraverseContext


open Verso.Output in
structure HtmlState where
  hlState : Hover.State Html := {}

abbrev EmitM := ReaderT HtmlContext (StateRefT HtmlState IO)

def logError (msg : String) : EmitM Unit := do
  (← read).logError msg

open Verso.Output Html in
open MD4Lean in
partial def md2Html (md : MD4Lean.Document) : Html := Id.run do
  let mut out := .empty
  for b in md.blocks do
    out := out ++ block b
  out

where
  block : MD4Lean.Block → Html
  | .p txt => {{<p>{{txt.map text}}</p>}}
  | .ul _ _ items => {{<ul>{{items.map fun ⟨_, _, _, txt⟩ => blocks txt}}</ul>}}
  | .ol _ _ _ items => {{<ol>{{items.map fun ⟨_, _, _, txt⟩ => blocks txt}}</ol>}}
  | .table hd rows =>
    {{<table>
        <thead><tr>{{hd.map fun h => {{<th>{{texts h}} </th>}} }}</tr></thead>
        <tbody>
          {{rows.map fun r => {{<tr>{{r.map fun c => {{<td>{{texts c}}</td>}} }}</tr>}} }}
        </tbody>
      </table>
    }}
  | .header n title => .tag s!"h{n + 1}" #[] <| texts title
  | .blockquote bs => {{<blockquote>{{blocks bs}}</blockquote>}}
  | .hr => {{<hr/>}}
  | .html xs => .text false (String.join xs.toList)
  | .code _ _ _ ss => {{<pre>{{String.join ss.toList}}</pre>}}


  blocks : Array MD4Lean.Block → Html
  | xs => xs.map block

  text : MD4Lean.Text → Html
  | .normal s => s
  | .a href title _ txt => {{<a href={{attr href}} title={{attr title}}>{{texts txt}}</a>}}
  | .nullchar => .empty
  | .em xs => {{<emph>{{texts xs}}</emph>}}
  | .strong xs => {{<strong>{{texts xs}}</strong>}}
  | .del xs => {{<del>{{texts xs}}</del>}}
  | .br _ => {{<br />}}
  | .softbr s => s
  | .code c => {{<code>{{String.join c.toList}}</code>}}
  | .img src title alt => {{<img src={{attr src}} title={{attr title}} alt={{String.join <| Array.toList <| alt.filterMap fun | .normal s => some s | _ => none}}/>}}
  | .u xs => texts xs -- TODO
  | .wikiLink _target txt => texts txt -- TODO
  | .entity x => .text false x
  | .latexMath _x => .empty -- TODO
  | .latexMathDisplay _x => .empty -- TODO

  texts : Array MD4Lean.Text → Html
  | xs => xs.map text

  attr xs := xs.map attrText |>.toList |> String.join

  attrText : MD4Lean.AttrText → String
  | .normal s => s
  | .nullchar => ""
  | .entity e => e

open MD4Lean in
/--
Constructs a string suitable for a full-text index.
-/
partial def mdIndex (md : MD4Lean.Document) : String := Id.run do
  let mut out := ""
  for b in md.blocks do
    out := out ++ block b
  out

where
  block : MD4Lean.Block → String
  | .p txt => texts txt
  | .ul _ _ items => "\n\n".intercalate <| Array.toList <| items.map fun ⟨_, _, _, txt⟩ => blocks txt
  | .ol _ _ _ items => "\n\n".intercalate <| Array.toList <| items.map fun ⟨_, _, _, txt⟩ => blocks txt
  | .table hd rows =>
    ((hd.map fun h => texts h).toList |> " | ".intercalate) ++
    ((rows.map fun r => r.map (fun c => texts c) |>.toList |> " | ".intercalate).toList |> "\n".intercalate)
  | .header n title => s!"#".pushn '#' n ++ " " ++ texts title ++ "\n\n"
  | .blockquote bs => bs.map block |>.map (s!"> {·}") |>.toList |> "\n\n".intercalate
  | .hr => ""
  | .html _ => ""
  | .code _ _ _ ss => String.join ss.toList

  blocks : Array MD4Lean.Block → String
  | xs => xs.map block |>.toList |> String.join

  text : MD4Lean.Text → String
  | .normal s => s
  | .a _href _title _ txt => texts txt
  | .nullchar => ""
  | .em xs | .strong xs | .del xs => texts xs
  | .br _ => "\n"
  | .softbr s => s
  | .code c => String.join c.toList
  | .img _src _title alt => texts alt
  | .u xs => texts xs
  | .wikiLink _target txt => texts txt
  | .entity _ => ""
  | .latexMath x => .join x.toList
  | .latexMathDisplay x => .join x.toList

  texts : Array MD4Lean.Text → String
  | xs => xs.map text |>.toList |> String.join

  attr : Array MD4Lean.AttrText → String
    | xs => xs.map attrText |>.toList |> String.join

  attrText : MD4Lean.AttrText → String
  | .normal s => s
  | .nullchar => ""
  | .entity e => e

private partial def newlinesOnly : SubVerso.Highlighting.Highlighted → Bool
  | .seq xs =>
    let nonEmpty := xs.filter (!·.isEmpty)
    nonEmpty.size > 0 && nonEmpty.all newlinesOnly
  | .text s => s.length > 0 && s.all (· == '\n')
  | .tactics _ _ _ hl | .span _ hl => newlinesOnly hl
  | .token .. | .unparsed .. | .point .. => false

open Verso.Output Html in
open Verso Doc Html in
open SubVerso.Highlighting in
def VersoLiterate.ModuleItem'.toHtml [Monad m] (itemIdx : Nat) (item : VersoLiterate.ModuleItem') : HtmlT Literate m Html := do
  let mut html := .empty
  let mut nextIndent := 0
  for c in item.code, idx in 0...* do
    match c with
    | .markdown i _ s =>
      html := html ++ {{<div class="md-text" style=s!"--indent: {i}">{{md2Html s}}</div>}}
    | .verso i _ x => do
      let text ←
        withReader (fun ρ => {ρ with codeOptions.identifierWordBreaks := true}) <|
        x.text.mapM Verso.Doc.Html.Block.toHtml
      let sub ←
        withReader (fun ρ => {ρ with codeOptions.identifierWordBreaks := true}) <|
        x.subsections.mapM Verso.Doc.Html.Part.toHtml
      html := html ++ {{ <div class="verso-text" style=s!"--indent: {i}">{{text ++ sub}}</div> }}
    | .highlighted hl =>
      if newlinesOnly hl then
        html := html ++ (← (Highlighted.text "\n").blockHtml (g := Literate) "lean" (trim := false))
        nextIndent := 0
      else
        let hl := trimLeading hl
        let (hl, i') := trimTrailing hl
        html := html ++ (← hl.blockHtml (g := Literate) "lean" (trim := false))
        nextIndent := i'
    | .modDoc doc =>
      let htmlId := (← read).traverseState.modDocLink (← read).traverseContext.currentModule itemIdx idx
      let text ←
        withReader (fun ρ => {ρ with codeOptions.identifierWordBreaks := true}) <|
        doc.text.mapM Verso.Doc.Html.Block.toHtml
      let sub ←
        withReader (fun ρ => {ρ with codeOptions.identifierWordBreaks := true}) <|
        doc.sections.mapM fun (lvl, p) =>
          withReader (fun ρ => {ρ with options.headerLevel := lvl + 1 }) <| Verso.Doc.Html.Part.toHtml p
      let idAttr := htmlId.map ("id", ·.htmlId.toString) |>.toArray
      html := html ++ {{ <div class="verso-text mod-doc" {{ idAttr }} style=s!"--indent: {nextIndent}">{{text ++ sub}}</div> }}
    | .markdownModDoc doc =>
      let htmlId := (← read).traverseState.modDocLink (← read).traverseContext.currentModule itemIdx idx
      let idAttr := htmlId.map ("id", ·.htmlId.toString) |>.toArray
      html := {{ <div class="md-text mod-doc" {{idAttr}}>{{md2Html doc}}</div>}}
  return html
where
  -- Trimming the leading newline is necessary because we display each section in HTML block mode,
  -- and we don't want to end up with an extra visual blank line between sections.
  trimLeading : SubVerso.Highlighting.Highlighted → SubVerso.Highlighting.Highlighted
    | hl =>
      if hl.toStringPrefix 1 |>.startsWith "\n" then
        hl.dropText 1
      else
        hl
  trimTrailing : SubVerso.Highlighting.Highlighted → (SubVerso.Highlighting.Highlighted × Nat)
    | hl =>
      let trailingIndent := hl.takeStringRightWhile (· == ' ')
      let hl := hl.dropTextRight trailingIndent.length
      if hl.toStringSuffix 1 |>.endsWith "\n" then
        (hl.dropTextRight 1, trailingIndent.length)
      else
        (hl.dropTextRight 1, 0)


structure Dir where
  mod : Option LitMod := none
  children : Array (Name × Dir) := #[]
deriving BEq

def Dir.get? (dir : Dir) (name : Name) : Option Dir := get' dir name.components
where
  get'
    | dir, [] => some dir
    | dir, c :: cs => do
      let d' ← dir.children.find? (·.1 == c)
      get' d'.2 cs

def Dir.Contains (dir : Dir) (name : Name) : Prop := dir.get? name |>.isSome

instance : GetElem? Dir Name Dir Dir.Contains where
  getElem dir name ok :=
    match h : dir.get? name with
    | some x => x
    | none => False.elim <| by
      simp_all [Dir.Contains]
  getElem? := Dir.get?

def Dir.insert (mod : LitMod) (dir : Dir) : Dir :=
  insert' mod.name.components dir
where
  insert' : List Name → Dir → Dir
  | [], d => { d with mod := some mod }
  | n :: ns, d =>
    let i := d.children.findIdx (·.1 == n)
    if _ : i < d.children.size then
      { d with children := d.children.set i (n, insert' ns d.children[i].2) }
    else
      { d with children := d.children.push (n, insert' ns {}) }

partial def Dir.sort (dir : Dir) : Dir :=
  { dir with
    children :=
      dir.children
        |>.map (fun (x, d) => (x, d.sort))
        |>.qsort (fun c c' => c.1.toString < c'.1.toString) }

/--
Recursively loads all the modules in the given directory.
-/
def loadDir (path : System.FilePath) : IO Dir := do
  let mut files := [path]
  let mut dir : Dir := {}
  repeat
    match files with
    | [] => break
    | f :: fs =>
      files := fs
      if ← f.isDir then
        files := ((← f.readDir).map (·.path)).toList ++ files
      else if f.extension == "json" then
        dir := dir.insert (← load f)
  return dir

partial def definitionIds (d : Dir) : NameMap (Name × String) := Id.run do
  let mut out := {}
  if let some m := d.mod then
    for item in m.contents do
      for x in item.code.flatMap (fun | .highlighted hl => hl.definedNames.toArray | _ => #[]) do
        out := out.insert x (m.name, x.toString)
  for c in d.children do
    out := out.mergeWith (fun _ _ x => x) (definitionIds c.2)
  return out

def code.css := include_str "code.css"

open Verso Output Html in
partial def page (title : String) (siteRoot : String) (headContents : Html) (current : Name) (root : Dir) (htmlId? : Option String) (code : Html) : Html := {{
  <html>
    <head>
      <meta charset="utf-8" />
      <meta name="viewport" content="width=device-width, initial-scale=1.0" />
      <base href={{siteRoot}}/>
      <title>{{title}}</title>
      {{ headContents }}
    </head>
    <body>
      <!-- Checkbox hack for hamburger menu -->
      <input type="checkbox" id="menu-toggle" class="menu-toggle" />

      <!-- Hamburger button -->
      <label for="menu-toggle" class="hamburger">
        <span></span>
        <span></span>
        <span></span>
      </label>
      <div class="layout">
        <!-- Sidebar -->
        <aside class="sidebar">
          <div class="sidebar-content">
            <nav class="module-tree">
              {{let curr := current.components
                root.children.map fun (x, d) =>
                  if let c :: cs := curr then
                    if x == c then
                      toNavigation (some cs) x d
                    else toNavigation none x d
                  else toNavigation none x d }}
              </nav>
          </div>
        </aside>

        <!-- Main content area -->
        <main class="main-area">
          <!-- Title bar with breadcrumbs -->
          <header class="title-bar">
            <ol class="breadcrumbs">
              <!--
              <li><a href="/">"root"</a></li>
              <li><a href="/utils">"utils"</a></li>
              <li><a href="/utils/string">"string"</a></li>
              <li><a href="/utils/string/validation">"validation"</a></li>
              <li><span class="current">"validation"</span></li> -->
              {{ breadcrumbs }}
            </ol>
          </header>

          <!-- Code content -->
          <section class="code-content" {{htmlId?.map ("id", ·) |>.toArray}}>
            {{code}}
          </section>
        </main>
      </div>
    </body>
  </html>
}}
where
  breadcrumbs := Id.run do
    let components := current.components
    if h : components = [] then return Html.empty
    else
      let mut breadcrumbs := .empty
      for h : i in [0:components.length - 1] do
        let addr := components.take (i+1) |>.map (·.toString) |> "/".intercalate
        have : i < components.length := by
          have := h.2.1
          grind
        breadcrumbs := breadcrumbs ++ {{<li><a href={{addr}}><code>{{toString components[i]}}</code></a></li>}}
      return breadcrumbs ++ {{<li><span class="current">{{toString <| components.getLast h}}</span></li>}}

  navLeaf (myName : Html) (current : Bool) : Html := {{<div class=s!"leaf{if current then " current" else ""}">{{myName}}</div>}}
  navNode (myName : Html) («open» : Bool) (current : Bool) (children : Array Html) : Html :=
    {{<details {{if «open» then #[("open", "")] else #[]}}><summary {{if current then #[("class", "current")] else #[]}}>{{myName}}</summary>{{children}}</details>}}

  toNavigation (current? : Option (List Name)) (name : Name) (dir : Dir) : Html :=
    let myName : Html :=
      let name := if let .str _ s := name then s else name.toString
      if let some x := dir.mod then {{
        <a href={{x.name.components.map (toString · ++ "/") |> String.join}} title={{x.name.toString}}>{{name}}</a>
      }} else name
    if dir.children.isEmpty then
      navLeaf myName (current? == some [])
    else
      if let some current := current? then
        match current with
        | [] =>
          navNode myName true true <| dir.children.map fun (x, d) => toNavigation none (name ++ x) d
        | c :: cs =>
          navNode myName true false <| dir.children.map fun (x, d) =>
            if c == x then
              toNavigation (some cs) (name ++ x) d
            else
              toNavigation none (name ++ x) d
      else navNode myName false false <| dir.children.map fun (x, d) => toNavigation none (name ++ x) d



open Verso Output Doc Html in
def emitMod (root : Dir) (outDir: System.FilePath) (mod : LitMod) : EmitM Unit := do
  let components := mod.name.components
  let nesting := components.length

  let siteRoot := if nesting = 0 then "./" else nesting.fold (init := "") fun _ _ s => s ++ "../"

  let mut breadcrumbs := Html.empty
  for h : i in [0:components.length - 1] do
    let addr := components.take (i+1) |>.map (·.toString) |> "/".intercalate
    have : i < components.length := by
      have := h.2.1
      grind
    breadcrumbs := {{<li><a href={{addr}}><code>{{toString components[i]}}</code></a></li>}} ++ breadcrumbs

  let htmlId? := (← read).moduleIds.find? mod.name

  let children : Array Html :=
    if let some d := root[mod.name]? then
      d.children.map fun (c : Name × Dir) =>
        {{<li><a href={{(components.map toString |> "/".intercalate) ++ "/" ++ toString c.1}}>{{mod.name ++ c.1 |> toString}}</a></li>}}
    else #[]

  let ctx := { (← read) with
               options := {logError}
               traverseContext := {currentModule := mod.name}
               codeOptions := {} }

  let (body, st) ← mod.contents.mapIdxM (ModuleItem'.toHtml) |>.run ctx (← get).hlState

  modify (fun s => { s with hlState := st })
  let headContents : Html := {{
    <!-- Stop favicon requests -->
    <link rel="icon" href="data:," />

    <script src="popper.js"></script>
    <script src="tippy.js"></script>
    <script>{{Html.text false highlightingJs}}</script>
    <style>{{Html.text false highlightingStyle}}</style>
    <script>s!"const __versoSiteRoot = {siteRoot.quote};"</script>
    <link rel="stylesheet" href="tippy-border.css"/>
    <link rel="stylesheet" href="code.css"/>

    <script src="-verso-search/elasticlunr.min.js"></script>
    <script src="-verso-search/fuzzysort.js"></script>
    <script src="-verso-search/searchIndex.js"></script>
    <script type="module" src="-verso-search/search-init.js"></script>
    <link rel="stylesheet" href="-verso-search/search-box.css"/>
    <link rel="stylesheet" href="-verso-search/search-highlight.css"/>
    <link rel="stylesheet" href="-verso-search/domain-display.css"/>
    <script src="-verso-search/search-highlight.js" defer="defer"></script>
  }}

  let contents := page (toString mod.name) siteRoot headContents mod.name root htmlId? body

  let outFile := mod.name.components.map (·.toString) |>.foldl (init := outDir) (· / ·)

  IO.FS.createDirAll outFile

  IO.FS.writeFile (outFile / "index.html") <| "<!DOCTYPE html>\n" ++ contents.asString

def emitDir (outDir : System.FilePath) (dir : Dir) : EmitM Unit := do
  let root := dir
  let mut todo := [dir]
  repeat
    match todo with
    | [] => break
    | d :: ds =>
      todo := ds
      if let some m := d.mod then
        emitMod root outDir m
      for c in d.children do
        todo := c.2 :: todo

partial def traverse1 (dir : Dir) : TraverseM Dir := do
  let mod ← dir.mod.mapM fun m => do
    discard <| saveModule m.name
    pure { m with
      contents :=
        ← m.contents.mapIdxM fun i item => do
          pure { item with
            code := ← item.code.mapIdxM fun j => fun
              | .markdown i declName? s => pure (.markdown i declName? s)
              | .verso i declName? v => do
                let text ← v.text.mapM Literate.traverseBlock
                let subsections ← v.subsections.mapM Literate.traversePart
                pure <| .verso i declName? { v with text, subsections }
              | .highlighted hl => do
                let defs := hl.definedNames
                for d in defs do
                  discard <| saveDef d
                pure (.highlighted hl)
              | .modDoc doc => do
                discard <| saveModDoc m.name i j
                let text ← doc.text.mapM Literate.traverseBlock
                let sections ← doc.sections.mapM fun (lvl, p) => do return (lvl, ← Literate.traversePart p)
                pure <| .modDoc { text, sections }
              | .markdownModDoc doc => do
                discard <| saveModDoc m.name i j
                pure (.markdownModDoc doc)
          }
      }
  let children ← dir.children.mapM fun (x, d) => do
    pure (x, ← withReader (fun ρ => { ρ with currentModule := ρ.currentModule ++ x }) <| traverse1 d)
  pure {dir with mod, children}

section
local instance {_ : BEq α} {_ : Hashable α} [BEq β] : BEq (HashMap α β) where
  beq x y :=
    x.size == y.size && x.fold (init := true) fun soFar k v => soFar && y[k]?.isEqSome v

local instance {_ : Ord α} : BEq (TreeSet α) where
  beq x y :=
    x.size == y.size && x.foldl (init := true) fun soFar v => soFar && y.contains v

local instance {_ : BEq α} {_ : Hashable α} : BEq (HashSet α) where
  beq x y :=
    x.size == y.size && x.fold (init := true) fun soFar v => soFar && y.contains v

local instance [BEq α] : BEq (NameMap α) where
  beq x y :=
    x.size == y.size && x.foldl (init := true) fun soFar k v => soFar && (y.find? k).isEqSome v

def reportHashSetDifferences [ToString α] [BEq α] [Hashable α] (a b : HashSet α) : String :=
  let removed := a.fold (init := []) fun soFar x =>
    if b.contains x then soFar else x :: soFar
  let added := b.fold (init := []) fun soFar x =>
    if a.contains x then soFar else x :: soFar
  (if added.isEmpty then "   * Nothing added." else s!"   * Added: {added.map toString |> ", ".intercalate }.") ++
  "\n" ++
  (if removed.isEmpty then "   * Nothing removed." else s!"   * Removed: {removed.map toString |> ", ".intercalate }.")

def reportDifferences (st1 st2 : State) : String :=
  let {htmlIds, usedInternalIds, usedHtmlIds, modDocs, moduleDomain, constantDefDomain} := st1
  let differingFields :=
    if st2.htmlIds != htmlIds then ["htmlIds"] else [] ++
    if st2.usedInternalIds != usedInternalIds then ["usedInternalIds"] else [] ++
    if st2.usedHtmlIds != usedHtmlIds then ["usedHtmlIds where:\n" ++ reportHashSetDifferences usedHtmlIds st2.usedHtmlIds] else [] ++
    if st2.modDocs != modDocs then ["modDocs"] else [] ++
    if st2.moduleDomain != moduleDomain then ["moduleDomain"] else [] ++
    if st2.constantDefDomain != constantDefDomain then ["constDefDomain"] else []
  "The following fields differ:\n" ++ "\n".intercalate (differingFields.map (s!" * {·}"))
end

def traverse (dir : Dir) (maxIterations : Nat := 10) : IO (Dir × State) := do
  let mut startState := {}
  let mut dir := dir
  for _ in [0:maxIterations-1] do
    let result ← traverse1 dir |>.run {} |>.run startState
    if dir == result.1 && startState == result.2 then return result
    dir := result.1
    startState := result.2
  -- The last iteration is partial here so we can have both states to give an error report
  let result ← traverse1 dir |>.run {} |>.run startState
  if startState == result.2 then return result
  dir := result.1

  throw <| .userError s!"Traversal made {maxIterations} iterations without terminating. {reportDifferences startState result.2}"


section
open Verso.Search

def constDomainName := `VersoHtml.constant
def moduleDomainName := `VersoHtml.module

def constMapper : DomainMapper where
  displayName := "Declaration"
  className := "const"
  quickJumpCss := "#search-wrapper .search-result.const :first-child { font-family: var(--verso-code-font-family); }"
  dataToSearchables :=
    "(domainData) =>
  Object.entries(domainData.contents).map(([key, value]) => ({
    searchKey: `${value[0].userName}`,
    address: `${value[0].address}#${value[0].id}`,
    domainId: '" ++ constDomainName.toString ++ "',
    ref: value,
  }))"

def moduleMapper : DomainMapper :=
  .withDefaultJs moduleDomainName "Module" "module"
    (css := "#search-wrapper .search-result.module :first-child { font-family: var(--verso-code-font-family); }")


def emitSearchBox (dir : System.FilePath) : IO Unit := do
  let domains : DomainMappers := .ofList [(constDomainName.toString, constMapper), (moduleDomainName.toString, moduleMapper)]
  Verso.FS.ensureDir dir
  for (file, contents) in searchBoxCode do
    IO.FS.writeBinFile (dir / file) contents
  IO.FS.writeFile (dir / "domain-mappers.js") (domains.toJs.pretty (width := 70))
  IO.FS.writeFile (dir / "domain-display.css") domains.quickJumpCss

/--
Adds a header to the current context and updates the traversal context.
-/
def IndexM.inDocstring (declName : Name) (act : IndexM Literate α) : IndexM Literate α := do
  let ctxHeader := declName.toString
  withReader (fun (iCtx, tCtx) => (iCtx.push ctxHeader, tCtx)) act


partial def mkIndex (traverseContext : Context) (traverseState : State) (dir : Dir) : Except String Index :=
  go dir |>.finalize traverseContext
where
  go (dir : Dir) : IndexM Literate Unit := do
    if let some m := dir.mod then
      for item in m.contents, itemIdx in 0...* do
        for c in item.code, codeIdx in 0...* do
          match c with
          | .highlighted .. => pure ()
          | .verso _ (some declName) xs =>
            if let some id := traverseState.constLink declName then
              let context ← IndexM.currentContext
              let content ← IndexM.inDocstring declName  do
                let content ← xs.text.foldlM (init := "") fun s b => do return s ++ (← blockText b) ++ "\n\n"
                xs.subsections.foldlM (init := content) fun s p' => do return s ++ (← partText p') ++ "\n\n"
              IndexM.save {id := id.link, header := declName.toString, context, content}
          | .verso .. => pure () -- Don't index things we can't link to anyway
          | .markdown _ (some declName) xs =>
            if let some id := traverseState.constLink declName then
              let context ← IndexM.currentContext
              IndexM.save {id := id.link, header := declName.toString, context, content := mdIndex xs}
          | .markdown .. => pure () -- Don't index things we can't link to anyway
          | .modDoc doc =>
            if let some id := traverseState.modDocLink m.name itemIdx codeIdx then
              let context ← IndexM.currentContext
              let content ← doc.text.foldlM (init := "") fun s b => do return s ++ (← blockText b) ++ "\n\n"
              let content ← doc.sections.foldlM (init := content) fun s (_lvl, p') => do
                let txt ← p'.content.foldlM (init := "") fun s b => do return s ++ (← blockText b) ++ "\n\n"
                -- No sub-parts in this representation
                return s ++ p'.titleString ++ "\n\n" ++ txt
              IndexM.save {id := id.link, header := m.name.toString, context, content}
          | .markdownModDoc doc =>
            if let some id := traverseState.modDocLink m.name itemIdx codeIdx then
              let context ← IndexM.currentContext
              IndexM.save {id := id.link, header := m.name.toString, context, content := mdIndex doc}
    for (_, ch) in dir.children do
      go ch

def emitIndex (traverseContext : Context) (traverseState : State) (dir : Dir) (outputDir : System.FilePath) (logError : String → IO Unit) : IO Unit := do
  match mkIndex traverseContext traverseState dir with
  | .error e =>
    logError e
  | .ok index =>
    -- Split the index into roughly 150k chunks for faster loading
    let (index, docs) := index.extractDocs
    let mut docBuckets : HashMap UInt8 (HashMap String Doc) := {}
    for (ref, content) in docs do
      let h := bucket ref
      docBuckets := docBuckets.alter h fun v =>
        v.getD {} |>.insert ref content

    for (bucket, docs) in docBuckets do
      let docJson := docs.fold (init := Json.mkObj []) fun json k v => json.setObjVal! k (v.foldr (init := Json.mkObj []) fun k v js => js.setObjVal! k (Json.str v))
      IO.FS.writeFile (outputDir / s!"searchIndex_{bucket}.js") s!"window.docContents[{bucket}].resolve({docJson.compress});"

    let indexJs := "const __verso_searchIndexData = " ++ index.toJson.compress ++ ";\n\n"
    let indexJs := indexJs ++ "const __versoSearchIndex = elasticlunr ? elasticlunr.Index.load(__verso_searchIndexData) : null;\n"
    let indexJs := indexJs ++ "window.docContents = {};\n"
    let indexJs := indexJs ++ "window.searchIndex = elasticlunr ? __versoSearchIndex : null;\n"
    IO.FS.writeFile (outputDir / "searchIndex.js") indexJs

    IO.FS.writeFile (outputDir / "elasticlunr.min.js") Verso.Output.Html.elasticlunr.js
where
  -- Not using a proper hash because this needs to be implemented identically in JS
  bucket (s : String) : UInt8 := Id.run do
    let mut hash := 0
    let mut n := 0
    while h : n < s.utf8ByteSize do
      hash := hash + s.getUtf8Byte ⟨n⟩ h
      n := n + 1
    return hash
end

def main (args : List String) : IO UInt32 := do
  let config ←
    match getConfig args with
    | .error e => throw <| .userError e
    | .ok v => pure v
  let errorCount ← IO.mkRef 0
  IO.FS.createDirAll config.outputDir
  IO.FS.writeFile (config.outputDir / "popper.js") Verso.Code.Highlighted.WebAssets.popper
  IO.FS.writeFile (config.outputDir / "tippy.js") Verso.Code.Highlighted.WebAssets.tippy
  IO.FS.writeFile (config.outputDir / "tippy-border.css") Verso.Code.Highlighted.WebAssets.tippy.border.css
  IO.FS.writeFile (config.outputDir / "code.css") code.css
  emitSearchBox (config.outputDir / "-verso-search")
  let dir ← loadDir config.inputDir
  let dir := dir.sort
  let (dir, traverseState) ← traverse dir
  let ctx := {
    logError msg := errorCount.modify (· + 1) *> IO.eprintln msg
    definitionIds := traverseState.definitionIds
    linkTargets := traverseState.linkTargets
    moduleIds := traverseState.moduleIds
    traverseState
  }
  let ((), st) ← emitDir config.outputDir dir |>.run ctx |>.run {}
  emitIndex {} traverseState dir (config.outputDir / "-verso-search") ctx.logError
  let domainData : NameMap Verso.Multi.Domain := ({} : NameMap _)
    |>.insert `VersoHtml.constant traverseState.constantDefDomain
    |>.insert `VersoHtml.module traverseState.moduleDomain
  IO.FS.writeFile (config.outputDir / "xref.json") <| Json.compress <| Verso.Multi.xrefJson domainData traverseState.allLinks
  IO.FS.writeFile (config.outputDir / "-verso-docs.json") st.hlState.dedup.docJson.compress
  let count ← errorCount.get
  if count > 0 then
    IO.eprintln s!"{count} errors occurred"
    return 1
  else return 0
