/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import Lean.Data.Json
import VersoLiterate
import Verso.Doc.Html
import Verso.Output.Html
import Verso.Output.Html.ElasticLunr
import Std.Data.HashMap
import Verso.FS
import VersoSearch
import Verso.Code.External.Code

open Lean

open Verso.Output.Html
open Verso.Code

open VersoLiterate
open Std

namespace VersoLiterateCode

structure HtmlContext where
  logError : String → IO Unit
  definitionIds : NameMap String
  moduleIds : NameMap String
  traverseState : Literate.TraverseState
  linkTargets : LinkTargets Literate.TraverseContext
  litConfig : LiterateConfig := {}


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
  | .code _ _ _ ss => {{<pre><code>{{String.join ss.toList}}</code></pre>}}


  blocks : Array MD4Lean.Block → Html
  | xs => xs.map block

  text : MD4Lean.Text → Html
  | .normal s => s
  | .a href title _ txt => {{<a href={{attr href}} title={{attr title}}>{{texts txt}}</a>}}
  | .nullchar => .empty
  | .em xs => {{<em>{{texts xs}}</em>}}
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
  | .header n title => "".pushn '#' n ++ " " ++ texts title ++ "\n\n"
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

section ImageRewriting

/-- Whether a URL string is a relative path (not absolute and not a protocol URL). -/
private def isRelativeImagePath (url : String) : Bool :=
  !url.startsWith "/" && (url.splitOn "://").length <= 1

/-- Converts an MD4Lean `AttrText` array to a plain string. -/
private def attrTextToString (src : Array MD4Lean.AttrText) : String :=
  String.join (src.map (fun | .normal s => s | .entity e => e | .nullchar => "") |>.toList)

open MD4Lean in
/--
Rewrites image URLs in an MD4Lean document using the given function.
Only relative image paths are rewritten; absolute paths and protocol URLs are left as-is.
-/
partial def rewriteMdImageUrls (f : String → String) (doc : Document) : Document :=
  { doc with blocks := doc.blocks.map rewriteBlock }
where
  rewriteBlock : Block → Block
    | .p txt => .p (txt.map rewriteText)
    | .ul tight marker items => .ul tight marker (items.map fun ⟨c, m, s, bs⟩ => ⟨c, m, s, bs.map rewriteBlock⟩)
    | .ol tight marker start items => .ol tight marker start (items.map fun ⟨c, m, s, bs⟩ => ⟨c, m, s, bs.map rewriteBlock⟩)
    | .table hd rows => .table (hd.map (·.map rewriteText)) (rows.map (·.map (·.map rewriteText)))
    | .header n title => .header n (title.map rewriteText)
    | .blockquote bs => .blockquote (bs.map rewriteBlock)
    | b => b

  rewriteText : Text → Text
    | .img src title alt =>
      let s := attrTextToString src
      if isRelativeImagePath s then .img #[.normal (f s)] title alt
      else .img src title alt
    | .a href title checked xs => .a href title checked (xs.map rewriteText)
    | .em xs => .em (xs.map rewriteText)
    | .strong xs => .strong (xs.map rewriteText)
    | .del xs => .del (xs.map rewriteText)
    | .u xs => .u (xs.map rewriteText)
    | .wikiLink target xs => .wikiLink target (xs.map rewriteText)
    | t => t

open Lean.Doc in
/-- Rewrites image URLs in Verso inline content. -/
partial def rewriteVersoInlineImageUrls (f : String → String) : Inline Ext → Inline Ext
  | .image alt url => .image alt (if isRelativeImagePath url then f url else url)
  | .concat xs => .concat (xs.map (rewriteVersoInlineImageUrls f))
  | .emph xs => .emph (xs.map (rewriteVersoInlineImageUrls f))
  | .bold xs => .bold (xs.map (rewriteVersoInlineImageUrls f))
  | .link xs url => .link (xs.map (rewriteVersoInlineImageUrls f)) url
  | .footnote name xs => .footnote name (xs.map (rewriteVersoInlineImageUrls f))
  | .other ext xs => .other ext (xs.map (rewriteVersoInlineImageUrls f))
  | i => i

open Lean.Doc in
/-- Rewrites image URLs in a Verso block. -/
partial def rewriteVersoBlockImageUrls (f : String → String) : Block Ext Ext → Block Ext Ext
  | .para xs => .para (xs.map (rewriteVersoInlineImageUrls f))
  | .ul items => .ul (items.map fun i => ⟨i.contents.map (rewriteVersoBlockImageUrls f)⟩)
  | .ol start items => .ol start (items.map fun i => ⟨i.contents.map (rewriteVersoBlockImageUrls f)⟩)
  | .dl items => .dl (items.map fun i =>
      ⟨i.term.map (rewriteVersoInlineImageUrls f), i.desc.map (rewriteVersoBlockImageUrls f)⟩)
  | .blockquote xs => .blockquote (xs.map (rewriteVersoBlockImageUrls f))
  | .concat xs => .concat (xs.map (rewriteVersoBlockImageUrls f))
  | .other ext xs => .other ext (xs.map (rewriteVersoBlockImageUrls f))
  | b => b

open Lean.Doc in
/-- Rewrites image URLs in a Verso part. -/
partial def rewriteVersoPartImageUrls (f : String → String) (p : Part Ext Ext Empty) : Part Ext Ext Empty :=
  { p with
    title := p.title.map (rewriteVersoInlineImageUrls f)
    content := p.content.map (rewriteVersoBlockImageUrls f)
    subParts := p.subParts.map (rewriteVersoPartImageUrls f) }

/-- Rewrites image URLs in a single Code item. -/
def rewriteCodeImageUrls (f : String → String) : Code → Code
  | .markdown i d doc => .markdown i d (rewriteMdImageUrls f doc)
  | .markdownModDoc doc => .markdownModDoc (rewriteMdImageUrls f doc)
  | .verso i d doc => .verso i d {
      text := doc.text.map (rewriteVersoBlockImageUrls f)
      subsections := doc.subsections.map (rewriteVersoPartImageUrls f)
    }
  | .modDoc doc => .modDoc {
      text := doc.text.map (rewriteVersoBlockImageUrls f)
      sections := doc.sections.map fun (lvl, p) => (lvl, rewriteVersoPartImageUrls f p)
    }
  | c => c

/-- Rewrites image URLs in all content of a LitMod. -/
def rewriteModImageUrls (f : String → String) (mod : LitMod) : LitMod :=
  { mod with contents := mod.contents.map fun item =>
      { item with code := item.code.map (rewriteCodeImageUrls f) } }

/--
Computes the parent directory path from a module name's components.
E.g., `Foo.Bar.Baz` → `"Foo/Bar/"`, `Foo` → `""`.
-/
private def moduleParentPath (modName : Name) : String :=
  let components := modName.components.map toString
  match components.dropLast with
  | [] => ""
  | parents => "/".intercalate parents ++ "/"

/--
Processes images for a module: copies image files from source to output directory
and rewrites URLs in the module content.
Returns the modified `LitMod` with rewritten image URLs.
-/
def processModuleImages (modName : Name) (srcDir : System.FilePath) (outDir : System.FilePath)
    (mod : LitMod) : IO LitMod := do
  if mod.images.isEmpty then return mod
  let parentPath := moduleParentPath modName
  -- Copy each image and build the URL rewriting function
  for imgRef in mod.images do
    let libRelPath := (parentPath ++ imgRef : String)
    let srcPath := srcDir / libRelPath
    let destPath := outDir / "-verso-images" / libRelPath
    if ← srcPath.pathExists then
      if let some parent := destPath.parent then
        IO.FS.createDirAll parent
      let contents ← IO.FS.readBinFile srcPath
      IO.FS.writeBinFile destPath contents
    else
      IO.eprintln s!"Warning: image '{imgRef}' referenced in module '{modName}' not found at {srcPath}"
  -- Rewrite URLs in the module content
  let rewrite (imgRef : String) : String :=
    "-verso-images/" ++ parentPath ++ imgRef
  return rewriteModImageUrls rewrite mod

end ImageRewriting

partial def newlinesOnly : SubVerso.Highlighting.Highlighted → Bool
  | .seq xs =>
    let nonEmpty := xs.filter (!·.isEmpty)
    nonEmpty.size > 0 && nonEmpty.all newlinesOnly
  | .text s => s.length > 0 && s.all (· == '\n')
  | .tactics _ _ _ hl | .span _ hl => newlinesOnly hl
  | .token .. | .unparsed .. | .point .. => false

/--
Returns `true` when the highlighted code contains no non-whitespace characters, proof states, or
messages to show.
-/
partial def whitespaceOnly : SubVerso.Highlighting.Highlighted → Bool
  | .seq xs => xs.all whitespaceOnly
  | .text s => s.all Char.isWhitespace
  | .token ⟨_, s⟩ | .unparsed s => s.all Char.isWhitespace
  | .tactics data _ _ hl | .span data hl => data.isEmpty && whitespaceOnly hl
  | .point .. => false

open SubVerso.Highlighting in
/--
Removes leading text characters from highlighted code while `p` holds.
Stops at the first non-text content or the first character where `p` is false.
Analogous to `String.dropWhile` but for `Highlighted`.
-/
partial def _root_.SubVerso.Highlighting.Highlighted.dropTextWhile
    (p : Char → Bool) (hl : Highlighted) : Highlighted := Id.run do
  let mut todo := [hl]
  let mut out : Highlighted := Highlighted.seq #[]
  repeat
    match todo with
    | [] => break
    | h :: more =>
      match h with
      | Highlighted.seq xs =>
        todo := xs.toList ++ more
      | Highlighted.text s =>
        let remaining := s.dropWhile p |>.copy
        if remaining.isEmpty then
          todo := more
        else
          out := out ++ Highlighted.text remaining
          for hl' in more do out := out ++ hl'
          return out
      | Highlighted.unparsed s =>
        let remaining := s.dropWhile p |>.copy
        if remaining.isEmpty then
          todo := more
        else
          out := out ++ Highlighted.unparsed remaining
          for hl' in more do out := out ++ hl'
          return out
      | other =>
        out := out ++ other
        for hl' in more do out := out ++ hl'
        return out
  return out

open Verso.Output Html in
open Verso Doc Html in
open SubVerso.Highlighting in
def renderCode [Monad m] (itemIdx : Nat) (item : VersoLiterate.ModuleItem') (docstringsAsText : Bool := false) : HtmlT Literate m Html := do
  let mut html := .empty
  let mut nextIndent := 0
  let mut hasContent := false
  let docCls := if docstringsAsText then "mod-doc" else ""
  for c in item.code, idx in 0...* do
    match c with
    | .markdown i _ s =>
      html := html ++ {{<div class=s!"md-text {docCls}" style=s!"--indent: {i}">{{md2Html s}}</div>}}
      hasContent := true
    | .verso i _ x => do
      let text ←
        withReader (fun ρ => {ρ with codeOptions.identifierWordBreaks := true}) <|
        x.text.mapM fun b : Block Literate => ToHtml.toHtml b
      let sub ←
        withReader (fun ρ => {ρ with codeOptions.identifierWordBreaks := true}) <|
        x.subsections.mapM fun p : Part Literate => ToHtml.toHtml p
      html := html ++ {{ <div class=s!"verso-text {docCls}" style=s!"--indent: {i}">{{text ++ sub}}</div> }}
      hasContent := true
    | .highlighted hl =>
      if newlinesOnly hl then
        -- Skip leading newlines before any content has been rendered
        if hasContent then
          html := html ++ (← (Highlighted.text "\n").blockHtml (g := Literate) "lean" (trim := false))
        nextIndent := 0
      else if !whitespaceOnly hl then
        let hl := trimLeading hl
        let (hl, i') := trimTrailing hl
        html := html ++ (← hl.blockHtml (g := Literate) "lean" (trim := false))
        nextIndent := i'
        hasContent := true
    | .modDoc doc =>
      let htmlId := (← read).traverseState.modDocLink (← read).traverseContext.currentModule itemIdx idx
      let text ←
        withReader (fun ρ => {ρ with codeOptions.identifierWordBreaks := true}) <|
        doc.text.mapM fun b : Block Literate => ToHtml.toHtml b
      let sub ←
        withReader (fun ρ => {ρ with codeOptions.identifierWordBreaks := true}) <|
        doc.sections.mapM fun (lvl, p) =>
          withReader (fun ρ => {ρ with options.headerLevel := lvl + 1 }) <| ToHtml.toHtml (α := Part Literate) p
      let idAttr := htmlId.map ("id", ·.htmlId.toString) |>.toArray
      html := html ++ {{ <div class="verso-text mod-doc" {{ idAttr }} style=s!"--indent: {nextIndent}">{{text ++ sub}}</div> }}
    | .markdownModDoc doc =>
      let htmlId := (← read).traverseState.modDocLink (← read).traverseContext.currentModule itemIdx idx
      let idAttr := htmlId.map ("id", ·.htmlId.toString) |>.toArray
      html := html ++ {{ <div class="md-text mod-doc" {{idAttr}}>{{md2Html doc}}</div>}}
  return html
where
  -- Trimming the leading newline is necessary because we display each section in HTML block mode,
  -- and we don't want to end up with an extra visual blank line between sections.
  trimLeading (hl : SubVerso.Highlighting.Highlighted) : SubVerso.Highlighting.Highlighted :=
    hl.dropTextWhile (· == '\n')
  trimTrailing : SubVerso.Highlighting.Highlighted → (SubVerso.Highlighting.Highlighted × Nat)
    | hl =>
      let trailingIndent := hl.takeStringRightWhile (· == ' ')
      let hl := hl.dropTextRight trailingIndent.length
      if hl.toStringSuffix 1 |>.endsWith "\n" then
        (hl.dropTextRight 1, trailingIndent.length)
      else
        (hl, 0)


open SubVerso.Highlighting in
/--
Collects the leading keyword token strings from highlighted code, in order.
Stops at the first non-keyword, non-whitespace token. Whitespace (`.text`)
tokens are skipped. This gives us e.g. `#["#eval"]` or `#["#print", "axioms"]`
or `#["set_option"]` for the corresponding commands.
-/
partial def leadingKeywords (hl : Highlighted) : Array String :=
  go hl #[] |>.1
where
  /-- Returns `(keywords, done)` where `done` means we hit a non-keyword token. -/
  go : Highlighted → Array String → Array String × Bool
    | .token ⟨.keyword .., s⟩, acc => (acc.push s.trimAscii.toString, false)
    | .text s, acc =>
      if s.trimAscii.toString.isEmpty then (acc, false) -- skip whitespace
      else (acc, true) -- non-empty text that isn't a keyword: stop
    | .seq xs, acc =>
      xs.foldl (init := (acc, false)) fun (acc, done) x =>
        if done then (acc, true) else go x acc
    | .span _ content, acc => go content acc
    | .tactics _ _ _ content, acc => go content acc
    | _, acc => (acc, true) -- any other node type: stop

/--
Checks whether a module item's highlighted code starts with a given keyword
pattern. The pattern is a space-separated sequence of keyword tokens
(e.g. `"#eval"`, `"#print axioms"`, `"set_option"`). The item's leading
keyword tokens must start with the pattern tokens in order. This means
`"#eval"` matches both `#eval expr` and `#eval in`, and `"#print"` matches
both `#print name` and `#print axioms name`.
-/
def matchesCommandPattern (item : ModuleItem') (pattern : String) : Bool :=
  let patTokens := pattern.split (· == ' ') |>.filter (!·.isEmpty) |>.toArray
  if patTokens.isEmpty then false
  else
    let hls := item.code.filterMap fun | .highlighted hl => some hl | _ => none
    let hl := hls.foldl (init := SubVerso.Highlighting.Highlighted.seq #[]) fun acc h =>
      SubVerso.Highlighting.Highlighted.seq #[acc, h]
    let leadingKws := leadingKeywords hl
    if leadingKws.size < patTokens.size then false
    else
      let rec check (i : Nat) : Bool :=
        if i >= patTokens.size then true
        else if leadingKws[i]! != patTokens[i]! then false
        else check (i + 1)
      check 0

/-- Checks whether a module item matches any of the given command patterns. -/
def matchesAnyCommandPattern (item : ModuleItem') (patterns : Array String) : Bool :=
  patterns.any (matchesCommandPattern item)

open SubVerso.Highlighting in
/--
Extracts info-severity output messages from a module item, if the item's
leading keywords match any pattern in `showOutput`. Returns all info messages found.
-/
def extractItemOutput (item : ModuleItem') (showOutput : Array String) : Array Highlighted.Message :=
  if !matchesAnyCommandPattern item showOutput then #[]
  else
    let hls := item.code.filterMap fun | .highlighted hl => some hl | _ => none
    let hl := hls.foldl (init := Highlighted.seq #[]) fun acc h => Highlighted.seq #[acc, h]
    Verso.Code.External.allInfo hl |>.filterMap fun (msg, _) =>
      if msg.severity == .info then some msg else none

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

/--
Loads modules from a module-map file. Each line is either:
- `ModuleName\t/path/to/file.json\t/path/to/srcDir` (with source directory)
- `ModuleName\t/path/to/file.json` (without source directory, for backwards compatibility)

Returns the module directory tree and a mapping from module names to source directories.
-/
def loadModuleMap (moduleMapFile : System.FilePath) : IO (Dir × Lean.NameMap System.FilePath) := do
  let contents ← IO.FS.readFile moduleMapFile
  let mut dir : Dir := {}
  let mut srcDirs : Lean.NameMap System.FilePath := {}
  for line in contents.splitOn "\n" do
    if line.isEmpty then continue
    match line.splitOn "\t" with
    | [name, jsonPath, srcDir] =>
      let mod ← load jsonPath
      dir := dir.insert mod
      srcDirs := srcDirs.insert name.toName ⟨srcDir⟩
    | [_, jsonPath] =>
      dir := dir.insert (← load jsonPath)
    | _ => throw <| .userError s!"Invalid module-map line: {line}"
  return (dir, srcDirs)

partial def definitionIds (d : Dir) : NameMap (Name × String) := Id.run do
  let mut out := {}
  if let some m := d.mod then
    for item in m.contents do
      for x in item.code.flatMap (fun | .highlighted hl => hl.definedNames.toArray | _ => #[]) do
        out := out.insert x (m.name, x.toString)
  for c in d.children do
    out := out.mergeWith (fun _ _ x => x) (definitionIds c.2)
  return out

/--
Collects all declaration names from all modules in a Dir tree.
These are the names that appear in `Code.verso _ (some dn) _` and
`Code.markdown _ (some dn) _` patterns.
-/
partial def collectDeclNames (d : Dir) : Std.HashSet Name := Id.run do
  let mut out : Std.HashSet Name := {}
  if let some m := d.mod then
    for item in m.contents do
      for c in item.code do
        match c with
        | .verso _ (some dn) _ | .markdown _ (some dn) _ => out := out.insert dn
        | _ => pure ()
  for (_, child) in d.children do
    for x in collectDeclNames child do
      out := out.insert x
  return out

/--
Collects headings from a module's content items for the page table of contents.
Returns an array of `(level, titleText, htmlId?)` tuples.
-/
def collectHeadings (mod : LitMod) (traverseState : Literate.TraverseState) :
    Array (Nat × String × Option String) := Id.run do
  let mut headings : Array (Nat × String × Option String) := #[]
  for h_item : itemIdx in [0:mod.contents.size] do
    have : itemIdx < mod.contents.size := by have := h_item.2.1; grind
    let item := mod.contents[itemIdx]
    for h_code : codeIdx in [0:item.code.size] do
      have : codeIdx < item.code.size := by have := h_code.2.1; grind
      match item.code[codeIdx] with
      | .modDoc doc =>
        let htmlId := traverseState.modDocLink mod.name itemIdx codeIdx
        for (lvl, part) in doc.sections do
          headings := headings.push (lvl, part.titleString, htmlId.map (·.htmlId.toString))
      | .markdownModDoc doc =>
        let htmlId := traverseState.modDocLink mod.name itemIdx codeIdx
        for b in doc.blocks do
          match b with
          | .header n title =>
            let titleText := title.map mdHeaderText |>.toList |> String.join
            headings := headings.push (n, titleText, htmlId.map (·.htmlId.toString))
          | _ => pure ()
      | _ => pure ()
  return headings
where
  mdHeaderText : MD4Lean.Text → String
    | .normal s => s
    | .code s => s.toList |> String.join
    | .em xs | .strong xs | .del xs => xs.map mdHeaderText |>.toList |> String.join
    | .a _ _ _ txt => txt.map mdHeaderText |>.toList |> String.join
    | _ => ""

open Verso Output Html in
/--
Builds the page ToC HTML from collected headings.
`pageUrl` is the page's URL relative to the site root (e.g. `"LitConfig/"` or `"LitConfig/Core/"`),
needed because the `<base>` tag makes bare `#id` anchors resolve relative to the site root.
-/
def buildPageToc (headings : Array (Nat × String × Option String)) (pageUrl : String := "") : Html :=
  let items := headings.map fun (lvl, title, htmlId?) =>
    let levelClass := s!"toc-level-{lvl}"
    match htmlId? with
    | some id => {{<li class={{levelClass}}><a href={{s!"{pageUrl}#{id}"}}>{{title}}</a></li>}}
    | none => {{<li class={{levelClass}}>{{title}}</li>}}
  {{<nav class="page-toc" aria-label="Page table of contents">
      <div class="page-toc-title">"On this page"</div>
      <ul>{{items}}</ul>
    </nav>}}

open Verso Output Html in
partial def page (title : String) (siteRoot : String) (headContents : Html) (current : Name) (root : Dir) (htmlId? : Option String) (code : Html) (pageToc : Html := .empty) (litConfig : LiterateConfig := {}) : Html := {{
  <html>
    <head>
      <meta charset="utf-8" />
      <meta name="viewport" content="width=device-width, initial-scale=1.0" />
      <base href={{siteRoot}}/>
      <title>{{title}}</title>
      {{ headContents }}
    </head>
    <body>
      <a href="#main-content" class="skip-link">"Skip to content"</a>
      <!-- Checkbox hack for hamburger menu -->
      <input type="checkbox" id="menu-toggle" class="menu-toggle" role="button" aria-label="Menu" />

      <!-- Hamburger button -->
      <label for="menu-toggle" class="hamburger" aria-label="Toggle navigation">
        <span></span>
        <span></span>
        <span></span>
      </label>
      <div class="layout">
        <!-- Sidebar -->
        <aside class="sidebar">
          <div class="sidebar-content">
            <nav class="module-tree" aria-label="Module navigation">
              {{navTree current root litConfig}}
              </nav>
          </div>
        </aside>

        <!-- Main content area -->
        <main class="main-area" id="main-content">
          <!-- Title bar with breadcrumbs -->
          <header class="title-bar">
            <ol class="breadcrumbs" aria-label="Breadcrumb">
              {{ breadcrumbs }}
            </ol>
          </header>

          <!-- Content wrapper: code + page ToC -->
          <div class="content-wrapper">
            <!-- Code content -->
            <section class="code-content" {{htmlId?.map ("id", ·) |>.toArray}}>
              {{code}}
            </section>
            {{ pageToc }}
          </div>
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

  /--
  When there is exactly one top-level entry, render it as a non-collapsible title header
  with its children as top-level nav entries. Otherwise, render the normal tree.
  -/
  navTree (current : Name) (root : Dir) (litConfig : LiterateConfig) : Array Html :=
    let curr := current.components
    match root.children with
    | #[(rootName, rootDir)] =>
      -- Single root: render as title + flat children
      let rootLabel : Html :=
        if let some x := rootDir.mod then
          let resolved := litConfig.resolveForModule x.name
          let (label, hasCustomTitle) := match resolved.title with
            | some t => (t, true)
            | none => (if let .str _ s := rootName then s else rootName.toString, false)
          let href := match resolved.url with
            | some u => u ++ "/"
            | none => x.name.components.map (toString · ++ "/") |> String.join
          let cls := if hasCustomTitle then "custom-title" else ""
          {{<a href={{href}} title={{x.name.toString}} class={{cls}}>{{label}}</a>}}
        else
          let label := if let .str _ s := rootName then s else rootName.toString
          (label : Html)
      let childCurr := match curr with
        | c :: cs => if c == rootName then some cs else none
        | [] => none
      #[{{<div class=s!"nav-title{if childCurr == some [] then " current" else ""}">{{rootLabel}}</div>}}] ++
        rootDir.children.map fun (x, d) =>
          match childCurr with
          | some (c :: cs) =>
            if c == x then toNavigation (some cs) (rootName ++ x) d
            else toNavigation none (rootName ++ x) d
          | _ => toNavigation none (rootName ++ x) d
    | _ =>
      -- Multiple roots: normal tree rendering
      root.children.map fun (x, d) =>
        if let c :: cs := curr then
          if x == c then
            toNavigation (some cs) x d
          else toNavigation none x d
        else toNavigation none x d

  toNavigation (current? : Option (List Name)) (name : Name) (dir : Dir) : Html :=
    let myName : Html :=
      if let some x := dir.mod then
        let resolved := litConfig.resolveForModule x.name
        let (label, hasCustomTitle) := match resolved.title with
          | some t => (t, true)
          | none => (if let .str _ s := name then s else name.toString, false)
        let href := match resolved.url with
          | some u => u ++ "/"
          | none => x.name.components.map (toString · ++ "/") |> String.join
        let cls := if hasCustomTitle then "custom-title" else ""
        {{<a href={{href}} title={{x.name.toString}} class={{cls}}>{{label}}</a>}}
      else
        let label := if let .str _ s := name then s else name.toString
        (label : Html)
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
    (if st2.htmlIds != htmlIds then ["htmlIds"] else []) ++
    (if st2.usedInternalIds != usedInternalIds then ["usedInternalIds"] else []) ++
    (if st2.usedHtmlIds != usedHtmlIds then ["usedHtmlIds where:\n" ++ reportHashSetDifferences usedHtmlIds st2.usedHtmlIds] else []) ++
    (if st2.modDocs != modDocs then ["modDocs"] else []) ++
    (if st2.moduleDomain != moduleDomain then ["moduleDomain"] else []) ++
    (if st2.constantDefDomain != constantDefDomain then ["constDefDomain"] else [])
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
    searchKey: `${value[0].data.userName}`,
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
      hash := hash + s.getUTF8Byte ⟨n⟩ h
      n := n + 1
    return hash
