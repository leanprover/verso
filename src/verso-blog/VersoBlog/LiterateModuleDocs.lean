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

open Verso Doc
open Lean

open SubVerso.Highlighting
open SubVerso.Helper
open SubVerso.Module
open Verso.Doc.Concrete (stringToInlines)

namespace Verso.Genre.Blog.Literate

open VersoLiterate

variable [bg : BlogGenre g]

partial def pushBlock (part : Part g) (block : Block g) : Part g :=
  if part.subParts.isEmpty then
    { part with content := part.content.push block }
  else
    { part with subParts := part.subParts.modify (part.subParts.size - 1) (pushBlock · block)}

def pushPart (parent child : Part g) : Part g :=
  { parent with subParts := parent.subParts.push child}

private def rwInline (rwI : Inline Literate → Inline g) : Literate.Inline → Array (Inline Literate) → Inline g
    | .highlighted hl, content =>
      .other (bg.inline_eq ▸ .highlightedCode { contextName := `lean } hl) <| content.map rwI
    | .data .., xs => .concat <| xs.map rwI

def inlineToWeb : Inline Literate → Inline g :=
  Inline.rewriteOther rwInline

def blockToWeb : Block Literate → Block g :=
  Block.rewriteOther rwInline fun _rwI rwB  => fun
    | .highlighted hl, content =>
      .other (bg.block_eq ▸ .highlightedCode { contextName := `lean } hl) <| content.map rwB
    | .data .., xs => .concat <| xs.map rwB

partial def partToWeb (p : Part Literate) : Part g :=
  let title := p.title.map inlineToWeb
  let content := p.content.map blockToWeb
  let subParts := p.subParts.map partToWeb
  {p with title, metadata := none, content, subParts}

private partial def attrText : MD4Lean.AttrText → String
  | .normal s => s
  | .nullchar => ""
  | .entity e => Output.Html.decodeEntity? e |>.getD e -- leave invalid entities alone

private partial def attr (str : Array MD4Lean.AttrText) : String :=
  str.map attrText |>.toList |> String.join

private partial def mdTextString : MD4Lean.Text → String
  | .normal s => s
  | .nullchar | .img .. | .latexMath .. | .latexMathDisplay .. | .br .. | .softbr .. =>  ""
  | .code s => s.toList |> String.join
  | .a _ _ _ txt | .em txt | .strong txt | .wikiLink _ txt | .u txt | .del txt => txt.map mdTextString |>.toList |> String.join
  | .entity e => Output.Html.decodeEntity? e |>.getD e -- leave invalid entities alone

private partial def mdText : MD4Lean.Text → Except String (Inline g)
  | .normal s => pure <| .text s
  | .nullchar => pure .empty
  | .softbr .. | .br .. => pure .empty
  | .a href _title _ txt => (.link · (attr href)) <$> txt.mapM mdText
  | .img src _title alt => pure <| .image (alt.map mdTextString |>.toList |> String.join) (attr src)
  | .em txt => .emph <$> txt.mapM mdText
  | .strong txt => .bold <$> txt.mapM mdText
  | .entity e => pure <| .text (Output.Html.decodeEntity? e |>.getD e) -- leave invalid entities alone
  | .code s => pure <| .code (s.toList |> String.join)
  | .latexMath s => pure <| .math .inline (s.toList |> String.join)
  | .latexMathDisplay s => pure <| .math .display (s.toList |> String.join)
  | .wikiLink .. => throw "Wiki-style links not supported"
  | .u .. => throw "Underline not supported"
  | .del .. => throw "Strikethrough not supported"

private partial def mdBlock : MD4Lean.Block → Except String (Block g)
  | .p xs => .para <$> xs.mapM mdText
  | .ul _ _ items => .ul <$> items.mapM fun ⟨_, _, _, content⟩ => (⟨·⟩) <$> content.mapM mdBlock
  | .ol _ n _ items => .ol n <$> items.mapM fun ⟨_, _, _, content⟩ => (⟨·⟩) <$> content.mapM mdBlock
  | .blockquote bs => .blockquote <$> bs.mapM mdBlock
  | .code _ _ _ s => pure <| .code <| String.join s.toList
  | .header .. => throw "Headers may not be nested under other blocks"
  | .table .. => throw "Markdown tables not supported"
  | .html .. => throw "Literal HTML in Markdown not supported"
  | .hr => throw "Thematic break (horizontal rule) in Markdown not supported"

open Code.External.ExternalCode in
partial def modToPage [bg : BlogGenre g] (mod : LitMod) (title : Array (Inline g)) (titleString : String) : Except String (Part g) := do
  let mut stack : Array (Part g) := #[]
  let mut p : Part g := {title, titleString, metadata := none, content := #[], subParts := #[]}

  let mut mdLevels := #[] -- Header nesting for legacy Markdown moduledocs

  for item in mod.contents do
    for c in item.code do
      match c with
      | .highlighted hl =>
        p := pushBlock p <| .other (bg.block_eq ▸ .highlightedCode { contextName := `lean } hl) #[]
      | .markdownModDoc doc =>
        for b in doc.blocks do
          match b with
          | .header lvl title =>
            dbg_trace "md section! {lvl} {repr title} {stack.size} {mdLevels}"
            let mdLevel := mdLevels.back? |>.getD 0
              let titleString := String.join <| Array.toList <| title.map mdTextString
              let title ← title.mapM mdText
              let newPart := {title, titleString, metadata := none, content := #[], subParts := #[]}

            if lvl > mdLevel then
              stack := stack.push p
              mdLevels := mdLevels.push lvl
              p := newPart
            else
              while h : stack.size > 0 ∧ mdLevels.size > 0 ∧ lvl < mdLevels.back?.getD 0 do
                let p' := stack.back
                stack := stack.pop
                mdLevels := mdLevels.pop
                p := pushPart p' p
              p := pushPart p newPart
          | other =>
            match mdBlock other with
            | .error e => throw e
            | .ok b' => p := pushBlock p b'
      | .modDoc doc =>
        dbg_trace "modDoc with {doc.text.size} blocks and {doc.sections.size} sections"
        dbg_trace "current is {p.titleString}"
        dbg_trace "stack is {stack.map (·.titleString)}"
        for b in doc.text do
          dbg_trace "block going into {p.titleString}"
          p := pushBlock p (blockToWeb b)
        for (lvl, sec) in doc.sections do
          dbg_trace "section! {lvl} {sec.titleString} {stack.size}"
          if lvl > stack.size then
            stack := stack.push p
            p := partToWeb sec
          else
            while h : lvl < stack.size do
              dbg_trace "Gonna pop {lvl} < {stack.size}"
              let p' := stack.back
              stack := stack.pop
              p := pushPart p' p
              dbg_trace "after pop, current is {p.titleString}"
            stack := stack.push p
            p := partToWeb sec
        dbg_trace "after current is {p.titleString}"
        dbg_trace "-------"
      | .verso i declName? docstring =>
        p := pushBlock p <| .other (bg.block_eq ▸ .docstring i declName?) <| docstringBlock docstring
      | .markdown i declName? docstring =>
        p := pushBlock p <| .other (bg.block_eq ▸ .docstring i declName?) (← mdDocstringBlock docstring.blocks)

  while h : stack.size > 0 do
    let p' := stack.back
    stack := stack.pop
    p := pushPart p' p
  return p
where
  docstringBlock (doc : LitVersoDocString) : Array (Block g) :=
    let parts := doc.subsections.map partToWeb
    doc.text.map blockToWeb ++ parts.map (docstringPart 0)
  docstringPart (lvl : Nat) (part : Part g) : Block g :=
    .other (bg.block_eq ▸ .docstringSection lvl) <|
      #[.para part.title] ++ part.content ++ part.subParts.map (docstringPart lvl)

  mdDocstringBlock (blocks : Array MD4Lean.Block) : Except String (Array (Block g)) := do
    let mut stack : Array (Nat × Array (Inline g) × Array (Block g)) := #[]
    let mut current := #[]
    for b in blocks do
      if let .header lvl title := b then
        let title ← title.mapM mdText
        let outerLvl := stack.back?.map (·.1) |>.getD 0
        while h : stack.size > 0 ∧ lvl ≤ (stack.back?.map (·.1) |>.getD 0) do
          let (lvl', title', current') := stack.back
          stack := stack.pop
          current := current'.push <| .other (bg.block_eq ▸ .docstringSection stack.size) <| #[.para title'] ++ current
        stack := stack.push (lvl, title, current)
        current := #[]
      else
        current := current.push (← mdBlock b)
    while h : stack.size > 0 do
      let (lvl', title', current') := stack.back
      stack := stack.pop
      current := current'.push <| .other (bg.block_eq ▸ .docstringSection stack.size) <| #[.para title'] ++ current
    return current

def modToPage! [BlogGenre g] (mod : LitMod) (title : Array (Inline g)) (titleString : String) : Part g :=
  match modToPage mod title titleString with
  | .error e => panic! s!"Couldn't load {titleString}: {e}"
  | .ok v => v

open System in
def loadModuleJson
    (leanProject : FilePath) (mod : String)
    (overrideToolchain : Option String := none) : IO String := do

  let projectDir := ((← IO.currentDir) / leanProject).normalize

  -- Validate that the path is really a Lean project
  let lakefile := projectDir / "lakefile.lean"
  let lakefile' := projectDir / "lakefile.toml"
  if !(← lakefile.pathExists) && !(← lakefile'.pathExists) then
    throw <| .userError s!"Neither {lakefile} nor {lakefile'} exist, couldn't load project"
  let toolchain ← match overrideToolchain with
    | none =>
      let toolchainfile := projectDir / "lean-toolchain"
      if !(← toolchainfile.pathExists) then
        throw <| .userError s!"File {toolchainfile} doesn't exist, couldn't load project"
      pure (← IO.FS.readFile toolchainfile).trim
    | some override => pure override

  -- Kludge: remove variables introduced by Lake. Clearing out DYLD_LIBRARY_PATH and
  -- LD_LIBRARY_PATH is useful so the version selected by Elan doesn't get the wrong shared
  -- libraries.
  let lakeVars :=
    #["LAKE", "LAKE_HOME", "LAKE_PKG_URL_MAP",
      "LEAN_SYSROOT", "LEAN_AR", "LEAN_PATH", "LEAN_SRC_PATH",
      "LEAN_GITHASH",
      "ELAN_TOOLCHAIN", "DYLD_LIBRARY_PATH", "LD_LIBRARY_PATH"]
  let cmd := "elan"
  let args := #["run", "--install", toolchain, "lake", "query", s!"+{mod}:literate"]
  let res ← IO.Process.output {
    cmd, args, cwd := projectDir
    -- Unset Lake's environment variables
    env := lakeVars.map (·, none)
  }
  if res.exitCode != 0 then reportFail projectDir cmd args res
  if let some f := res.stdout.split (· == '\n') |>.find? (!·.isEmpty) then
    IO.FS.readFile f
  else throw <| .userError s!"No result returned from build of {mod}"

where
  decorateOut (name : String) (out : String) : String :=
    if out.isEmpty then "" else s!"\n{name}:\n{out}\n"
  reportFail {α} (projectDir : FilePath) (cmd : String) (args : Array String) (res : IO.Process.Output) : IO α := do
    IO.eprintln <|
      "Build process failed." ++
      "\nCWD: " ++ projectDir.toString ++
      "\nCommand: " ++ cmd ++
      "\nArgs: " ++ repr args ++
      "\nExit code: " ++ toString res.exitCode ++
      "\nstdout: " ++ res.stdout ++
      "\nstderr: " ++ res.stderr

    throw <| .userError <|
      "Build process failed." ++
      decorateOut "stdout" res.stdout ++
      decorateOut "stderr" res.stderr




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

  let (titleTerm, _st) ← liftTermElabM <| DocElabM.run genre g {} initState <| do
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

  let mod ← runTermElabM fun _ => do
    let name ← mkFreshUserName (x.getId ++ `getPart)
    let title ← titleTerm.mapM (elabTerm · (some (.app (mkConst ``Verso.Doc.Inline) g)))
    let title ← Meta.mkArrayLit (.app (mkConst ``Verso.Doc.Inline) g) title.toList
    withOptions (Compiler.LCNF.compiler.extract_closed.set · false) do
      addAndCompile <| .defnDecl {
        name, levelParams := [], type := .app (mkConst ``Verso.Doc.Part) g,
        value := ← Meta.mkAppM ``modToPage! #[
          ← Meta.mkAppM ``VersoLiterate.loadJsonString! #[mkConst jsonName, mkStrLit s!"JSON for {x.getId}"],
          title,
          mkStrLit titleString
        ],
        hints := .regular 0, safety := .safe
      }
    pure name

  let metadata ← if let some m := metadata? then `(some $m) else `(none)
  elabCommand <| ← `(command|def $x : Part $genre := {$(mkIdent mod) with metadata := $metadata})


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

Specifically, `literate_page POST from MOD in DIR as TITLE` defines a post `POST` by elaborating the
module `MOD` in the project directory `DIR` with title `TITLE`.

`DIR` should be a project directory that contains a toolchain file and a Lake configuration
(`lakefile.toml` or `lakefile.lean`), which should depend on the same version of Verso that this
website is using.
-/
syntax "literate_page " ident optConfig " from " ident " in " str " as " str (" with " term)? : command
/--
Creates a post from a literate Lean module with Verso-based module docstrings in it. Markdown module
docstrings are supported, but no attempt is made to elaborate included code.

Specifically, `literate_post POST from MOD in DIR as TITLE` defines a post `POST` by elaborating the
module `MOD` in the project directory `DIR` with title `TITLE`.

`DIR` should be a project directory that contains a toolchain file and a Lake configuration
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
