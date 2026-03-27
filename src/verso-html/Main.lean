/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import VersoLiterateCode

open Lean

open Verso.Output.Html
open Verso.Code

open VersoLiterate
open VersoLiterateCode
open Std

structure Config where
  inputDir : System.FilePath
  outputDir : System.FilePath

def getConfig (args : List String) : Except String Config :=
  match args with
  | [i, o] => pure { inputDir := i, outputDir := o }
  | _ => throw s!"Didn't understand args: {args}. Expected INDIR OUTDIR"

def code.css := include_str "code.css"

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

  let (results, st) ← mod.contents.mapIdxM (renderCode) |>.run ctx (← get).hlState
  -- Discard the accumulated headers because there's no local ToC here
  let body : Html := .seq (results.map (·.1))

  modify ({ · with hlState := st })
  let headContents : Html := {{
    <!-- Stop favicon requests -->
    <link rel="icon" href="data:," />

    <script src="popper.js"></script>
    <script src="tippy.js"></script>
    <script>{{Html.text false highlightingJs}}</script>
    <style>{{Html.text false highlightingStyle}}</style>
    <link rel="stylesheet" href="tippy-border.css"/>
    <link rel="stylesheet" href="code.css"/>

    <script src="-verso-search/elasticlunr.min.js"></script>
    <script src="-verso-search/fuzzysort.min.js"></script>
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
  let domainData : Verso.NameMap Verso.Multi.Domain := ({} : Verso.NameMap _)
    |>.insert constDomainName traverseState.constantDefDomain
    |>.insert moduleDomainName traverseState.moduleDomain
  IO.FS.writeFile (config.outputDir / "xref.json") <| Json.compress <| Verso.Multi.xrefJson domainData traverseState.allLinks
  IO.FS.writeFile (config.outputDir / "-verso-docs.json") st.hlState.dedup.docJson.compress
  let count ← errorCount.get
  if count > 0 then
    IO.eprintln s!"{count} errors occurred"
    return 1
  else return 0
