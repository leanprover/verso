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
  planFile : Option System.FilePath := none
  configFile : Option System.FilePath := none

def getConfig : List String → Except String Config
  | args => go args { inputDir := "", outputDir := "" }
where
  go : List String → Config → Except String Config
  | "--plan" :: file :: rest, cfg => go rest { cfg with planFile := some file }
  | "--config" :: file :: rest, cfg => go rest { cfg with configFile := some file }
  | [], cfg =>
    if cfg.inputDir.toString.isEmpty then
      throw s!"Didn't understand args: []. Expected INDIR OUTDIR [--plan FILE] [--config FILE]"
    else pure cfg
  | [i, o], cfg => pure { cfg with inputDir := i, outputDir := o }
  | i :: o :: rest, cfg =>
    if cfg.inputDir.toString.isEmpty then go rest { cfg with inputDir := i, outputDir := o }
    else throw s!"Didn't understand args: {i :: o :: rest}. Expected INDIR OUTDIR [--plan FILE] [--config FILE]"
  | other, _ => throw s!"Didn't understand args: {other}. Expected INDIR OUTDIR [--plan FILE] [--config FILE]"

/--
Checks if a `Code` item is a module docstring (modDoc or markdownModDoc).
-/
private def Code.isModDoc : Code → Bool
  | .modDoc _ => true
  | .markdownModDoc _ => true
  | _ => false

/--
Checks if a `Code` item is an import statement based on the module item's kind.
This is determined at the item level rather than the code level.
-/
private def ModuleItem'.isImport (item : ModuleItem') : Bool :=
  item.kind == ``Lean.Parser.Command.import

private def shouldShowDocstring (config : LiterateConfig) (declName : Name) : Bool :=
  if config.showDocstrings then
    !config.hideDocstringsFor.contains declName
  else
    config.showDocstringsFor.contains declName

namespace VersoLiterateCode

/-- Collect all module names in a Dir tree. -/
partial def Dir.allModuleNames (dir : Dir) (prefix_ : Name := .anonymous) : Array Name := Id.run do
  let mut result := #[]
  if let some m := dir.mod then
    result := result.push m.name
  for (n, child) in dir.children do
    result := result ++ child.allModuleNames (prefix_ ++ n)
  return result

/-- Filter a Dir to only include modules in the given name set.
    Intermediate namespace nodes are kept if they have descendants in the set. -/
partial def Dir.filter (names : Std.HashSet Name) (dir : Dir) : Dir :=
  let mod := dir.mod.bind fun m => if names.contains m.name then some m else none
  let children := dir.children.filterMap fun (n, child) =>
    let child' := child.filter names
    if child'.mod.isSome || !child'.children.isEmpty then
      some (n, child')
    else
      none
  { mod, children }

/-- Remove modules matching any excluded prefix and their children. -/
partial def Dir.applyExcludes (excludes : Array Name) (dir : Dir) (prefix_ : Name := .anonymous) : Dir :=
  let mod := dir.mod.bind fun m =>
    if excludes.any fun e => e == m.name || Name.isPrefixOf e m.name then none else some m
  let children := dir.children.filterMap fun (n, child) =>
    let fullName := prefix_ ++ n
    if excludes.any fun e => e == fullName || Name.isPrefixOf e fullName then
      none
    else
      let child' := child.applyExcludes excludes fullName
      if child'.mod.isSome || !child'.children.isEmpty then
        some (n, child')
      else
        none
  { mod, children }
where
  Name.isPrefixOf (prefix_ name : Name) : Bool :=
    if prefix_ == name then true
    else match name with
    | .anonymous => false
    | .str parent _ => Name.isPrefixOf prefix_ parent
    | .num parent _ => Name.isPrefixOf prefix_ parent

/-- Apply ordering: ordered modules appear first (in listed order), then
    remaining modules alphabetically.
    `order` specifies the ordering of direct children of the Dir tree root.
    `orderChildren` specifies the ordering of children of specific parent nodes. -/
partial def Dir.applyOrder (order : Array Name) (orderChildren : NameMap (Array Name))
    (dir : Dir) (prefix_ : Name := .anonymous) : Dir :=
  -- Determine the ordering for this level's children
  -- Check both `order` (for children whose full name matches) and `orderChildren` (for this prefix)
  let childOrder : Array Name :=
    -- First, get names from orderChildren for this specific prefix
    let fromOrderChildren := match orderChildren.find? prefix_ with
      | some o => o
      | none => #[]
    -- Then get names from `order` that are direct children of this prefix
    let fromOrder := order.filter fun name =>
      -- A name is a direct child if removing the last component gives us the prefix
      match name with
      | .str parent _ => parent == prefix_
      | _ => false
    -- Merge: orderChildren takes priority if both exist, otherwise use order
    if !fromOrderChildren.isEmpty then fromOrderChildren
    else fromOrder
  let children := if childOrder.isEmpty then
    -- Just sort alphabetically
    dir.children.qsort (fun c c' => c.1.toString < c'.1.toString)
  else
    -- Partition: ordered first, then alphabetical remainder
    let ordered := childOrder.filterMap fun name =>
      -- The name in the order array is the full name; we need the last component
      let lastComponent := name.components.getLast!
      dir.children.find? (·.1 == lastComponent)
    let unordered := dir.children.filter fun (n, _) =>
      !childOrder.any fun name => name.components.getLast! == n
    let unordered := unordered.qsort (fun c c' => c.1.toString < c'.1.toString)
    ordered ++ unordered
  let children := children.map fun (n, child) =>
    (n, child.applyOrder order orderChildren (prefix_ ++ n))
  { dir with children }

/-- Find a module by name in the Dir tree. -/
partial def Dir.findMod? (dir : Dir) (name : Name) : Option LitMod := do
  if let some m := dir.mod then
    if m.name == name then return m
  dir.children.findSome? fun (_, child) => child.findMod? name

end VersoLiterateCode

def literate.css := include_str "literate.css"

open Verso Output Doc Html in
def emitMod (root : Dir) (outDir: System.FilePath) (mod : LitMod) : EmitM Unit := do
  let components := mod.name.components
  let nesting := components.length

  let siteRoot := if nesting = 0 then "./" else nesting.fold (init := "") fun _ _ s => s ++ "../"

  let htmlId? := (← read).moduleIds.find? mod.name

  -- Build imports list
  let imports := mod.contents.filter ModuleItem'.isImport
  let importNames := imports.flatMap (·.defines)

  let litConfig := (← read).litConfig

  let ctx := { (← read) with
               options := {logError}
               traverseContext := {currentModule := mod.name}
               codeOptions := {} }

  -- Apply hide_commands filtering
  let contents := if litConfig.hideCommands.isEmpty then mod.contents
    else mod.contents.filter fun item =>
      !litConfig.hideCommands.contains item.kind

  -- Group items: modDoc items become prose, others go in code boxes
  let mut body : Html := .empty

  -- Imports section (collapsible)
  if !importNames.isEmpty then
    let importLinks := importNames.map fun n =>
      if (root[n]?).isSome then
        let href := n.components.map (toString · ++ "/") |> String.join
        {{<li><a href={{href}}>{{n.toString}}</a></li>}}
      else
        {{<li>{{n.toString}}</li>}}
    body := body ++ {{
      <details class="imports-list">
        <summary>"Imports"</summary>
        <ul>{{importLinks}}</ul>
      </details>
    }}

  -- Process items: prose (modDoc) flows between code boxes
  let mut currentCodeItems : Array (Nat × ModuleItem') := #[]

  for h : itemIdx in [0:contents.size] do
    have : itemIdx < contents.size := by have := h.2.1; grind
    let item := contents[itemIdx]
    -- Apply docstring filtering
    let item :=
      if litConfig.showDocstrings && litConfig.hideDocstringsFor.isEmpty then item
      else { item with code := item.code.filter fun
        | .verso _ (some dn) _ | .markdown _ (some dn) _ =>
          shouldShowDocstring litConfig dn
        | _ => true }
    let hasModDoc := item.code.any Code.isModDoc
    if hasModDoc then
      -- Flush any accumulated code items first
      if !currentCodeItems.isEmpty then
        let (codeHtml, st) ← currentCodeItems.foldlM (init := (.empty, (← get).hlState)) fun (html, st) (idx, cItem) => do
          let (h, st') ← renderCode idx cItem |>.run ctx st
          pure (html ++ h, st')
        modify (fun s => { s with hlState := st })
        body := body ++ {{<div class="code-box">{{codeHtml}}</div>}}
        currentCodeItems := #[]
      -- Render this item's code — modDoc parts render as prose, rest as inline code
      let (itemHtml, st) ← renderCode itemIdx item |>.run ctx (← get).hlState
      modify (fun s => { s with hlState := st })
      body := body ++ itemHtml
    else
      currentCodeItems := currentCodeItems.push (itemIdx, item)

  -- Flush remaining code items
  if !currentCodeItems.isEmpty then
    let (codeHtml, st) ← currentCodeItems.foldlM (init := (.empty, (← get).hlState)) fun (html, st) (idx, cItem) => do
      let (h, st') ← renderCode idx cItem |>.run ctx st
      pure (html ++ h, st')
    modify (fun s => { s with hlState := st })
    body := body ++ {{<div class="code-box">{{codeHtml}}</div>}}

  let faviconTag : Html := match litConfig.metadata.favicon with
    | some fav => {{<link rel="icon" href={{(System.FilePath.fileName fav).getD fav}}/>}}
    | none => {{<link rel="icon" href="data:,"/>}}
  let descTag : Html := match litConfig.metadata.description with
    | some desc => {{<meta name="description" content={{desc}}/>}}
    | none => .empty
  let extraCssTags : Html := litConfig.extraCss.foldl (init := .empty) fun acc css =>
    acc ++ {{<link rel="stylesheet" href={{(⟨css⟩ : System.FilePath).fileName.getD css}}/>}}
  let extraJsTags : Html := litConfig.extraJs.foldl (init := .empty) fun acc js =>
    acc ++ {{<script src={{(⟨js⟩ : System.FilePath).fileName.getD js}} defer="defer"></script>}}

  let headContents : Html := {{
    {{ faviconTag }}
    {{ descTag }}

    <script src="popper.js"></script>
    <script src="tippy.js"></script>
    <script>{{Html.text false highlightingJs}}</script>
    <style>{{Html.text false highlightingStyle}}</style>
    <link rel="stylesheet" href="tippy-border.css"/>
    <link rel="stylesheet" href="literate.css"/>
    <script src="copy-button.js" defer="defer"></script>

    <script src="-verso-search/elasticlunr.min.js"></script>
    <script src="-verso-search/fuzzysort.min.js"></script>
    <script src="-verso-search/searchIndex.js"></script>
    <script type="module" src="-verso-search/search-init.js"></script>
    <script src="-verso-search/domain-mappers.js" defer="defer"></script>
    <link rel="stylesheet" href="-verso-search/search-box.css"/>
    <link rel="stylesheet" href="-verso-search/search-highlight.css"/>
    <link rel="stylesheet" href="-verso-search/domain-display.css"/>
    <script src="-verso-search/search-highlight.js" defer="defer"></script>

    {{ extraCssTags }}
    {{ extraJsTags }}
  }}

  let pageTitle := match litConfig.metadata.title with
    | some siteTitle => s!"{mod.name} — {siteTitle}"
    | none => toString mod.name

  let pageHtml := page pageTitle siteRoot headContents mod.name root htmlId? body

  let outFile := mod.name.components.map (·.toString) |>.foldl (init := outDir) (· / ·)

  IO.FS.createDirAll outFile

  IO.FS.writeFile (outFile / "index.html") <| "<!DOCTYPE html>\n" ++ pageHtml.asString

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

open Verso Output Html in
partial def emitLandingPage (outDir : System.FilePath) (dir : Dir) (litConfig : LiterateConfig := {}) : IO Unit := do
  let faviconTag : Html := match litConfig.metadata.favicon with
    | some fav => {{<link rel="icon" href={{(System.FilePath.fileName fav).getD fav}}/>}}
    | none => {{<link rel="icon" href="data:,"/>}}
  let descTag : Html := match litConfig.metadata.description with
    | some desc => {{<meta name="description" content={{desc}}/>}}
    | none => .empty
  let extraCssTags : Html := litConfig.extraCss.foldl (init := .empty) fun acc css =>
    acc ++ {{<link rel="stylesheet" href={{(⟨css⟩ : System.FilePath).fileName.getD css}}/>}}
  let extraJsTags : Html := litConfig.extraJs.foldl (init := .empty) fun acc js =>
    acc ++ {{<script src={{(⟨js⟩ : System.FilePath).fileName.getD js}} defer="defer"></script>}}
  let headContents : Html := {{
    {{ faviconTag }}
    {{ descTag }}
    <link rel="stylesheet" href="literate.css"/>
    <script src="-verso-search/elasticlunr.min.js"></script>
    <script src="-verso-search/fuzzysort.min.js"></script>
    <script src="-verso-search/searchIndex.js"></script>
    <script type="module" src="-verso-search/search-init.js"></script>
    <script src="-verso-search/domain-mappers.js" defer="defer"></script>
    <link rel="stylesheet" href="-verso-search/search-box.css"/>
    <link rel="stylesheet" href="-verso-search/search-highlight.css"/>
    <link rel="stylesheet" href="-verso-search/domain-display.css"/>
    <script src="-verso-search/search-highlight.js" defer="defer"></script>
    {{ extraCssTags }}
    {{ extraJsTags }}
  }}
  let landingTitle := litConfig.metadata.title.getD "Module Index"
  let toc := buildToc dir
  let pageContents : Html := {{
    <html>
      <head>
        <meta charset="utf-8" />
        <meta name="viewport" content="width=device-width, initial-scale=1.0" />
        <title>{{landingTitle}}</title>
        {{ headContents }}
      </head>
      <body>
        <main class="landing-page" id="main-content">
          <h1>{{landingTitle}}</h1>
          {{ toc }}
        </main>
      </body>
    </html>
  }}
  IO.FS.writeFile (outDir / "index.html") <| "<!DOCTYPE html>\n" ++ pageContents.asString
where
  buildToc (dir : Dir) : Html :=
    if dir.children.isEmpty then .empty
    else {{<ul class="module-toc">{{dir.children.map fun (_, d) => tocEntry d}}</ul>}}
  tocEntry (dir : Dir) : Html :=
    let link : Html :=
      if let some m := dir.mod then
        let href := m.name.components.map (toString · ++ "/") |> String.join
        {{<a href={{href}}>{{m.name.toString}}</a>}}
      else
        -- namespace-only node (no module file)
        .empty
    let children := buildToc dir
    {{<li>{{link}}{{children}}</li>}}

section EmitLanding

open Verso Output Doc Html

/--
Emit the landing page using a specific module's rendered content.
The module still appears at its normal location; we just also render it as index.html.
-/
def emitLandingFromModule (outDir : System.FilePath) (root : Dir) (modName : Name) (ctx : HtmlContext) : IO Unit := do
  let litConfig := ctx.litConfig
  let some mod := root.findMod? modName
    | do IO.eprintln s!"Landing page module '{modName}' not found"; return
  let siteRoot := "./"
  let htmlId? := ctx.moduleIds.find? mod.name
  let imports := mod.contents.filter ModuleItem'.isImport
  let importNames := imports.flatMap (·.defines)
  let emitCtx := { ctx with
                   options := {logError := fun msg => IO.eprintln msg}
                   traverseContext := {currentModule := mod.name}
                   codeOptions := {} }
  let mut body : Html := .empty
  if !importNames.isEmpty then
    let importLinks := importNames.map fun n =>
      if (root[n]?).isSome then
        let href := n.components.map (toString · ++ "/") |> String.join
        {{<li><a href={{href}}>{{n.toString}}</a></li>}}
      else
        {{<li>{{n.toString}}</li>}}
    body := body ++ {{
      <details class="imports-list">
        <summary>"Imports"</summary>
        <ul>{{importLinks}}</ul>
      </details>
    }}
  -- Apply hide_commands filtering
  let modContents := if litConfig.hideCommands.isEmpty then mod.contents
    else mod.contents.filter fun item =>
      !litConfig.hideCommands.contains item.kind
  let mut currentCodeItems : Array (Nat × ModuleItem') := #[]
  let mut hlState : HtmlState := {}
  for h : itemIdx in [0:modContents.size] do
    have : itemIdx < modContents.size := by have := h.2.1; grind
    let item := modContents[itemIdx]
    -- Apply docstring filtering
    let item :=
      if litConfig.showDocstrings && litConfig.hideDocstringsFor.isEmpty then item
      else { item with code := item.code.filter fun
        | .verso _ (some dn) _ | .markdown _ (some dn) _ =>
          shouldShowDocstring litConfig dn
        | _ => true }
    let hasModDoc := item.code.any Code.isModDoc
    if hasModDoc then
      if !currentCodeItems.isEmpty then
        let (codeHtml, st) ← currentCodeItems.foldlM (init := (.empty, hlState.hlState)) fun (html, st) (idx, cItem) => do
          let (h, st') ← renderCode idx cItem |>.run emitCtx st
          pure (html ++ h, st')
        hlState := { hlState with hlState := st }
        body := body ++ {{<div class="code-box">{{codeHtml}}</div>}}
        currentCodeItems := #[]
      let (itemHtml, st) ← renderCode itemIdx item |>.run emitCtx hlState.hlState
      hlState := { hlState with hlState := st }
      body := body ++ itemHtml
    else
      currentCodeItems := currentCodeItems.push (itemIdx, item)
  if !currentCodeItems.isEmpty then
    let (codeHtml, st) ← currentCodeItems.foldlM (init := (.empty, hlState.hlState)) fun (html, st) (idx, cItem) => do
      let (h, st') ← renderCode idx cItem |>.run emitCtx st
      pure (html ++ h, st')
    hlState := { hlState with hlState := st }
    body := body ++ {{<div class="code-box">{{codeHtml}}</div>}}
  let faviconTag : Html := match litConfig.metadata.favicon with
    | some fav => {{<link rel="icon" href={{(System.FilePath.fileName fav).getD fav}}/>}}
    | none => {{<link rel="icon" href="data:,"/>}}
  let descTag : Html := match litConfig.metadata.description with
    | some desc => {{<meta name="description" content={{desc}}/>}}
    | none => .empty
  let extraCssTags : Html := litConfig.extraCss.foldl (init := .empty) fun acc css =>
    acc ++ {{<link rel="stylesheet" href={{(⟨css⟩ : System.FilePath).fileName.getD css}}/>}}
  let extraJsTags : Html := litConfig.extraJs.foldl (init := .empty) fun acc js =>
    acc ++ {{<script src={{(⟨js⟩ : System.FilePath).fileName.getD js}} defer="defer"></script>}}
  let headContents : Html := {{
    {{ faviconTag }}
    {{ descTag }}
    <script src="popper.js"></script>
    <script src="tippy.js"></script>
    <script>{{Html.text false highlightingJs}}</script>
    <style>{{Html.text false highlightingStyle}}</style>
    <link rel="stylesheet" href="tippy-border.css"/>
    <link rel="stylesheet" href="literate.css"/>
    <script src="copy-button.js" defer="defer"></script>
    <script src="-verso-search/elasticlunr.min.js"></script>
    <script src="-verso-search/fuzzysort.min.js"></script>
    <script src="-verso-search/searchIndex.js"></script>
    <script type="module" src="-verso-search/search-init.js"></script>
    <script src="-verso-search/domain-mappers.js" defer="defer"></script>
    <link rel="stylesheet" href="-verso-search/search-box.css"/>
    <link rel="stylesheet" href="-verso-search/search-highlight.css"/>
    <link rel="stylesheet" href="-verso-search/domain-display.css"/>
    <script src="-verso-search/search-highlight.js" defer="defer"></script>
    {{ extraCssTags }}
    {{ extraJsTags }}
  }}
  let landingPageTitle := match litConfig.metadata.title with
    | some siteTitle => s!"{mod.name} — {siteTitle}"
    | none => toString mod.name
  let pageHtml := page landingPageTitle siteRoot headContents mod.name root htmlId? body
  IO.FS.writeFile (outDir / "index.html") <| "<!DOCTYPE html>\n" ++ pageHtml.asString

end EmitLanding

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
  IO.FS.writeFile (config.outputDir / "literate.css") literate.css
  -- Copy the copy-button JS
  IO.FS.writeFile (config.outputDir / "copy-button.js") copyButtonJs
  emitSearchBox (config.outputDir / "-verso-search")
  let dir ← loadDir config.inputDir

  -- Load config from TOML if provided
  let litConfig ← match config.configFile with
    | some path => loadLiterateConfig path
    | none => pure ({} : LiterateConfig)

  -- Copy extra CSS files to output directory
  for css in litConfig.extraCss do
    let name := (⟨css⟩ : System.FilePath).fileName.getD css
    IO.FS.writeFile (config.outputDir / name) (← IO.FS.readFile css)
  -- Copy extra JS files to output directory
  for js in litConfig.extraJs do
    let name := (⟨js⟩ : System.FilePath).fileName.getD js
    IO.FS.writeFile (config.outputDir / name) (← IO.FS.readFile js)
  -- Copy favicon to output directory
  if let some favicon := litConfig.metadata.favicon then
    let name := (⟨favicon⟩ : System.FilePath).fileName.getD favicon
    IO.FS.writeFile (config.outputDir / name) (← IO.FS.readFile favicon)

  -- Filter by plan file if provided
  let dir ← match config.planFile with
    | some planPath => do
      if ← planPath.pathExists then
        let planContents ← IO.FS.readFile planPath
        let planNames := planContents.splitOn "\n"
          |>.filter (!·.isEmpty)
          |>.map String.toName
        let nameSet := Std.HashSet.ofList planNames
        pure <| dir.filter nameSet
      else pure dir
    | none => pure dir

  -- Apply nav tree transformations (exclude, then order)
  let dir := dir.applyExcludes litConfig.exclude
  let dir := dir.applyOrder litConfig.order litConfig.orderChildren

  let (dir, traverseState) ← traverse dir
  let ctx := {
    logError msg := errorCount.modify (· + 1) *> IO.eprintln msg
    definitionIds := traverseState.definitionIds
    linkTargets := traverseState.linkTargets
    moduleIds := traverseState.moduleIds
    traverseState
    litConfig
  }
  let ((), st) ← emitDir config.outputDir dir |>.run ctx |>.run {}

  -- Landing page: use configured module or auto-generated ToC
  match litConfig.landingPage with
  | some landingModName =>
    if let some _landingMod := dir.findMod? landingModName then
      -- Emit the landing module's content as index.html using the same page template
      emitLandingFromModule config.outputDir dir landingModName ctx
    else
      IO.eprintln s!"Warning: landing_page module '{landingModName}' not found, using default"
      emitLandingPage config.outputDir dir litConfig
  | none =>
    emitLandingPage config.outputDir dir litConfig

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
where
  copyButtonJs : String :=
    include_str "../../static-web/literate/copy-button.js"
