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
  outputDir : System.FilePath
  moduleMapFile : System.FilePath
  configFile : Option System.FilePath := none

def getConfig : List String → Except String Config
  | [outputDir, moduleMapFile] => pure { outputDir, moduleMapFile }
  | [outputDir, moduleMapFile, configFile] => pure { outputDir, moduleMapFile, configFile := some configFile }
  | _ => throw "Usage: verso-literate-html OUTDIR MODULE-MAP [CONFIG]"

/--
Whether a `Code` item is a module docstring (modDoc or markdownModDoc).
-/
private def Code.isModDoc : Code → Bool
  | .modDoc _ => true
  | .markdownModDoc _ => true
  | _ => false

/--
Whether a `Code` item is a declaration docstring (verso or markdown).
-/
private def Code.isDeclDoc : Code → Bool
  | .verso _ _ _ => true
  | .markdown _ _ _ => true
  | _ => false

/--
Whether a `Code` item is an import statement based on the module item's kind.
This is determined at the item level rather than the code level.
-/
private def ModuleItem'.isImport (item : ModuleItem') : Bool :=
  item.kind == ``Lean.Parser.Module.header

private def shouldShowDocstring (config : ResolvedConfig) (declName : Name) : Bool :=
  if config.showDocstrings then
    !config.hideDocstringsFor.contains declName
  else
    config.showDocstringsFor.contains declName

/-- Converts a theme key to a CSS custom property name: replace `_` with `-` and prepend `--verso-`. -/
private def themeKeyToCssVar (key : String) : String :=
  "--verso-" ++ key.map fun c => if c == '_' then '-' else c

/--
Generates the content of `literate-theme.css` from light and dark theme maps.
Returns `none` if both maps are empty (no file should be written).
-/
def generateThemeCss (light : Std.TreeMap String String compare) (dark : Std.TreeMap String String compare) : Option String :=
  if light.isEmpty && dark.isEmpty then none
  else
    let lightCss :=
      if light.isEmpty then ""
      else
        let vars := light.foldl (init := "") fun acc k v =>
          acc ++ s!"    {themeKeyToCssVar k}: {v};\n"
        s!":root \{\n{vars}}\n"
    let darkCss :=
      if dark.isEmpty then ""
      else
        let vars := dark.foldl (init := "") fun acc k v =>
          acc ++ s!"        {themeKeyToCssVar k}: {v};\n"
        let vars2 := dark.foldl (init := "") fun acc k v =>
          acc ++ s!"    {themeKeyToCssVar k}: {v};\n"
        s!"@media (prefers-color-scheme: dark) \{\n    :root \{\n{vars}    }\n}\n:root[data-theme=\"dark\"] \{\n{vars2}}\n"
    some (lightCss ++ darkCss)

namespace VersoLiterateCode

/-- Removes modules matching any excluded prefix and their children. -/
partial def Dir.applyExcludes (excludes : Array Name) (dir : Dir) (prefix_ : Name := .anonymous) : Dir :=
  let mod := dir.mod.bind fun m =>
    if excludes.any fun e => Name.isPrefixOf e m.name then none else some m
  let children := dir.children.filterMap fun (n, child) =>
    let fullName := prefix_ ++ n
    if excludes.any fun e => Name.isPrefixOf e fullName then
      none
    else
      let child' := child.applyExcludes excludes fullName
      if child'.mod.isSome || !child'.children.isEmpty then
        some (n, child')
      else
        none
  { mod, children }

/--
Applies ordering: ordered modules appear first (in listed order), then
remaining modules alphabetically.
`order` specifies the ordering of direct children of the Dir tree root.
`orderChildren` specifies the ordering of children of specific parent nodes.
-/
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
      let lastComponent := name.components.getLastD name
      dir.children.find? (·.1 == lastComponent)
    let unordered := dir.children.filter fun (n, _) =>
      !childOrder.any fun name => name.components.getLastD name == n
    let unordered := unordered.qsort (fun c c' => c.1.toString < c'.1.toString)
    ordered ++ unordered
  let children := children.map fun (n, child) =>
    (n, child.applyOrder order orderChildren (prefix_ ++ n))
  { dir with children }

/-- Finds a module by name in the Dir tree. -/
partial def Dir.findMod? (dir : Dir) (name : Name) : Option LitMod := do
  if let some m := dir.mod then
    if m.name == name then return m
  dir.children.findSome? fun (_, child) => child.findMod? name

end VersoLiterateCode

def literate.css := include_str "literate.css"

open Verso Output Html in
/-- Renders output messages for a list of code items, returning the combined HTML and updated state. -/
private def renderOutputMessages (items : Array (Nat × ModuleItem')) (showOutput : Array String)
    (hlCtx : HighlightHtmlM.Context Literate) (hlState : Hover.State Html) : Html × Hover.State Html :=
  items.foldl (init := (.empty, hlState)) fun (html, st) (_, cItem) =>
    let msgs := extractItemOutput cItem showOutput
    msgs.foldl (init := (html, st)) fun (html, st) msg =>
      let (msgHtml, st') := msg.blockHtml (g := Literate) (summarize := false) |>.run hlCtx |>.run st
      (html ++ msgHtml, st')

open Verso Output Html in
/--
Builds the `<head>` contents for a literate page. When `includeCodeAssets` is true,
includes popper/tippy/highlighting/copy-button assets needed for code hover tooltips.
-/
private def mkHeadContents (litConfig : LiterateConfig) (includeCodeAssets : Bool := true) : Html :=
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
  let hasThemeCss := !litConfig.theme.isEmpty || !litConfig.themeDark.isEmpty
  let themeCssTag : Html := if hasThemeCss then {{<link rel="stylesheet" href="literate-theme.css"/>}} else .empty
  let codeAssets : Html := if includeCodeAssets then {{
    <script src="popper.js"></script>
    <script src="tippy.js"></script>
    <script>{{Html.text false highlightingJs}}</script>
    <style>{{Html.text false highlightingStyle}}</style>
    <link rel="stylesheet" href="tippy-border.css"/>
  }} else .empty
  let copyButtonTag : Html := if includeCodeAssets then {{
    <script src="copy-button.js" defer="defer"></script>
  }} else .empty
  {{
    {{ faviconTag }}
    {{ descTag }}
    {{ codeAssets }}
    <link rel="stylesheet" href="literate.css"/>
    {{ themeCssTag }}
    {{ copyButtonTag }}
    <script src="-verso-search/elasticlunr.min.js"></script>
    <script src="-verso-search/fuzzysort.min.js"></script>
    <script src="-verso-search/searchIndex.js"></script>
    <script type="module" src="-verso-search/search-init.js"></script>
    <link rel="stylesheet" href="-verso-search/search-box.css"/>
    <link rel="stylesheet" href="-verso-search/search-highlight.css"/>
    <link rel="stylesheet" href="-verso-search/domain-display.css"/>
    <script src="-verso-search/search-highlight.js" defer="defer"></script>
    {{ extraCssTags }}
    {{ extraJsTags }}
  }}

open Verso Output Doc Html in
/--
Renders the body HTML for a module page: imports section, code boxes, and prose.
Returns the body HTML and updated highlight state.
-/
private def renderModBody (mod : LitMod) (resolved : ResolvedConfig)
    (ctx : HtmlContext) (initHlState : HtmlState) :
    IO (Html × HtmlState × Array (Nat × String × String)) := do
  let emitCtx := { ctx with
                   options := {logError := ctx.logError}
                   traverseContext := {currentModule := mod.name}
                   codeOptions := {} }
  let hlCtx : HighlightHtmlM.Context Literate :=
    ⟨emitCtx.linkTargets, emitCtx.traverseContext, emitCtx.definitionIds, emitCtx.codeOptions⟩

  -- Render a single code item and its output messages
  let renderCodeItemWithOutput (idx : Nat) (item : ModuleItem') (hlState : HtmlState) : IO (Html × HtmlState) := do
    let ((codeHtml, _, _), st) ← renderCode idx item |>.run emitCtx hlState.hlState
    let (outputHtml, st') := renderOutputMessages #[(idx, item)] resolved.showOutput hlCtx st
    return (codeHtml ++ outputHtml, { hlState with hlState := st' })

  -- Render accumulated code items into a code box
  let flushCodeItems (items : Array (Nat × ModuleItem')) (hlState : HtmlState) : IO (Html × HtmlState) := do
    if items.isEmpty then return (.empty, hlState)
    let mut boxHtml : Html := .empty
    let mut hlState := hlState
    for (idx, cItem) in items do
      let (itemHtml, hlState') ← renderCodeItemWithOutput idx cItem hlState
      hlState := hlState'
      boxHtml := boxHtml ++ itemHtml
    if boxHtml == .empty then return (.empty, hlState)
    return ({{<div class="code-box">{{boxHtml}}</div>}}, hlState)

  -- Filter docstrings based on resolved config
  let filterDocstrings (item : ModuleItem') : ModuleItem' :=
    if resolved.showDocstrings && resolved.hideDocstringsFor.isEmpty then item
    else { item with code := item.code.filter fun
      | .verso _ (some dn) _ | .markdown _ (some dn) _ =>
        shouldShowDocstring resolved dn
      | _ => true }

  -- Apply hide_commands filtering and remove import items (handled separately).
  -- Preserve original indices so that mod-doc anchor lookups (keyed by original item index) work.
  let contents := Id.run do
    let mut contents : Array (Nat × ModuleItem') := #[]
    for h : origIdx in 0...mod.contents.size do
      let item := mod.contents[origIdx]
      if !ModuleItem'.isImport item &&
         (resolved.hideCommands.isEmpty || !matchesAnyCommandPattern item resolved.hideCommands) then
        contents := contents.push (origIdx, item)
    pure contents

  let mut body : Html := .empty

  -- Collect import items into a collapsible section, rendered before other content
  let mut importHtml : Html := .empty
  let mut importHlState := initHlState
  for h : itemIdx in 0...mod.contents.size do
    let item := mod.contents[itemIdx]
    if ModuleItem'.isImport item then
      let ((codeHtml, _, _), st) ← renderCode itemIdx item |>.run emitCtx importHlState.hlState
      importHlState := { importHlState with hlState := st }
      importHtml := importHtml ++ codeHtml
  if resolved.showImports && importHtml != .empty then
    body := body ++ {{
      <details class="imports-list">
        <summary>"Imports"</summary>
        <div class="imports-code">{{importHtml}}</div>
      </details>
    }}

  -- Process items: prose (modDoc) flows between code boxes
  let mut currentCodeItems : Array (Nat × ModuleItem') := #[]
  let mut hlState := importHlState
  let mut allHeadings : Array (Nat × String × String) := #[]
  let mut usedIds := ctx.traverseState.usedHtmlIds
  for (origIdx, item) in contents do
    let item := filterDocstrings item
    let hasModDoc := item.code.any Code.isModDoc
    let hasDeclDocAsText := resolved.docstringsAsText && item.code.any Code.isDeclDoc
    if hasModDoc then
      -- Flush accumulated code items, then render modDoc as prose
      let (flushHtml, hlState') ← flushCodeItems currentCodeItems hlState
      hlState := hlState'
      body := body ++ flushHtml
      currentCodeItems := #[]
      let ((itemHtml, hdgs, usedIds'), st) ← renderCode origIdx item (usedHtmlIds := usedIds) |>.run emitCtx hlState.hlState
      hlState := { hlState with hlState := st }
      usedIds := usedIds'
      allHeadings := allHeadings ++ hdgs
      body := body ++ itemHtml
    else if hasDeclDocAsText then
      -- Flush accumulated code items, then split docstrings from code
      let (flushHtml, hlState') ← flushCodeItems currentCodeItems hlState
      hlState := hlState'
      body := body ++ flushHtml
      currentCodeItems := #[]
      let docItem := { item with code := item.code.filter Code.isDeclDoc }
      let remainingCode := (item.code.filter (!Code.isDeclDoc ·)).toList.dropWhile
        fun | .highlighted hl => newlinesOnly hl | _ => false
      let codeItem := { item with code := remainingCode.toArray }
      let ((docHtml, _), st) ← renderCode origIdx docItem (docstringsAsText := true) |>.run emitCtx hlState.hlState
      hlState := { hlState with hlState := st }
      body := body ++ docHtml
      let (codeBoxHtml, hlState') ← renderCodeItemWithOutput origIdx codeItem hlState
      hlState := hlState'
      unless codeBoxHtml == .empty do
        body := body ++ {{<div class="code-box">{{codeBoxHtml}}</div>}}
    else
      currentCodeItems := currentCodeItems.push (origIdx, item)

  -- Flush remaining code items
  let (flushHtml, hlState') ← flushCodeItems currentCodeItems hlState
  hlState := hlState'
  body := body ++ flushHtml
  return (body, hlState, allHeadings)

open Verso Output Doc Html in
def emitMod (root : Dir) (outDir: System.FilePath) (mod : LitMod)
    (srcDirs : Lean.NameMap System.FilePath := {}) : EmitM Unit := do
  -- Process images: copy files and rewrite URLs in content
  let mod ← match srcDirs.find? mod.name with
    | some srcDir => processModuleImages mod.name srcDir outDir mod
    | none => pure mod
  let htmlId? := (← read).moduleIds.find? mod.name
  let litConfig := (← read).litConfig
  let resolved := litConfig.resolveForModule mod.name
  let ctx := moduleContext mod.name litConfig

  let (body, hlState, headings) ← renderModBody mod resolved (← read) (← get)
  set hlState

  let headContents := mkHeadContents litConfig

  let tocHtml := if headings.size >= 2 then buildPageToc headings ctx.href else .empty

  let modLabel := resolved.title.getD (toString mod.name)
  let pageTitle := match litConfig.metadata.title with
    | some siteTitle => s!"{modLabel} — {siteTitle}"
    | none => modLabel

  let pageHtml := page pageTitle ctx.siteRoot headContents mod.name root htmlId? body (pageToc := tocHtml) (litConfig := litConfig)

  let outFile := ctx.outPath outDir

  IO.FS.createDirAll outFile

  IO.FS.writeFile (outFile / "index.html") <| "<!DOCTYPE html>\n" ++ pageHtml.asString

def emitDir (outDir : System.FilePath) (dir : Dir)
    (srcDirs : Lean.NameMap System.FilePath := {}) : EmitM Unit := do
  let root := dir
  let mut todo := [dir]
  repeat
    match todo with
    | [] => break
    | d :: ds =>
      todo := ds
      if let some m := d.mod then
        emitMod root outDir m srcDirs
      for c in d.children do
        todo := c.2 :: todo

open Verso Output Html in
partial def emitLandingPage (outDir : System.FilePath) (dir : Dir) (litConfig : LiterateConfig := {}) : IO Unit := do
  let headContents := mkHeadContents litConfig (includeCodeAssets := false)
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
        let ctx := moduleContext m.name litConfig
        {{<a href={{ctx.href}}>{{m.name.toString}}</a>}}
      else
        -- namespace-only node (no module file)
        .empty
    let children := buildToc dir
    {{<li>{{link}}{{children}}</li>}}

open Verso Output Doc Html in
/--
Emits the landing page using a specific module's rendered content.
The module still appears at its normal location; we just also render it as index.html.
-/
def emitLandingFromModule (outDir : System.FilePath) (root : Dir) (modName : Name)
    (ctx : HtmlContext) (initHlState : HtmlState := {})
    (srcDirs : Lean.NameMap System.FilePath := {}) : IO HtmlState := do
  let litConfig := ctx.litConfig
  let resolved := litConfig.resolveForModule modName
  let some mod := root.findMod? modName
    | throw <| .userError s!"Landing page module '{modName}' not found"
  -- Process images for landing page module
  let mod ← match srcDirs.find? mod.name with
    | some srcDir => processModuleImages mod.name srcDir outDir mod
    | none => pure mod
  let siteRoot := "./"
  let htmlId? := ctx.moduleIds.find? mod.name

  let (body, hlState, headings) ← renderModBody mod resolved ctx initHlState

  let headContents := mkHeadContents litConfig
  let tocHtml := if headings.size >= 2 then buildPageToc headings else .empty
  let modLabel := resolved.title.getD (toString mod.name)
  let landingPageTitle := match litConfig.metadata.title with
    | some siteTitle => s!"{modLabel} — {siteTitle}"
    | none => modLabel
  let pageHtml := page landingPageTitle siteRoot headContents mod.name root htmlId? body (pageToc := tocHtml) (litConfig := litConfig)
  IO.FS.writeFile (outDir / "index.html") <| "<!DOCTYPE html>\n" ++ pageHtml.asString
  return hlState

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
  let (dir, srcDirs) ← loadModuleMap config.moduleMapFile

  -- Load config from TOML if provided
  let litConfig ← match config.configFile with
    | some path => loadLiterateConfig path
    | none => pure ({} : LiterateConfig)

  -- Generate theme CSS file if theme overrides are present
  if let some themeCssContent := generateThemeCss litConfig.theme litConfig.themeDark then
    IO.FS.writeFile (config.outputDir / "literate-theme.css") themeCssContent

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

  -- Apply nav tree transformations (exclude, then order)
  let dir := dir.applyExcludes litConfig.exclude
  let dir := dir.applyOrder litConfig.order litConfig.orderChildren

  -- Validate: declarations in show_docstrings_for / hide_docstrings_for must exist
  if !litConfig.showDocstringsFor.isEmpty || !litConfig.hideDocstringsFor.isEmpty then
    let declNames := collectDeclNames dir
    for d in litConfig.showDocstringsFor do
      unless declNames.contains d do
        errorCount.modify (· + 1)
        IO.eprintln s!"Error: declaration '{d}' in show_docstrings_for does not exist"
    for d in litConfig.hideDocstringsFor do
      unless declNames.contains d do
        errorCount.modify (· + 1)
        IO.eprintln s!"Error: declaration '{d}' in hide_docstrings_for does not exist"

  let (dir, traverseState) ← traverse dir
  let ctx := {
    logError msg := errorCount.modify (· + 1) *> IO.eprintln msg
    definitionIds := traverseState.definitionIds
    linkTargets := traverseState.linkTargets
    moduleIds := traverseState.moduleIds
    traverseState
    litConfig
  }
  let ((), st) ← emitDir config.outputDir dir srcDirs |>.run ctx |>.run {}

  -- Landing page: use configured module or auto-generated ToC
  let st ← match litConfig.landingPage with
    | some landingModName =>
      emitLandingFromModule config.outputDir dir landingModName ctx st srcDirs
    | none =>
      emitLandingPage config.outputDir dir litConfig
      pure st

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
