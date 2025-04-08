/-
Copyright (c) 2023-2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import SubVerso.Helper
import VersoBlog.Basic
import VersoBlog.LiterateLeanPage.Options
import MD4Lean


open Lean

open SubVerso.Highlighting
open SubVerso.Helper
open Verso.Doc.Concrete (stringToInlines)

namespace Verso.Genre.Blog.Literate

open System in
def loadModuleContent
    (leanProject : FilePath) (mod : String)
    (overrideToolchain : Option String := none) : IO (Array Json) := do

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
      "ELAN_TOOLCHAIN", "DYLD_LIBRARY_PATH", "LD_LIBRARY_PATH"]


  let json ← IO.FS.withTempFile fun h f => do
    let cmd := "elan"
    let args := #["run", "--install", toolchain, "lake", "exe", "subverso-extract-mod", mod, f.toString]

    let res ← IO.Process.output {
      cmd, args, cwd := projectDir
      -- Unset Lake's environment variables
      env := lakeVars.map (·, none)
    }
    if res.exitCode != 0 then
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
    h.rewind
    match Json.parse (← h.readToEnd) with
    | .error err =>
      throw <| .userError s!"Couldn't parse JSON from output file: {err}"
    | .ok val =>
      let .arr xs := val
        | throw <| .userError s!"Expected a JSON array as a result of module extraction but got:\n{val}"
      pure xs
  return json
where
  decorateOut (name : String) (out : String) : String :=
    if out.isEmpty then "" else s!"\n{name}:\n{out}\n"

structure Helper where
  highlight (term : String) (type? : Option String) : IO Highlighted

open System in
def Helper.fromModule
    (leanProject : FilePath) (mod : String)
    (overrideToolchain : Option String := none) : IO Helper := do

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
      "ELAN_TOOLCHAIN", "DYLD_LIBRARY_PATH", "LD_LIBRARY_PATH"]

  let cmd := "elan"
  let args := #["run", "--install", toolchain, "lake", "exe", "subverso-helper", mod]

  let hl ← do
    let (procIn, proc) ← do
      let proc ← IO.Process.spawn {
        cmd, args, cwd := projectDir
        -- Unset Lake's environment variables
        env := lakeVars.map (·, none)
        stdin := .piped
        stdout := .piped
        stderr := .inherit
      }
      proc.takeStdin
    let mutex ← Std.Mutex.new (IO.FS.Stream.ofHandle procIn, IO.FS.Stream.ofHandle proc.stdout)
    pure <| fun tm ty? => do
      mutex.atomically do
        let (procIn, procOut) ← get
        if let some code ← proc.tryWait then
          throw <| .userError s!"Process terminated: {code}"
        send procIn (Request.term tm ty?)
        match (← receiveThe Response procOut) with
        | some (.result (.highlighted hl)) => pure hl
        | some (.error code e more) =>
          let mut msg := s!"{e} ({code})."
          if let some details := more then
            msg := msg ++ s!" Details:\n  {details}"
          throw <| .userError msg
        | none => throw <| .userError "Helper process no longer running"

  return ⟨hl⟩
where
  decorateOut (name : String) (out : String) : String :=
    if out.isEmpty then "" else s!"\n{name}:\n{out}\n"



def loadLiteratePage (root : System.FilePath) (module : String) : IO (Array Json) := do
  let json ← loadModuleContent root module
  pure json

section
variable [Monad m] [MonadError m] [MonadQuotation m]


partial def getModuleDocString (hl : Highlighted) : m String := do
  let str := (← getString hl).trim
  let str := str.stripPrefix "/-!" |>.stripSuffix "-/" |>.trim
  pure str
where getString : Highlighted → m String
  | .text txt => pure txt
  | .tactics .. => throwError "Tactics found in module docstring!"
  | .point .. => pure ""
  | .span _ hl => getModuleDocString hl
  | .seq hls => do return (← hls.mapM getString).foldl (init := "") (· ++ ·)
  | .token ⟨_, txt⟩ => pure txt


open Verso Doc in
open Lean.Parser.Command in
open SubVerso.Highlighting in
def phrase (content : Json) : m (Name × Highlighted) := do
  let kind ←
    match content.getObjValAs? String "kind" with
    | .error e => throwError e
    | .ok v => pure (String.toName v)
  let code ←
    match content.getObjValAs? Highlighted "code" with
    | .error e => throwError e
    | .ok v => pure v
  return (kind, code)


end

def getFirstMessage : Highlighted → Option (Highlighted.Span.Kind × String)
  | .span msgs x =>
    msgs[0]? <|> getFirstMessage x
  | .point k m => pure (k, m)
  | .seq xs => do
    for x in xs do
      try
        return (← getFirstMessage x)
      catch
        | () => continue
    failure
  | .tactics _ _ _ x => getFirstMessage x
  | .text ..
  | .token .. => failure

open Verso Doc Elab PartElabM in
open Lean.Parser.Command in
partial def docFromMod (genre : Term) (project : System.FilePath) (mod : String) (content : Array Json) : PartElabM Unit := do
  let mut mdHeaders : Array Nat := #[]
  let helper ← Helper.fromModule project mod
  for cmd in content do
    let (kind, hl) ← phrase cmd
    match kind with
    | ``Lean.Parser.Module.header => pure ()
    | ``moduleDoc =>
      let str ← getModuleDocString hl
      let some ⟨mdBlocks⟩ := MD4Lean.parse str
        | throwError m!"Failed to parse Markdown: {str}"
      for b in mdBlocks do
        match b with
        | .header lvl txt =>
          let inlines ← txt.mapM (ofInline helper)

          if let some realLevel := mdHeaders.findRev? (· ≤ lvl) then
            closePartsUntil realLevel ⟨0⟩ -- TODO endPos
            mdHeaders := mdHeaders.take realLevel
          else
            mdHeaders := #[]

          -- The new header could be a sibling or a child. If this is true, it's a child:
          if !mdHeaders.back?.isEqSome lvl then
            mdHeaders := mdHeaders.push lvl

          push {
            titleSyntax := (← `(#[$inlines,*])),
            expandedTitle := some (txt.map inlineText |>.toList |> String.join, inlines),
            metadata := none,
            blocks := #[],
            priorParts := #[]
          }
        | other =>
          addBlock (← ofBlock helper other)
    | ``eval | ``evalBang | ``reduceCmd | ``print | ``printAxioms | ``printEqns | ``«where» | ``version | ``synth | ``check =>
      addBlock (← ``((Block.other (BlockExt.highlightedCode `name $(quote hl)) #[] : Block $genre)))
      if let some (k, msg) := getFirstMessage hl then
        let sev := match k with
          | .error => "error"
          | .info => "information"
          | .warning => "warning"
        addBlock (← ``(Block.other (Blog.BlockExt.htmlDiv $(quote sev)) #[Block.code $(quote msg)]))
    | _ =>
      addBlock (← ``((Block.other (BlockExt.highlightedCode `name $(quote hl)) #[] : Block $genre)))
  closePartsUntil 0 ⟨0⟩ -- TODO endPos?
where
  ofBlock (helper : Helper) : MD4Lean.Block → PartElabM Term
  | .header .. => throwError "Headers should be processed at the part level"
  | .p txt => do
    let inlines ← txt.mapM (ofInline helper)
    ``((Block.para #[$inlines,*] : Block $genre))
  | .ul _ _ lis => do
    ``(Doc.Block.ul #[$(← lis.mapM (ofLi helper)),*])
  | .ol _ start _ lis => do
    ``(Doc.Block.ol $(quote (start : Int)) #[$(← lis.mapM (ofLi helper)),*])
  | .code info lang _ strs => do
    let str := strs.toList |> String.join
    if info.isEmpty && lang.isEmpty then
      ``(Doc.Block.code $(quote str))
    else
      let msg : MessageData :=
        "Info and language information in code blocks is not supported:" ++
        indentD m!"info is {repr info} and language is {repr lang}"
      throwError msg
  | .blockquote bs => do
    ``(Doc.Block.blockquote #[$(← bs.mapM (ofBlock helper)),*])
  | b => throwError "Unsupported block {repr b}"

  ofLi (helper : Helper) : MD4Lean.Li MD4Lean.Block → PartElabM Term
  | {isTask, taskChar:=_, taskMarkOffset:=_, contents} => do
    if isTask then throwError "Tasks not supported"
    ``(Doc.ListItem.mk #[$(← contents.mapM (ofBlock helper)),*])

  ofInline (helper : Helper) : MD4Lean.Text → PartElabM Term
  | .normal str => ``(Inline.text $(quote str))
  | .nullchar => throwError "Unsupported null character in Markdown"
  | .softbr txt => ``(Inline.linebreak $(quote txt))
  | .a href _title _isAuto contents => do
    let href := (← href.mapM ofAttrText).toList |> String.join
    let contents ← contents.mapM (ofInline helper)
    ``(Inline.link #[$contents,*] $(quote href))
  | .code str => do
    let codeStr := String.join str.toList
    try
      let hl ← helper.highlight codeStr none
      ``((Inline.other (InlineExt.highlightedCode `name $(quote hl)) #[] : Inline $genre))
    catch
      | e =>
        if (← getLogInlines) then
          logInfo m!"Couldn't highlight '{codeStr}': {indentD e.toMessageData}"
        ``(Inline.code $(quote <| String.join str.toList))
  | .em txt => do ``(Inline.emph #[$(← txt.mapM (ofInline helper)),*])
  | .strong txt => do ``(Inline.strong #[$(← txt.mapM (ofInline helper)),*])
  | .img src _title alt => do
    let src := (← src.mapM ofAttrText).toList |> String.join
    let alt := (alt.map inlineText).toList |> String.join
    ``(Inline.image $(quote alt) $(quote src))
  | .latexMath strs =>
    let str := strs.toList |> String.join
    ``(Inline.math MathMode.inline $(quote str))
  | .latexMathDisplay strs =>
    let str := strs.toList |> String.join
    ``(Inline.math MathMode.display $(quote str))
  | other => throwError "Unimplemented {repr other}"

  inlineText : MD4Lean.Text → String
  | .normal str
  | .softbr str => str
  | .em xs
  | .strong xs
  | .a _ _ _ xs => xs.map inlineText |>.toList |> String.join
  | _ => ""

  ofAttrText : MD4Lean.AttrText → PartElabM String
  | .normal txt => pure txt
  | other => throwError "Unimplemented {repr other}"


open Verso Doc in
open Lean Elab Command in
open PartElabM in
def elabLiteratePage (x : Ident) (path : StrLit) (mod : Ident) (title : StrLit) (genre : Term) (metadata? : Option Term): CommandElabM Unit := do


  let titleParts ← stringToInlines title
  let titleString := inlinesToString (← getEnv) titleParts
  let initState : PartElabM.State := .init (.node .none nullKind titleParts)

  let jsons ← loadLiteratePage path.getString mod.getId.toString

  let ((), _st, st') ← liftTermElabM <| PartElabM.run {} initState <| do
    setTitle titleString (← liftDocElabM <| titleParts.mapM (elabInline ⟨·⟩))
    if let some metadata := metadata? then
      modifyThe PartElabM.State fun st => {st with partContext.metadata := some metadata}

    docFromMod genre path.getString mod.getId.toString jsons

  let finished := st'.partContext.toPartFrame.close 0
  let finished :=
    -- Obey the Markdown convention of a single top-level header being the title of the document, if it's been followed
    if let .mk _ _ _ meta #[] #[p] _ := finished then
      match p with
      | .mk t1 t2 t3 _ bs ps pos =>
        -- Propagate metadata fields
        FinishedPart.mk t1 t2 t3 meta bs ps pos
      | _ => p
    else finished

  elabCommand <| ← `(def $x : Part $genre := $(← finished.toSyntax genre st'.linkDefs st'.footnoteDefs))

end Literate
open Literate

open Lean.Parser (sepByIndent)
open Lean.Parser.Term
open Verso.Doc.Concrete

/--
Creates a page from a literate Lean module with Markdown module docstrings in it, performing a
best-effort conversion from a large subset of Markdown to Verso documents. Inline code elements are
elaborated as terms after the module itself; if they succeed, then they are highlighted as well. If
not, they become ordinary Markdown code.

Specifically, `def_literate_page PAGE from MOD in DIR as TITLE` defines a page `PAGE` by elaborating
the module `MOD` in the project directory `DIR` with title `TITLE`.

The literate Lean module does not need to use the same toolchain as Verso. `DIR` should be a project
directory that contains a toolchain file and a Lake configuration (`lakefile.toml` or
`lakefile.lean`), which should depend on the same version of SubVerso that Verso is using.

Set the option `verso.literateMarkdown.logInlines` to `true` to see the error messages that
prevented elaboration of inline elements.
-/
syntax "def_literate_page " ident " from " ident " in " str " as " str (" with " term)? : command
/--
Creates a post from a literate Lean module with Markdown module docstrings in it, performing a
best-effort conversion from a large subset of Markdown to Verso documents. Inline code elements are
elaborated as terms after the module itself; if they succeed, then they are highlighted as well. If
not, they become ordinary Markdown code.

Specifically, `def_literate_page POST from MOD in DIR as TITLE` defines a post `POST` by elaborating
the module `MOD` in the project directory `DIR` with title `TITLE`.

The literate Lean module does not need to use the same toolchain as Verso. `DIR` should be a project
directory that contains a toolchain file and a Lake configuration (`lakefile.toml` or
`lakefile.lean`), which should depend on the same version of SubVerso that Verso is using.

Set the option `verso.literateMarkdown.logInlines` to `true` to see the error messages that
prevented elaboration of inline elements.
-/
syntax "def_literate_post " ident " from " ident " in " str " as " str (" with " term)?: command


open Verso Doc in
open Lean Elab Command in
elab_rules : command
  | `(def_literate_page $x from $mod in $path as $title $[with $metadata]?) =>
    withScope (fun sc => {sc with opts := Elab.async.set sc.opts false}) do
      let genre ← `(Page)
      elabLiteratePage x path mod title genre metadata


open Verso Doc in
open Lean Elab Command in
elab_rules : command
  | `(def_literate_post $x from $mod in $path as $title $[with $metadata]?) =>
    withScope (fun sc => {sc with opts := Elab.async.set sc.opts false}) do
      let genre ← `(Post)
      elabLiteratePage x path mod title genre metadata
