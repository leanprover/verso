/-
Copyright (c) 2024-2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import Lean.Elab.Command
import Lean.Elab.InfoTree

import Verso
import Verso.FS
import Verso.Doc.ArgParse
import Verso.Doc.Elab.Monad
import Verso.Code
import Verso.Instances

import SubVerso.Highlighting
import SubVerso.Examples

import VersoManual.InlineLean.Scopes
import VersoManual.InlineLean.IO.Context
import VersoManual.InlineLean.Block


open Lean Elab
open Verso ArgParse Doc Elab Genre.Manual Html Code Highlighted.WebAssets
open SubVerso.Highlighting Highlighted

open Lean.Elab.Tactic.GuardMsgs

open Lean.Elab.Term (mkFreshIdent)

open Verso.Genre.Manual.InlineLean.IOExample

namespace Verso.Genre.Manual.InlineLean

inductive FileType where
  | stdin | stdout | stderr
  | input (file : System.FilePath)
  | output (file : System.FilePath)
  | other (file : System.FilePath)
deriving ToJson, FromJson, Repr, BEq, DecidableEq, Quote


def Block.exampleFile (type : FileType) : Block where
  data := ToJson.toJson type

structure ExampleFileConfig where
  type : FileType
  «show» : Bool := true

-- TODO: upstream
instance [Functor m] : Functor (ValDesc m) where
  map f d := {
    description := d.description
    get := fun v => f <$> d.get v
  }

def FileType.parse [Monad m] [MonadError m] : ArgParse m FileType :=
    (.positional `type (literally `stdin) *> pure .stdin) <|>
    (.positional `type (literally `stdout) *> pure .stdout) <|>
    (.positional `type (literally `stderr) *> pure .stderr) <|>
    (.positional `type (literally `stderr) *> pure .stderr) <|>
    (FileType.input <$> (.positional `type (literally `input) *> .positional `filename path)) <|>
    (FileType.output <$> (.positional `type (literally `output) *> .positional `filename path)) <|>
    (FileType.other <$> (.positional `type (literally `other) *> .positional `filename path))
where
  path : ValDesc m System.FilePath := Coe.coe <$> ValDesc.string

  literally (n : Name) : ValDesc m Unit := {
    description := n
    get := fun
      | .name x => if x.getId == n then pure () else throwErrorAt x m!"Expected '{toString n}', got '{toString x.getId}'"
      | nonName => throwError m!"Expected '{toString n}', got {repr nonName}"
  }


def ExampleFileConfig.parse [Monad m] [MonadInfoTree m] [MonadLiftT CoreM m] [MonadEnv m] [MonadError m] : ArgParse m ExampleFileConfig :=
  ExampleFileConfig.mk <$> FileType.parse <*> ((·.getD true) <$> .named `show .bool true)


def IOExample.exampleFileSyntax [Monad m] [MonadQuotation m] (type : FileType) (contents : String) : m Term := do
  `(Block.other (Block.exampleFile $(quote type)) #[Block.code $(quote contents)])


@[code_block_expander exampleFile]
def exampleFile : CodeBlockExpander
  | args, str => do
    let config ← ExampleFileConfig.parse.run args
    let s := str.getString

    if config.show then
      return #[← IOExample.exampleFileSyntax config.type s]
    else
      return #[]


@[block_extension Block.exampleFile]
def Block.exampleFile.descr : BlockDescr where
  traverse _ _ _ := pure none
  toTeX := none
  extraCss := [
    r#"
.example-file {
  white-space: normal;
  font-family: var(--verso-structure-font-family);
  margin: 1rem;
  width: fit-content;
  border: 1px solid #ddd;
  padding: 0.5rem;

  /* These are necessary for the container to behave nicely on mobile */
  overflow-x: auto;
  max-width: 100%;
  box-sizing: border-box;
}
.example-file::before {
  counter-reset: linenumber;
}
.example-file > .line {
  display: block;
  white-space: pre;
  counter-increment: linenumber;
  font-family: var(--verso-code-font-family);
}
.example-file > .line::before {
  -webkit-user-select: none;
  display: inline-block;
  content: counter(linenumber);
  border-right: 1px solid #ddd;
  width: 2em;
  padding-right: 0.25em;
  margin-right: 0.25em;
  font-family: var(--verso-code-font-family);
  text-align: right;
}
.example-file > .line::after {
  -webkit-user-select: none;
  display: inline-block;
  content: "⏎";
  opacity: 0;
}
.example-file > .line:hover::after {
  opacity: 1;
}
.example-file > .line:hover, .example-file > .line:hover::before {
  background-color: #eee;
}
.example-file > .empty {
  display: block;
  white-space: pre;
  font-family: var(--verso-code-font-family);
  font-style: italic;
}
.example-file > .empty::before {
  -webkit-user-select: none;
  display: inline-block;
  content: "";
  border-right: 1px solid #ddd;
  width: 2em;
  padding-right: 0.25em;
  margin-right: 0.25em;
  font-family: var(--verso-code-font-family);
  text-align: right;
}
"#
  ]
  extraJs := [
    highlightingJs
  ]
  extraJsFiles := [("popper.js", popper), ("tippy.js", tippy)]
  extraCssFiles := [("tippy-border.css", tippy.border.css)]
  toHtml :=
    open Verso.Output Html in
    some <| fun _ _ _ data blocks => do
      match FromJson.fromJson? (α := FileType) data with
      | .error err =>
        HtmlT.logError <| "Couldn't deserialize file metadata while rendering HTML: " ++ err
        pure .empty
      | .ok type =>
        let str ←
          match blocks with
          | #[.code s] => pure s
          | other =>
            HtmlT.logError <| s!"Expected a single code block in an example file, but got {other.size} blocks"
            return .empty
        let descr : Html :=
          match type with
          | .stdin => {{<code>"stdin"</code>}}
          | .stdout => {{<code>"stdout"</code>}}
          | .stderr => {{<code>"stderr"</code>}}
          | .input f => {{"Input: "<code>{{f.toString}}</code>}}
          | .output f => {{"Output: "<code>{{f.toString}}</code>}}
          | .other f => {{"File: "<code>{{f.toString}}</code>}}


        let lines : Html :=
          if str.isEmpty || str == "\n" then
            {{<code class="empty">"<empty>"</code>}}
          else
            getLines str |>.map ({{<code class="line">{{show String from ·}}</code>}})

        pure {{
          <div class="example-file">
            {{descr}}
            {{lines}}
          </div>}}
where
  getLines (file : String) : Array String :=
    let lines := file.split (· == '\n') |>.toArray
    if lines.back? == some "" then lines.pop else lines

namespace IOExample

open SubVerso in
private def getSubversoDir : IO System.FilePath := do
  let srcSearchPath ← Compat.initSrcSearchPath
  let libSearchPath := (← IO.getEnv "LEAN_PATH")
    |>.map System.SearchPath.parse
    |>.getD []
  let searchPath := srcSearchPath ++ libSearchPath
  let path? := searchPath.find? (·.components.contains "subverso")

  let some path := path?
    | throw <| IO.userError <|
        "Failed to load subverso package path from these candidates:\n" ++
        String.join (searchPath.map (s!" * {·}\n"))
  let p := path.normalize.components.reverse.dropWhile (· != "subverso") |>.reverse |> System.mkFilePath
  if ← p.isDir then
    pure <| (← IO.currentDir) / p
  else
    throw <| IO.userError s!"SubVerso directory {p} not found"


def startExample [Monad m] [MonadEnv m] [MonadError m] [MonadQuotation m] [MonadRef m] : m Unit := do
  match ioExampleCtx.getState (← getEnv) with
  | some _ => throwError "Can't initialize - already in a context"
  | none =>
    let leanCodeName ← mkFreshIdent (← getRef)
    modifyEnv fun env =>
      ioExampleCtx.setState env (some {leanCodeName})

def saveLeanCode (src : StrLit) : DocElabM Ident := do
  match ioExampleCtx.getState (← getEnv) with
  | none => throwError "Can't set Lean code - not in an IO example"
  | some st =>
    if st.code.isNone then
      modifyEnv fun env =>
        ioExampleCtx.setState env (some {st with code := src})
      return st.leanCodeName
    else throwError "Code already specified"


def saveInputFile [Monad m] [MonadEnv m] [MonadError m] (name : System.FilePath) (contents : StrLit) : m Unit := do
  match ioExampleCtx.getState (← getEnv) with
  | none => throwError "Can't save file - not in an IO example"
  | some st =>
    modifyEnv fun env => ioExampleCtx.setState env (some {st with inputFiles := st.inputFiles.push (name, contents)})

def saveOutputFile [Monad m] [MonadEnv m] [MonadError m] (name : System.FilePath) (contents : StrLit) : m Unit := do
  match ioExampleCtx.getState (← getEnv) with
  | none => throwError "Can't save file - not in an IO example"
  | some st =>
    modifyEnv fun env => ioExampleCtx.setState env (some {st with outputFiles := st.outputFiles.push (name, contents)})

def saveStdin [Monad m] [MonadEnv m] [MonadError m] (contents : StrLit) : m Unit := do
  match ioExampleCtx.getState (← getEnv) with
  | none => throwError "Can't save stdin - not in an IO example"
  | some st =>
    match st.stdin with
    | none => modifyEnv fun env => ioExampleCtx.setState env (some {st with stdin := some contents})
    | some _ => throwError "stdin already specified"

def saveStdout [Monad m] [MonadEnv m] [MonadError m] (contents : StrLit) : m Unit := do
  match ioExampleCtx.getState (← getEnv) with
  | none => throwError "Can't save stdout - not in an IO example"
  | some st =>
    match st.stdout with
    | none => modifyEnv fun env => ioExampleCtx.setState env (some {st with stdout := some contents})
    | some _ => throwError "stdout already specified"

def saveStderr [Monad m] [MonadEnv m] [MonadError m] (contents : StrLit) : m Unit := do
  match ioExampleCtx.getState (← getEnv) with
  | none => throwError "Can't save stderr - not in an IO example"
  | some st =>
    match st.stderr with
    | none => modifyEnv fun env => ioExampleCtx.setState env (some {st with stderr := some contents})
    | some _ => throwError "stderr already specified"


def check
    (leanCode : StrLit) (leanCodeName : Name)
    (inputFiles outputFiles : Array (System.FilePath × StrLit))
    (stdin stdout stderr : Option StrLit) : DocElabM Highlighted :=
  IO.FS.withTempDir fun dirname => do
    let toolchain : String ← IO.FS.readFile "lean-toolchain"
    let leanCodeName : String :=
      match leanCodeName with
      -- | .str .anonymous n => n
      | _ => "Main"
    let out ← IO.Process.output {cmd := "lake", args := #["env", "which", "subverso-extract-mod"]}
    if out.exitCode != 0 then
      throwError
        m!"When running 'lake env which subverso-extract-mod', the exit code was {out.exitCode}\n" ++
        m!"Stderr:\n{out.stderr}\n\nStdout:\n{out.stdout}\n\n"
    let some «subverso-extract-mod» := out.stdout.splitOn "\n" |>.head?
      | throwError "No executable path found"
    let «subverso-extract-mod» ← IO.FS.realPath «subverso-extract-mod»

    -- Avoid contention during parallel builds
    let leanFileName : System.FilePath := (leanCodeName : System.FilePath).addExtension "lean"
    IO.FS.writeFile (dirname / "lean-toolchain") toolchain
    IO.FS.writeFile (dirname / leanFileName) leanCode.getString
    IO.FS.writeFile (dirname / "lakefile.toml")
      s!"name = \"example\"
  defaultTargets = [\"{leanCodeName}\"]

  [[lean_exe]]
  name = \"{leanCodeName}\"
  "
    for (f, i) in inputFiles do
      IO.FS.writeFile (dirname / f) i.getString

    let out ← IO.Process.output {cmd := "lake", args := #["clean"], cwd := some dirname}
    if out.exitCode != 0 then
      throwError
        m!"When running 'lake clean' in {dirname}, the exit code was {out.exitCode}\n" ++
        m!"Stderr:\n{out.stderr}\n\nStdout:\n{out.stdout}\n\n"

    let out ← IO.Process.output {cmd := "lake", args := #["build"], cwd := some dirname}
    if out.exitCode != 0 then
      throwError
        m!"When running 'lake build' in {dirname}, the exit code was {out.exitCode}\n" ++
        m!"Stderr:\n{out.stderr}\n\nStdout:\n{out.stdout}\n\n"
    let proc ← IO.Process.spawn {cmd := "lake", args := #["--quiet", "exe", leanCodeName], cwd := some dirname, stdin := .piped, stdout := .piped, stderr := .piped}
    let (stdinH, proc) ← proc.takeStdin
    stdinH.putStr (stdin.map (·.getString) |>.getD "")
    stdinH.flush
    let stdoutTask ← IO.asTask proc.stdout.readToEnd Task.Priority.dedicated
    let stderrOut ← proc.stderr.readToEnd
    let exitCode ← proc.wait

    let ref ← getRef
    let loc {k} (s : Option (TSyntax k)) : Syntax := s.map (·.raw) |>.getD ref

    if exitCode != 0 then
      Lean.logError s!"Running 'lake --quiet exe {leanCodeName}' failed with exit code {exitCode}."

    let stdoutOut ← IO.ofExcept stdoutTask.get
    let expectedStdout := stdout.map (·.getString) |>.getD ""
    if stdoutOut.trim != expectedStdout.trim then
      if let some stdoutLit := stdout then
        Verso.Doc.Suggestion.saveSuggestion stdoutLit (shorten stdoutOut) stdoutOut
      logErrorAt (loc stdout) s!"Mismatched stdout. Expected:\n{expectedStdout}\nGot:\n{stdoutOut}"

    let expectedStderr := stderr.map (·.getString) |>.getD ""
    if stderrOut.trim != expectedStderr.trim then
      if let some stderrLit := stderr then
        Verso.Doc.Suggestion.saveSuggestion stderrLit (shorten stderrOut) stderrOut
      logErrorAt (loc stderr) s!"Mismatched stderr. Expected:\n{stderr.map (·.getString) |>.getD ""}\nGot:{stderrOut}\n"

    for (f, o) in outputFiles do
      let f' := dirname / f
      if ← f'.pathExists then
        let contents ← IO.FS.readFile f'
        if contents.trim != o.getString.trim then
          Verso.Doc.Suggestion.saveSuggestion o (shorten contents) contents
          logErrorAt (loc (some o)) s!"Output file {f} mismatch. Got:\n{contents}"
      else Lean.logError s!"Output file {f} not found"

    let out ← IO.Process.output {cmd := "lake", args := #["update", "subverso"], cwd := some dirname}
    if out.exitCode != 0 then
      throwError
        m!"When running 'lake update subverso' in {dirname}, the exit code was {out.exitCode}\n" ++
        m!"Stderr:\n{out.stderr}\n\nStdout:\n{out.stdout}\n\n"
    let jsonFile := s!"{leanCodeName}.json"
    let out ← IO.Process.output {cmd := toString «subverso-extract-mod» , args := #[leanCodeName, jsonFile], cwd := some dirname}
    if out.exitCode != 0 then
      throwError
        m!"When running '{«subverso-extract-mod»} {leanCodeName} {jsonFile}' in {dirname}, the exit code was {out.exitCode}\n" ++
        m!"Stderr:\n{out.stderr}\n\nStdout:\n{out.stdout}\n\n"
    let json ← IO.FS.readFile (dirname / jsonFile)
    let json ← IO.ofExcept <| Json.parse json
    let Json.arr json := json
      | throwError m!"Expected a JSON aray, got {json}"
    let json ← json.mapM fun v =>
      match v.getObjVal? "code" with
      | .ok v => pure v
      | .error e => throwError e
    json.foldlM (init := .empty) fun hl v =>
      match FromJson.fromJson? v with
      | .ok v => pure <| hl ++ v
      | .error e =>
        throwError m!"Failed to deserialized JSON output as highlighted Lean code. Error: {indentD e}\nJSON: {Json.arr json}"


where
  shorten (str : String) : String :=
    if str.length < 30 then str else str.take 30 ++ "…"

def endExample (body : TSyntax `term) : DocElabM (TSyntax `term) := do
  match ioExampleCtx.getState (← getEnv) with
  | none => throwErrorAt body "Can't end example - never started"
  | some {code, leanCodeName, inputFiles, outputFiles, stdin, stdout, stderr} => do
    modifyEnv fun env =>
      ioExampleCtx.setState env none

    let some leanCode := code
      | throwErrorAt body "No code specified"

    let hlLean ← check leanCode leanCodeName.getId inputFiles outputFiles stdin stdout stderr

    `(let $leanCodeName : Highlighted := $(quote hlLean)
      $body)

structure Config where
  tag : Option String := none
  «show» : Bool := true

def Config.parse [Monad m] [MonadInfoTree m] [MonadLiftT CoreM m] [MonadEnv m] [MonadError m] : ArgParse m Config :=
  Config.mk <$> .named `tag .string true <*> ((·.getD true) <$> .named `show .bool true)

structure FileConfig extends Config where
  name : String

def FileConfig.parse [Monad m] [MonadInfoTree m] [MonadLiftT CoreM m] [MonadEnv m] [MonadError m] : ArgParse m FileConfig :=
  FileConfig.mk <$> Config.parse <*> .positional `name .string

end IOExample

open IOExample in
@[code_block_expander inputFile]
def inputFile : CodeBlockExpander
  | args, str => do
    let opts ← FileConfig.parse.run args
    saveInputFile opts.name str
    -- The quote step here is to prevent the editor from showing document AST internals when the
    -- cursor is on the code block
    if opts.show then
      pure #[← exampleFileSyntax (.input opts.name) str.getString]
    else
      pure #[]

open IOExample in
@[code_block_expander outputFile]
def outputFile : CodeBlockExpander
  | args, str => do
    let opts ← FileConfig.parse.run args
    saveOutputFile opts.name str
    -- The quote step here is to prevent the editor from showing document AST internals when the
    -- cursor is on the code block
    if opts.show then
      pure #[← exampleFileSyntax (.output opts.name) str.getString]
    else
      pure #[]

open IOExample in
@[code_block_expander stdin]
def stdin : CodeBlockExpander
  | args, str => do
    let opts ← Config.parse.run args
    saveStdin str
    -- The quote step here is to prevent the editor from showing document AST internals when the
    -- cursor is on the code block
    if opts.show then
      pure #[← exampleFileSyntax .stdin str.getString]
    else
      pure #[]

open IOExample in
@[code_block_expander stdout]
def stdout : CodeBlockExpander
  | args, str => do
    let opts ← Config.parse.run args
    saveStdout str
    -- The quote step here is to prevent the editor from showing document AST internals when the
    -- cursor is on the code block
    if opts.show then
      pure #[← exampleFileSyntax .stdout str.getString]
    else
      pure #[]

open IOExample in
@[code_block_expander stderr]
def stderr : CodeBlockExpander
  | args, str => do
    let opts ← Config.parse.run args
    saveStderr str
    -- The quote step here is to prevent the editor from showing document AST internals when the
    -- cursor is on the code block
    if opts.show then
      pure #[← exampleFileSyntax .stderr str.getString]
    else
      pure #[]


open IOExample in
@[code_block_expander ioLean]
def ioLean : CodeBlockExpander
  | args, str => do
    let opts ← Config.parse.run args
    let x ← saveLeanCode str
    if opts.show then
      let range := Syntax.getRange? str
      let range := range.map (← getFileMap).utf8RangeToLspRange
      pure #[← ``(Block.other (Block.lean $x (some $(quote (← getFileName))) $(quote range)) #[Block.code $(quote str.getString)])]
    else
      pure #[]


open IOExample in
@[directive_expander ioExample]
def ioExample : DirectiveExpander
 | args, blocks => do
    ArgParse.done.run args
    startExample
    let body ← blocks.mapM elabBlock
    let body' ← `(Verso.Doc.Block.concat #[$body,*]) >>= endExample
    pure #[body']
