/-
Copyright (c) 2023-2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import SubVerso.Helper
import SubVerso.Module
import VersoBlog.Basic
import VersoBlog.LiterateLeanPage.Options
import MD4Lean


open Lean

open SubVerso.Highlighting
open SubVerso.Helper
open SubVerso.Module
open Verso.Doc.Concrete (stringToInlines)

namespace Verso.Genre.Blog.Literate

structure LitPageConfig where
  header : Bool := false

open System in
def loadModuleContent
    (leanProject : FilePath) (mod : String)
    (overrideToolchain : Option String := none) : IO (Array ModuleItem) := do

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


  IO.FS.withTempFile fun h f => do
    let cmd := "elan"

    let args := #["run", "--install", toolchain, "lake", "exe", "subverso-extract-mod", mod, f.toString]
    let res ← IO.Process.output {
      cmd, args, cwd := projectDir
      -- Unset Lake's environment variables
      env := lakeVars.map (·, none)
    }
    if res.exitCode != 0 then reportFail projectDir cmd args res
    h.rewind

    let .ok json := Json.parse (← h.readToEnd)
      | throw <| IO.userError s!"Expected JSON"
    match Module.fromJson? json with
    | .error err =>
      throw <| IO.userError s!"Couldn't parse JSON from output file: {err}\nIn:\n{json}"
    | .ok val => pure val.items

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
      "LEAN_GITHASH",
      "ELAN_TOOLCHAIN", "DYLD_LIBRARY_PATH", "LD_LIBRARY_PATH"]

  let cmd := "elan"


  let args := #["run", "--install", toolchain, "lake", "env", "which", "subverso-helper"]

    let res ← IO.Process.output {
      cmd, args, cwd := projectDir
      -- Unset Lake's environment variables
      env := lakeVars.map (·, none)
    }
    if res.exitCode != 0 then
      let args := #["run", "--install", toolchain, "lake", "build", "subverso-helper"]

      let res ← IO.Process.output {
        cmd, args, cwd := projectDir
        -- Unset Lake's environment variables
        env := lakeVars.map (·, none)
      }
      if res.exitCode != 0 then reportFail projectDir cmd args res

  let args := #["run", "--install", toolchain, "lake", "env", "subverso-helper", mod]
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


def loadLiteratePage (root : System.FilePath) (module : String) : IO (Array ModuleItem) := do
  loadModuleContent root module


inductive Pat where
  | char : Char → Pat
  | str : String → Pat
  | var : Name → Pat
  | any : Pat
deriving BEq, Hashable, Repr, Inhabited

-- TODO rewrite with dynamic programming
partial def Pat.match (p : List Pat) (str : String) : Option (NameMap String) :=
  go str.iter p
where
  go iter
    | [] => if iter.atEnd then pure {} else failure
    | .char c :: p' =>
      if h : iter.hasNext then
        if iter.curr' h == c then
          go (iter.next' h) p'
        else failure
      else failure
    | .str s :: p' =>
      go iter (s.data.map .char ++ p')
    | .var x :: p' => do
      let mut iter' := iter.toEnd
      while iter'.pos ≥ iter.pos do
        try
          let rest ← go iter' p'
          return rest.insert x (iter.extract iter')
        catch
          | () =>
            iter' := iter'.prev
            continue
      failure
    | .any :: p' => do
      let mut iter' := iter.toEnd
      while iter'.pos ≥ iter.pos do
        try
          return (← go iter' p')
        catch
          | () =>
            iter' := iter'.prev
            continue
      failure

inductive Template where
  | str : String → Template
  | var : Name → Template
deriving BEq, Hashable, Repr, Inhabited

def Template.subst (vars : NameMap String) : Template → Except String String
  | .str s => pure s
  | .var x => if let some s := vars.find? x then pure s else throw s!"Not found: '{x}'"

syntax url_pattern := "*" <|> str <|> char <|> ident
syntax url_template := str <|> ident

syntax url_case := url_pattern* " => " url_template*

namespace Internal
scoped syntax "url_pat " url_pattern* : term
scoped syntax "url_tpl " url_template* : term
scoped syntax "url_subst " url_case : term
scoped syntax "url_subst" "(" term ")" url_case : term

macro_rules
  | `(term|url_pat) => `([])
  | `(term|url_pat * $p*) => `([.any] ++ url_pat $p*)
  | `(term|url_pat $s:str $p*) => `([.str $s] ++ url_pat $p*)
  | `(term|url_pat $c:char $p*) => `([.char $c] ++ url_pat $p*)
  | `(term|url_pat $x:ident $p*) => `([.var $(quote x.getId)] ++ url_pat $p*)
  | `(term|url_tpl) => `([])
  | `(term|url_tpl $x:ident $t*) => ``([Template.var $(quote x.getId)] ++ url_tpl $t*)
  | `(term|url_tpl $s:str $t*) => ``([Template.str $s] ++ url_tpl $t*)
  | `(term|url_subst($s) $pat* => $template*) =>
    `(let s := $s; Pat.match (url_pat $pat*) s |>.map fun ρ => String.join <$> (url_tpl $template*.mapM (Template.subst ρ)))
  | `(term|url_subst $pat* => $template*) =>
    `(fun s => url_subst(s) $pat* => $template*)


def getSubst [Monad m] : TSyntax ``url_case → m (List Pat × List Template)
  | `(url_case|$pat* => $template*) => do
    let pat := pat.map fun
      | `(url_pattern| *) => Pat.any
      | `(url_pattern| $s:str) => .str s.getString
      | `(url_pattern| $c:char) => .char c.getChar
      | `(url_pattern| $x:ident) => .var x.getId
      | p => panic! s!"Didn't understand pattern {p}"
    let template := template.map fun
      | `(url_template| $s:str) => Template.str s.getString
      | `(url_template| $x:ident) => Template.var x.getId
      | t => panic! s!"Didn't understand template {t}"
    pure (pat.toList, template.toList)
  | c => panic! s!"Didn't understand case {c}"


/-- info: some (Except.ok "foo/foo/bar/baz/f.png") -/
#guard_msgs in
#eval (url_subst "xy/" z "/static/" pic ".jpg" => "foo/" z "/" pic ".png") "xy/foo/static/bar/baz/f.jpg"

end Internal

section
variable [Monad m] [MonadError m] [MonadQuotation m]


partial def getModuleDocString (hl : Highlighted) : m String := do
  let str := (← getString hl).trim
  let str := str.stripPrefix "/-!" |>.stripSuffix "-/" |>.trim
  pure str
where getString : Highlighted → m String
  | .text txt | .unparsed txt => pure txt
  | .tactics .. => throwError "Tactics found in module docstring!"
  | .point .. => pure ""
  | .span _ hl => getModuleDocString hl
  | .seq hls => do return (← hls.mapM getString).foldl (init := "") (· ++ ·)
  | .token ⟨_, txt⟩ => pure txt
end

def getFirstMessage : Highlighted → Option (Highlighted.Span.Kind × Highlighted.MessageContents Highlighted)
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
  | .unparsed ..
  | .token .. => failure

partial def examplesFromMod [Monad m] [MonadError m]
    (mod : String) (content : Array ModuleItem) : m (Array (Name × Option (Position × Position) × Highlighted)) := do
  let modname := mod.toName
  let mut examples : Array (Name × Option (Position × Position) × Highlighted) := #[]
  let mut complete : Highlighted := .empty
  for item in content do
    let {defines, code, range, ..} := item
    complete := complete ++ code
    for x in defines do
      examples := examples.push (modname ++ x, range, code)
  return examples

open Verso Doc Elab PartElabM in
open Lean.Parser.Command in
partial def docFromMod (project : System.FilePath) (mod : String)
    (config : LitPageConfig) (content : Array ModuleItem)
    (rewriter : Array (List Pat × List Template)) : PartElabM Unit := do
  let mut mdHeaders : Array Nat := #[]
  let helper ← Helper.fromModule project mod
  for cmd in content do
    let {kind, code, ..} := cmd
    match kind with
    | ``Lean.Parser.Module.header =>
      if config.header then
        addBlock (← `(Block.other (BlockExt.highlightedCode { contextName := `name } $(quote code)) Array.mkArray0))
      else pure ()
    | ``moduleDoc =>
      let str ← getModuleDocString code
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
            titleSyntax := (← arr inlines),
            expandedTitle := some (txt.map inlineText |>.toList |> String.join, inlines),
            metadata := none,
            blocks := #[],
            priorParts := #[]
          }
        | other =>
          addBlock (← ofBlock helper other)
    | ``eval | ``evalBang | ``reduceCmd | ``print | ``printAxioms | ``printEqns | ``«where» | ``version | ``synth | ``check =>
      addBlock (← `(Block.other (BlockExt.highlightedCode { contextName := `name } $(quote code)) Array.mkArray0))
      if let some (k, msg) := getFirstMessage code then
        let sev := match k with
          | .error => "error"
          | .info => "information"
          | .warning => "warning"
        addBlock (← ``(Block.other (Blog.BlockExt.htmlDiv $(quote sev)) (Array.mkArray1 (Block.code $(quote msg)))))
    | _ =>
      addBlock (← `(Block.other (BlockExt.highlightedCode { contextName := `name } $(quote code)) Array.mkArray0))
  closePartsUntil 0 ⟨0⟩ -- TODO endPos?
where
  arr (xs : Array Term) : PartElabM Term := do
    if xs.size ≤ 8 then
      pure <| Syntax.mkCApp (`Array ++ s!"mkArray{xs.size}".toName) xs
    else
      `(#[$xs,*])

  ofBlock (helper : Helper) : MD4Lean.Block → PartElabM Term
  | .header .. => throwError "Headers should be processed at the part level"
  | .p txt => do
    let inlines ← txt.mapM (ofInline helper)
    ``(Block.para $(← arr inlines))
  | .ul _ _ lis => do
    ``(Doc.Block.ul $(← arr (← lis.mapM (ofLi helper))))
  | .ol _ start _ lis => do
    ``(Doc.Block.ol $(quote (start : Int)) $(← arr (← lis.mapM (ofLi helper))))
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
    ``(Doc.Block.blockquote $(← arr (← bs.mapM (ofBlock helper))))
  | b => throwError "Unsupported block {repr b}"

  ofLi (helper : Helper) : MD4Lean.Li MD4Lean.Block → PartElabM Term
  | {isTask, taskChar:=_, taskMarkOffset:=_, contents} => do
    if isTask then throwError "Tasks not supported"
    ``(Doc.ListItem.mk $(← arr (← contents.mapM (ofBlock helper))))

  ofInline (helper : Helper) : MD4Lean.Text → PartElabM Term
  | .normal str => ``(Inline.text $(quote str))
  | .nullchar => throwError "Unsupported null character in Markdown"
  | .softbr txt => ``(Inline.linebreak $(quote txt))
  | .a href _title _isAuto contents => do
    let href := (← href.mapM ofAttrText).toList |> String.join
    let contents ← contents.mapM (ofInline helper)
    ``(Inline.link $(← arr contents) $(quote href))
  | .code str => do
    let codeStr := String.join str.toList
    try
      let hl ← helper.highlight codeStr none
      `(Inline.other (InlineExt.highlightedCode { contextName := `name } $(quote hl)) #[])
    catch
      | e =>
        if (← getLogInlines) then
          logInfo m!"Couldn't highlight '{codeStr}': {indentD e.toMessageData}"
        ``(Inline.code $(quote <| String.join str.toList))
  | .em txt => do ``(Inline.emph $(← arr (← txt.mapM (ofInline helper))))
  | .strong txt => do ``(Inline.bold $(← arr (← txt.mapM (ofInline helper))))
  | .img src _title alt => do
    let mut src := (← src.mapM ofAttrText).toList |> String.join
    for (pat, template) in rewriter do
      if let some ρ := Pat.match pat src then
        src := ""
        for t in template do
          match t.subst ρ with
          | .error e => throwError e
          | .ok v => src := src ++ v
        break
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


syntax rewrites := "rewriting " ("| " url_case)+

open Verso Doc in
open Lean Elab Command in
open PartElabM in
def elabLiteratePage (x : Ident) (path : StrLit) (mod : Ident) (config : LitPageConfig) (title : StrLit) (genre : Term) (metadata? : Option Term) (rw : Option (TSyntax ``rewrites)) : CommandElabM Unit :=
  withTraceNode `verso.blog.literate (fun _ => pure m!"Literate '{title.getString}'") do

  let rewriter ← rw.mapM fun
    | `(rewrites|rewriting $[| $cases]*) => cases.mapM Internal.getSubst
    | rw => panic! s!"Unknown rewriter {rw}"
  let rewriter := rewriter.getD #[]

  let titleParts ← stringToInlines title
  let titleString := inlinesToString (← getEnv) titleParts
  let initState : PartElabM.State := .init (.node .none nullKind titleParts)

  let items ← withTraceNode `verso.blog.literate.loadMod (fun _ => pure m!"Loading '{mod}' in '{path}'") <|
    loadLiteratePage path.getString mod.getId.toString

  let g ← runTermElabM fun _ => Term.elabTerm genre (some (.const ``Doc.Genre []))

  let ((), _st, st') ← liftTermElabM <| PartElabM.run genre g {} initState <| do
    setTitle titleString (← liftDocElabM <| titleParts.mapM (elabInline ⟨·⟩))
    if let some metadata := metadata? then
      modifyThe PartElabM.State fun st => {st with partContext.metadata := some metadata}

    withTraceNode `verso.blog.literate.renderMod (fun _ => pure m!"Rendering '{mod}'") <|
      docFromMod path.getString mod.getId.toString config items rewriter


  let finished := st'.partContext.toPartFrame.close 0
  let finished :=
    -- Obey the Markdown convention of a single top-level header being the title of the document, if it's been followed
    if let .mk _ _ _ «meta» #[] #[p] _ := finished then
      match p with
      | .mk t1 t2 t3 _ bs ps pos =>
        -- Propagate metadata fields
        FinishedPart.mk t1 t2 t3 «meta» bs ps pos
      | _ => p
    else finished

  elabCommand <| ← `(def $x : Part $genre := $(← finished.toSyntax' genre))

end Literate
open Literate

open Lean.Parser (sepByIndent)
open Lean.Parser.Term
open Verso.Doc.Concrete



open Internal
def ofRewrites [Monad m] [MonadQuotation m] : TSyntax ``rewrites → m Term
  | `(rewrites| rewriting $[| $cases:url_case]*) => do
    let f ← `(fun _ => failure)
    cases.foldrM (init := f) fun case next =>
      `(fun s => (url_subst(s) $case) <|> $next s)
  | _ => pure ⟨.missing⟩

open Lean.Parser.Tactic

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
syntax "def_literate_page " ident optConfig " from " ident " in " str " as " str (" with " term)? (rewrites)? : command
/--
Creates a post from a literate Lean module with Markdown module docstrings in it, performing a
best-effort conversion from a large subset of Markdown to Verso documents. Inline code elements are
elaborated as terms after the module itself; if they succeed, then they are highlighted as well. If
not, they become ordinary Markdown code.

Specifically, `def_literate_post POST from MOD in DIR as TITLE` defines a post `POST` by elaborating
the module `MOD` in the project directory `DIR` with title `TITLE`.

The literate Lean module does not need to use the same toolchain as Verso. `DIR` should be a project
directory that contains a toolchain file and a Lake configuration (`lakefile.toml` or
`lakefile.lean`), which should depend on the same version of SubVerso that Verso is using.

Set the option `verso.literateMarkdown.logInlines` to `true` to see the error messages that
prevented elaboration of inline elements.
-/
syntax "def_literate_post " ident optConfig " from " ident " in " str " as " str (" with " term)? (rewrites)? : command



declare_config_elab litPageConfig LitPageConfig

open Verso Doc in
open Lean Elab Command in
elab_rules : command
  | `(def_literate_page $x $cfg:optConfig from $mod in $path as $title $[with $metadata]? $[$rw:rewrites]?) => do
    let (config, _) ← liftTermElabM <| do
      litPageConfig cfg |>.run {elaborator := `x} |>.run {goals := []}
    withScope (fun sc => {sc with opts := Elab.async.set sc.opts false}) do
      let genre ← `(Page)
      elabLiteratePage x path mod config title genre metadata rw


open Verso Doc in
open Lean Elab Command in
elab_rules : command
  | `(def_literate_post $x $cfg:optConfig from $mod in $path as $title $[with $metadata]? $[$rw:rewrites]?) => do
    let (config, _) ← liftTermElabM <| do
      litPageConfig cfg |>.run {elaborator := `x} |>.run {goals := []}
    withScope (fun sc => {sc with opts := Elab.async.set sc.opts false}) do
      let genre ← `(Post)
      elabLiteratePage x path mod config title genre metadata rw
