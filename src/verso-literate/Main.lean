/-
Copyright (c) 2023-2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import SubVerso.Compat
import SubVerso.Examples.Env
import SubVerso.Module
import SubVerso.Highlighting.Export
import MD4Lean
import Lean.DocString.Syntax
import Lean.DocString.Extension

import VersoLiterate

open Lean Elab Frontend
open Lean.Elab.Command hiding Context
open SubVerso Examples Module
open SubVerso.Highlighting (Highlighted highlight highlightMany)
open VersoLiterate
open Verso.Doc


def helpText : String :=
"Extract a module's highlighted representation as JSON

Usage: verso-literate [OPTS] MOD [OUT]

MOD is the name of a Lean module, and OUT is the destination of the JSON.
If OUT is not specified, the JSON is emitted to standard output.

OPTS may be:
  --suppress-namespace NS
    Suppress the showing of namespace NS in metadata

  --suppress-namespaces FILE
    Suppress the showing of the whitespace-delimited list of namespaces in FILE
"

/--
Extends the last token's trailing whitespace to include the rest of the file.
-/
partial def wholeFile (contents : String) (stx : Syntax) : Syntax :=
  wholeFile' stx |>.getD stx
where
  wholeFile' : Syntax → Option Syntax
  | Syntax.atom info val => pure <| Syntax.atom (wholeFileInfo info) val
  | Syntax.ident info rawVal val pre => pure <| Syntax.ident (wholeFileInfo info) rawVal val pre
  | Syntax.node info k args => do
    for i in [0:args.size - 1] do
      let j := args.size - (i + 1)
      if let some s := wholeFile' args[j]! then
        let args := args.set! j s
        return Syntax.node info k args
    none
  | .missing => none

  wholeFileInfo : SourceInfo → SourceInfo
    | .original l l' t _ => .original l l' t contents.endPos
    | i => i

instance : ToJson ElabInline where
  toJson v := s!"{v.name}"
instance : ToJson ElabBlock where
  toJson v := s!"{v.name}"
instance : ToJson Empty where
  toJson := nofun


section
open SubVerso.Highlighting
open Lean.Parser.Command


structure ExtractState where
  nextId : Nat := 0
  versoComments : Std.HashMap Nat Syntax := {}

def spanInfo (stx1 stx2 : Syntax) : SourceInfo :=
  match stx1.getHeadInfo, stx2.getTailInfo with
  | .original leading start _ _, .original _ _ trailing endPos =>
    .original leading start trailing endPos
  | .synthetic start _ _, .original _ _ _ endPos
  | .synthetic start _ _, .synthetic _ endPos _
  | .original _ start _ _, .synthetic _ endPos _ =>
    .synthetic start endPos
  | .none, _ | _, .none =>
    .none

def commentEndToken (commentInfo : SourceInfo) : Syntax :=
  let info :=
    match commentInfo with
    | .original leading _ trailing endPos =>
      let startPos := ⟨endPos.byteIdx - 2⟩
      .original { leading with startPos := startPos, stopPos := startPos } startPos trailing endPos
    | .synthetic _ endPos canonical =>
      let startPos := ⟨endPos.byteIdx - 2⟩
      .synthetic startPos endPos canonical
    | .none => .none
  .atom info "-/"


/--
Return all stacks of syntax nodes satisfying `visit`, starting with such a node that also fulfills
`accept` (default "is leaf"), and ending with the root.
-/
partial def findStacks (root : Syntax) (visit : Syntax → Bool) (accept : Syntax → Bool := fun stx => !stx.hasArgs) : Array Syntax.Stack :=
  if visit root then (go [] root).run #[] |>.2 else #[]
where
  go (stack : Syntax.Stack) (stx : Syntax) : StateM (Array Syntax.Stack) Unit := do
    if accept stx then
      modify (·.push <| (stx, 0) :: stack)  -- the first index is arbitrary as there is no preceding element
    for i in *...stx.getNumArgs do
      if visit stx[i] then go ((stx, i) :: stack) stx[i]

@[specialize] partial def replaceStackM [Monad m] (stx : Syntax) (fn : Syntax.Stack → Syntax → m (Option Syntax)) : m Syntax :=
  go stx []
where
  go : Syntax → Syntax.Stack → m Syntax
  | stx@(.node info kind args), stk => do
    match (← fn stk stx) with
    | some stx =>
      return stx
    | none =>
      return .node info kind (← args.mapIdxM (fun i s => go s ((stx, i) :: stk)))
  | stx, stk => do
    let o ← fn stk stx
    return o.getD stx

def findHighestM [Monad m] (stx : Syntax) (fn : Syntax → Option α) : m (Array α) := do
  let mut next : Array Syntax := #[stx] -- Syntax to check at the next depth
  while !next.isEmpty do
    let here := next
    next := #[]

    let ok := here.filterMap fn
    if !ok.isEmpty then return ok

    for s in here do
      if let .node _ _ args := s then next := next ++ args

  return #[]

/--
Finds the definition sites of each constant in an info tree, and replaces each docstring with a
reference to the definition for later substitution.
-/
def findDocstringDefs (stx : Syntax) (t : InfoTree) : TermElabM Syntax := do
  -- Find the definition sites of all constants in this info tree
  let defSites := t.deepestNodes fun _ i _ =>
    match i with
    | .ofTermInfo ti =>
      if ti.isBinder then
        match ti.expr with
        | .const x _ => some (x, ti.stx)
        | _ => none
      else none
    | _ => none
  let defSites ← defSites.filterM fun x => do
    return (← findInternalDocString? (← getEnv) x.1) |>.isSome
  -- Now find the largest syntax object that contains just one of these definition sites and replace
  -- all doc comments with a placeholder token
  let stx ← stx.replaceM fun s => do
    if let some range := s.getRange? then
      let includes := defSites.filter (·.2.getRange?.map (range.includes · true true) |>.getD false)
      if let [(x, _)] := includes then
        some <$> s.replaceM fun s' => do
          if s'.isOfKind ``docComment then
            rewriteComment x s'
          else pure none
      else pure none
    else pure none
  -- That worked for most cases, but not for inductive datatypes or structures, which have further
  -- nested declarations with docstrings. These, and things like them, will be caught by the
  -- following heuristic: any remaining unprocessed doc comments are associated with the unique
  -- highest definition site that they share a closest ancestor with.
  let stx ← replaceStackM stx fun stk stx => do
    if stx.isOfKind ``docComment && stx[1].isAtom || stx[1].isOfKind ``versoCommentBody then
      for (parent, i) in stk do
        let defs ← findHighestM parent fun x =>
          if x.isIdent then defSites.find? (fun y => identMatch y.2 x) |>.map (·.1) else none
        if defs.size = 0 then continue
        else if h : defs.size = 1 then
          let x := defs[0]
          let indentColumn := (← getFileMap).utf8PosToLspPos stx.getHeadInfo.getPos! |>.character
          return ← rewriteComment x stx
        else -- abort
          return none
      return none
    else pure none
  return stx
where
  identMatch (stx1 stx2 : Syntax) : Bool :=
    normIdent stx1 == normIdent stx2

  normIdent (stx : Syntax) : Syntax :=
    if stx.getKind == ``declId then stx[0] else stx

  rewriteComment (x : Name) (stx : Syntax) : TermElabM Syntax := do
    let indentColumn := (← getFileMap).utf8PosToLspPos stx.getHeadInfo.getPos! |>.character
    let info := if let .atom info _ := stx[1] then info else spanInfo stx stx
    return .node .none `replacedDoc #[.atom info s!"▼{indentColumn}◄{x}▲"]


/--
Highlights a sequence of syntaxes, each with its own info tree. Typically used for highlighting a
module, where each command has its own corresponding tree.

The work of constructing the alias table is performed once, with all the trees together.
-/
partial def highlightFrontendResult' (result : Compat.Frontend.FrontendResult)
    (suppressNamespaces : List Name := []) :
    TermElabM (Array (Array Code)) := do
  let trees' := result.items.flatMap (·.info |>.toArray)
  let infoTable : InfoTable := .ofInfoTrees trees'
  let modrefs := Lean.Server.findModuleRefs (← getFileMap) trees'
  let ids := build modrefs

  let ctx := ⟨ids, true, false, sortSuppress suppressNamespaces⟩

  let mut code : Array (Array Code) := #[]

  let ((), headerSt) ← highlight' #[] result.headerSyntax true |>.run ctx |>.run infoTable |>.run (← HighlightState.ofMessages result.headerSyntax #[])
  code := code.push #[.highlighted <| Highlighted.fromOutput headerSt.output]

  for cmd in result.items do
    let st ← HighlightState.ofMessages cmd.commandSyntax (Compat.messageLogArray cmd.messages)
    let (hl, _) ← go cmd |>.run ctx |>.run infoTable |>.run st
    code := code.push hl

  return code
where

  go (res : Compat.Frontend.FrontendItem) : HighlightM (Array Code) := do
    if res.info.size > 1 then panic! s!"Command {res.commandSyntax.getKind} has {res.info.size} info trees, expected at most 1"
    let stx ←
      if let some t := res.info[0]? then
        findDocstringDefs res.commandSyntax t
      else pure res.commandSyntax

    if stx.isOfKind ``moduleDoc then
      if let some declRange ← getDeclarationRange? stx then
        if stx[1].getKind == ``versoCommentBody then
          let doc? := getVersoModuleDocs (← getEnv) |>.snippets |>.findSome? fun s =>
             guard (s.declarationRange == declRange) *> some s
          if let some doc := doc? then
            return #[.modDoc (← toModLit doc)]
        else if stx[1].isAtom then
          if let some doc := MD4Lean.parse (stx[1].getAtomVal.stripSuffix "-/") then
            return #[.markdownModDoc doc]

    highlight' (Option.map (#[·]) res.info[0]? |>.getD #[]) stx true
    let hl ← modifyGet fun (st : HighlightState) => (Highlighted.fromOutput st.output, {st with output := []})
    let hl ← hl.substM (m := HighlightM) fun str => do
      if str.endsWith "▲" then
        let str := str.dropWhile (· ≠ '▼') |>.drop 1 |>.dropRight 1
        let indentStr := str.takeWhile (· ≠ '◄')
        let str := str.drop (indentStr.length + 1)
        let declName := str.toName
        let i := indentStr.toNat!
        if let some v ← findInternalDocString? (← getEnv) declName then
          some <$> do match v with
          | .inl x =>
            let some md := MD4Lean.parse x
              | pure (Code.markdown i (some declName) ⟨#[.code #[] #[] none #["Failed to parse Markdown:\n", x]]⟩)
            pure (Code.markdown i (some declName) md)
          | .inr x =>
            let x ← toLit x
            pure <| Code.verso i (some declName) x
        else pure none
      else pure none
    pure <| hl.map fun
      | .inl hl => .highlighted hl
      | .inr c => c

  toLit (doc : VersoDocString) : HighlightM (LitVersoDocString) := do
    pure { text := ← doc.text.mapM blockToLit, subsections := ← doc.subsections.mapM partToLit }

  toModLit (doc : VersoModuleDocs.Snippet) : HighlightM (LitVersoModuleDocs.Snippet) := do
    pure { text := ← doc.text.mapM blockToLit, sections := ← doc.sections.mapM fun (l, _, p) => (l, ·) <$> partToLit p }

  inlineToLit : Lean.Doc.Inline ElabInline → HighlightM (Lean.Doc.Inline Ext)
    | .text s => pure <| .text s
    | .linebreak s => pure <| .linebreak s
    | .concat xs => .concat <$> xs.mapM inlineToLit
    | .emph xs => .emph <$> xs.mapM inlineToLit
    | .bold xs => .bold <$> xs.mapM inlineToLit
    | .code s => pure <| .code s
    | .math m s => pure <| .math m s
    | .link txt url => (.link · url) <$> txt.mapM inlineToLit
    | .image alt url => pure <| .image alt url
    | .footnote name xs => .footnote name <$> xs.mapM inlineToLit
    | .other x xs => do
      let xs ← xs.mapM inlineToLit
      let handlers ← getInlineToLiterate
      for h in handlers do
        if let some v ← h x.name x.val xs then
          return v
      throwError "No inline handler for {x.name} with type {x.val.typeName}"


  blockToLit : Lean.Doc.Block ElabInline ElabBlock → HighlightM (Lean.Doc.Block Ext Ext)
    | .para xs => .para <$> xs.mapM inlineToLit
    | .concat xs => .concat <$> xs.mapM blockToLit
    | .ul items => .ul <$> items.mapM fun x => ListItem.mk <$> x.contents.mapM blockToLit
    | .ol n items => .ol n <$> items.mapM fun x => ListItem.mk <$> x.contents.mapM blockToLit
    | .dl items => .dl <$> items.mapM fun x => DescItem.mk <$> x.term.mapM inlineToLit <*> x.desc.mapM blockToLit
    | .blockquote xs => .blockquote <$> xs.mapM blockToLit
    | .code s => pure <| .code s
    | .other x xs => do
      let xs ← xs.mapM blockToLit
      let handlers ← getBlockToLiterate
      for h in handlers do
        if let some v ← h x.name x.val xs then
          return v
      throwError "No block handler for {x.name} with type {x.val.typeName}"

  partToLit (p : Lean.Doc.Part ElabInline ElabBlock Empty) : HighlightM (Lean.Doc.Part Ext Ext Empty) :=
    return { p with
      title := ← p.title.mapM inlineToLit
      content := ← p.content.mapM blockToLit
      subParts := ← p.subParts.mapM partToLit
    }

end


unsafe def go (suppressedNamespaces : Array Name) (extraImports : Array Name) (mod : String) (out : IO.FS.Stream) : IO UInt32 := do
  try
    initSearchPath (← findSysroot)
    let modName := mod.toName

    let sp ← Compat.initSrcSearchPath
    let sp : SearchPath := (sp : List System.FilePath) ++ [("." : System.FilePath)]
    let fname ← do
      if let some fname ← sp.findModuleWithExt "lean" modName then
        pure fname
      else
        throw <| IO.userError s!"Failed to load {modName} from {sp}"
    let contents ← IO.FS.readFile fname
    let fm := FileMap.ofString contents
    let ictx := Parser.mkInputContext contents fname.toString
    let (headerStx, parserState, msgs) ← Parser.parseHeader ictx
    let imports := headerToImports headerStx
    enableInitializersExecution
    let env ← Compat.importModules (extraImports.map ({module := ·}) ++ imports) {}
    let pctx : Frontend.Context := {inputCtx := ictx}

    let scopes := [{header := "", opts := maxHeartbeats.set {} 10000000 }]
    let commandState := { env, maxRecDepth := defaultMaxRecDepth, messages := msgs, scopes }
    let cmdPos := parserState.pos
    let cmdSt ← IO.mkRef {commandState, parserState, cmdPos}

    let res ← Compat.Frontend.processCommands headerStx pctx cmdSt
    let res := res.updateLeading contents

    let hls ← (Frontend.runCommandElabM <| liftTermElabM <| highlightFrontendResult' res (suppressNamespaces := suppressedNamespaces.toList)) pctx cmdSt

    let env := (← cmdSt.get).commandState.env

    let items : Array ModuleItem' := hls.zip (res.syntax) |>.map fun (hl, stx) => {
      defines := hl.foldl (init := #[]) fun
        | out, .highlighted h => out ++ h.definedNames.toArray
        | out, _ => out,
      kind := stx.getKind,
      range := stx.getRange?.map fun ⟨s, e⟩ => (fm.toPosition s, fm.toPosition e),
      code := hl,
    }

    let items := exportItems items

    out.putStrLn (json%{"module": $mod, "items": $(toJson items)}).compress

    return (0 : UInt32)

  catch e =>
    IO.eprintln s!"error finding highlighted code: {toString e}"
    return 2

structure LiterateConfig where
  handleInline : ElabInline → Array (Lean.Doc.Inline ElabInline) → MetaM (Inline Literate)
  handleBlock : ElabBlock → Array (Lean.Doc.Block ElabInline ElabBlock) → MetaM (Block Literate)

structure Config where
  suppressedNamespaces : Array Name := #[]
  mod : String
  outFile : Option String := none
  extraImports : Array Name := #[]

def Config.fromArgs (args : List String) : IO Config := go {mod := ""} args
where
  go (cfg : Config) : List String → IO Config
    | "--suppress-namespace" :: more =>
      if let ns :: more := more then
        go { cfg with suppressedNamespaces := cfg.suppressedNamespaces.push ns.toName } more
      else
        throw <| .userError "No namespace given after --suppress-namespace"
    | "--suppress-namespaces" :: more => do
      if let file :: more := more then
        let contents ← IO.FS.readFile file
        let nss' := contents.splitToList (·.isWhitespace) |>.filter (!·.isEmpty) |>.map (·.toName)
        go { cfg with suppressedNamespaces := cfg.suppressedNamespaces ++ nss' } more
      else
        throw <| .userError "No namespace file given after --suppress-namespaces"
    | "--import" :: more => do
      if let mod :: more := more then
        go { cfg with extraImports := cfg.extraImports.push mod.toName } more
      else
        throw <| .userError "No import given after --import"
    | [mod] => pure { cfg with mod }
    | [mod, outFile] => pure { cfg with mod, outFile := some outFile }
    | other => throw <| .userError s!"Didn't understand remaining arguments: {other}"

unsafe def main (args : List String) : IO UInt32 := do
  try
    let {suppressedNamespaces, mod, outFile, extraImports} ← Config.fromArgs args
    if mod.isEmpty then throw <| .userError s!"No import module provided"
    match outFile with
    | none =>
      go suppressedNamespaces extraImports mod (← IO.getStdout)
    | some outFile =>
      if let some p := (outFile : System.FilePath).parent then
        IO.FS.createDirAll p
      IO.FS.withFile outFile .write fun h =>
        go suppressedNamespaces extraImports mod (.ofHandle h)
  catch e =>
    IO.eprintln e
    IO.println helpText
    pure 1
